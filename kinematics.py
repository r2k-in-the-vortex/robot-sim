"""Forward kinematics for a six-axis robot using standard DH parameters."""

from __future__ import annotations

import math
from dataclasses import dataclass, replace
from typing import Sequence

Matrix4 = tuple[tuple[float, float, float, float], ...]
Vector3 = tuple[float, float, float]


@dataclass(frozen=True)
class InverseKinematicsSolution:
	"""One inverse-kinematics branch for the supported six-axis geometry."""

	angles: tuple[float, float, float, float, float, float]
	shoulder_branch: int
	elbow_branch: int
	position_error: float
	orientation_error: float


@dataclass(frozen=True)
class PositionIKSolution:
	"""A joint solution matching a Cartesian position, with orientation free."""

	angles: tuple[float, float, float, float, float, float]
	position_error: float
	iterations: int


@dataclass(frozen=True)
class DHParameters:
	"""Standard DH values for one revolute joint; angles are in radians."""

	theta: float
	d: float
	a: float
	alpha: float


def dh_transform(parameters: DHParameters) -> Matrix4:
	"""Return the standard-DH transform from frame i to frame i - 1."""
	theta = parameters.theta
	alpha = parameters.alpha
	cos_theta = math.cos(theta)
	sin_theta = math.sin(theta)
	cos_alpha = math.cos(alpha)
	sin_alpha = math.sin(alpha)

	return (
		(cos_theta, -sin_theta * cos_alpha, sin_theta * sin_alpha, parameters.a * cos_theta),
		(sin_theta, cos_theta * cos_alpha, -cos_theta * sin_alpha, parameters.a * sin_theta),
		(0.0, sin_alpha, cos_alpha, parameters.d),
		(0.0, 0.0, 0.0, 1.0),
	)


def multiply_transforms(left: Matrix4, right: Matrix4) -> Matrix4:
	"""Multiply two 4x4 homogeneous transforms."""
	return tuple(
		tuple(sum(left[row][index] * right[index][column] for index in range(4)) for column in range(4))
		for row in range(4)
	)


def forward_kinematics(parameters: Sequence[DHParameters]) -> tuple[Matrix4, ...]:
	"""Return base-relative transforms for all six consecutive joint frames."""
	if len(parameters) != 6:
		raise ValueError(f"Expected DH parameters for 6 joints, got {len(parameters)}")

	transforms: list[Matrix4] = []
	current_transform: Matrix4 = (
		(1.0, 0.0, 0.0, 0.0),
		(0.0, 1.0, 0.0, 0.0),
		(0.0, 0.0, 1.0, 0.0),
		(0.0, 0.0, 0.0, 1.0),
	)
	for joint_parameters in parameters:
		current_transform = multiply_transforms(current_transform, dh_transform(joint_parameters))
		transforms.append(current_transform)
	return tuple(transforms)


def frame_origin(transform: Matrix4) -> tuple[float, float, float]:
	"""Return a transform's origin expressed in the base frame."""
	return (transform[0][3], transform[1][3], transform[2][3])


def compose_dh_parameters(
	static_values: Sequence[tuple[float, float, float, float]],
	joint_angles_degrees: Sequence[float] | None = None,
) -> tuple[DHParameters, ...]:
	"""Build DH rows from degree offsets and live joint angles.

	Each static row is ``(theta_offset_deg, d, a, alpha_deg)``. Runtime joint
	angles are in degrees and default to zero; they are added to the stored theta
	offset and are not part of the static rows.
	"""
	if len(static_values) != 6:
		raise ValueError(f"Expected static DH values for 6 joints, got {len(static_values)}")
	if joint_angles_degrees is None:
		joint_angles_degrees = (0.0,) * 6
	if len(joint_angles_degrees) != 6:
		raise ValueError(f"Expected runtime angles for 6 joints, got {len(joint_angles_degrees)}")

	parameters = []
	for row, joint_angle in zip(static_values, joint_angles_degrees):
		if len(row) != 4:
			raise ValueError("Each static DH row must contain theta offset, d, a, and alpha")
		if not all(math.isfinite(value) for value in (*row, joint_angle)):
			raise ValueError("Static DH values and runtime joint angles must be finite")
		theta_offset, d, a, alpha = row
		parameters.append(
			DHParameters(
				theta=math.radians(theta_offset + joint_angle),
				d=d,
				a=a,
				alpha=math.radians(alpha),
			)
		)
	return tuple(parameters)


def _rotation(transform: Matrix4) -> tuple[tuple[float, float, float], ...]:
	return tuple(tuple(transform[row][column] for column in range(3)) for row in range(3))


def _transpose3(matrix: tuple[tuple[float, float, float], ...]) -> tuple[tuple[float, float, float], ...]:
	return tuple(tuple(matrix[column][row] for column in range(3)) for row in range(3))


def _multiply3(
	left: tuple[tuple[float, float, float], ...],
	right: tuple[tuple[float, float, float], ...],
) -> tuple[tuple[float, float, float], ...]:
	return tuple(
		tuple(sum(left[row][index] * right[index][column] for index in range(3)) for column in range(3))
		for row in range(3)
	)


def _wrap_angle(angle: float) -> float:
	return math.atan2(math.sin(angle), math.cos(angle))


def _solve_linear3(
	matrix: tuple[tuple[float, float, float], ...], vector: Vector3
) -> Vector3:
	"""Solve a 3x3 linear system with pivoted Gaussian elimination."""
	augmented = [list(matrix[row]) + [vector[row]] for row in range(3)]
	for column in range(3):
		pivot = max(range(column, 3), key=lambda row: abs(augmented[row][column]))
		if abs(augmented[pivot][column]) < 1e-15:
			raise ArithmeticError("Singular damped Jacobian system")
		augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
		pivot_value = augmented[column][column]
		for index in range(column, 4):
			augmented[column][index] /= pivot_value
		for row in range(3):
			if row == column:
				continue
			factor = augmented[row][column]
			for index in range(column, 4):
				augmented[row][index] -= factor * augmented[column][index]
	return (augmented[0][3], augmented[1][3], augmented[2][3])


def inverse_kinematics_position(
	target_position: Vector3,
	geometry: Sequence[DHParameters],
	*,
	initial_angles: Sequence[float] | None = None,
	tolerance: float = 1e-6,
	max_iterations: int = 200,
) -> PositionIKSolution | None:
	"""Find a position-matching pose while allowing end-effector orientation to vary.

	Uses damped least squares seeded from the current runtime joint angles. This
	mode is useful for Cartesian position jogging on mechanisms with fewer than
	six independent axes, where preserving arbitrary orientation can be
	overconstrained. Geometry theta values are static offsets; returned angles
	are runtime joint angles in radians.
	"""
	_validate_supported_geometry(geometry, tolerance)
	if len(target_position) != 3 or not all(math.isfinite(value) for value in target_position):
		raise ValueError("target_position must contain three finite values")
	if not math.isfinite(tolerance) or tolerance <= 0 or max_iterations <= 0:
		raise ValueError("tolerance and max_iterations must be positive")
	if initial_angles is None:
		angles = [0.0] * 6
	else:
		if len(initial_angles) != 6 or not all(math.isfinite(value) for value in initial_angles):
			raise ValueError("initial_angles must contain six finite runtime angles")
		angles = list(initial_angles)

	damping = 0.1
	best_error = math.inf
	for iteration in range(max_iterations + 1):
		parameters = tuple(
			replace(joint, theta=joint.theta + angle)
			for joint, angle in zip(geometry, angles)
		)
		transforms = forward_kinematics(parameters)
		position = frame_origin(transforms[-1])
		error = tuple(target_position[axis] - position[axis] for axis in range(3))
		error_norm = math.sqrt(sum(component * component for component in error))
		if error_norm <= tolerance:
			return PositionIKSolution(tuple(_wrap_angle(angle) for angle in angles), error_norm, iteration)
		if iteration == max_iterations:
			break

		jacobian_columns = []
		for joint_index in range(6):
			if joint_index == 0:
				previous_rotation = (
					(1.0, 0.0, 0.0),
					(0.0, 1.0, 0.0),
					(0.0, 0.0, 1.0),
				)
				joint_origin = (0.0, 0.0, 0.0)
			else:
				previous = transforms[joint_index - 1]
				previous_rotation = _rotation(previous)
				joint_origin = frame_origin(previous)
			axis = tuple(previous_rotation[row][2] for row in range(3))
			to_tool = tuple(position[axis_index] - joint_origin[axis_index] for axis_index in range(3))
			jacobian_columns.append((
				axis[1] * to_tool[2] - axis[2] * to_tool[1],
				axis[2] * to_tool[0] - axis[0] * to_tool[2],
				axis[0] * to_tool[1] - axis[1] * to_tool[0],
			))

		gram = tuple(
			tuple(
				sum(jacobian_columns[column][row] * jacobian_columns[column][other] for column in range(6))
				+ (damping * damping if row == other else 0.0)
				for other in range(3)
			)
			for row in range(3)
		)
		try:
			dual_step = _solve_linear3(gram, error)  # type: ignore[arg-type]
		except ArithmeticError:
			return None
		joint_step = tuple(
		sum(jacobian_columns[column][axis] * dual_step[axis] for axis in range(3))
			for column in range(6)
		)
		step_scale = min(1.0, 0.25 / max(math.sqrt(sum(value * value for value in joint_step)), 1e-12))
		candidate_angles = [angles[index] + step_scale * joint_step[index] for index in range(6)]
		candidate_parameters = tuple(
			replace(joint, theta=joint.theta + angle)
			for joint, angle in zip(geometry, candidate_angles)
		)
		candidate_position = frame_origin(forward_kinematics(candidate_parameters)[-1])
		candidate_error = math.dist(candidate_position, target_position)
		if candidate_error < error_norm:
			angles = candidate_angles
			best_error = candidate_error
			damping = max(1e-4, damping * 0.7)
		else:
			damping = min(10.0, damping * 2.0)
			if damping >= 10.0 and candidate_error >= best_error:
				break
			best_error = min(best_error, candidate_error)
	return None


def _validate_supported_geometry(parameters: Sequence[DHParameters], tolerance: float) -> None:
	if len(parameters) != 6:
		raise ValueError(f"Expected DH parameters for 6 joints, got {len(parameters)}")
	for joint in parameters:
		if not all(math.isfinite(value) for value in (joint.theta, joint.d, joint.a, joint.alpha)):
			raise ValueError("All DH parameters must be finite numbers")

	checks = (
		(parameters[0].alpha, math.pi / 2, "joint 1 alpha"),
		(parameters[1].d, 0.0, "joint 2 d"),
		(parameters[1].alpha, 0.0, "joint 2 alpha"),
		(parameters[2].a, 0.0, "joint 3 a"),
		(parameters[2].d, 0.0, "joint 3 d"),
		(parameters[2].alpha, 0.0, "joint 3 alpha"),
		(parameters[3].d, 0.0, "joint 4 d"),
		(parameters[3].alpha, math.pi / 2, "joint 4 alpha"),
		(parameters[4].a, 0.0, "joint 5 a"),
		(parameters[4].d, 0.0, "joint 5 d"),
		(parameters[4].alpha, -math.pi / 2, "joint 5 alpha"),
		(parameters[5].alpha, 0.0, "joint 6 alpha"),
		(parameters[5].d, 0.0, "joint 6 d"),
	)
	for actual, expected, name in checks:
		if not math.isclose(actual, expected, abs_tol=tolerance, rel_tol=0.0):
			raise ValueError(f"Inverse kinematics requires {name}={expected:g}, got {actual:g}")
	if parameters[1].a <= 0 or parameters[3].a <= 0 or parameters[5].a <= 0:
		raise ValueError("Inverse kinematics requires positive a2, a4, and a6")


def inverse_kinematics(
	target_pose: Matrix4,
	geometry: Sequence[DHParameters],
	*,
	preferred_theta3: float = 0.0,
	tolerance: float = 1e-7,
) -> tuple[InverseKinematicsSolution, ...]:
	"""Solve the supported robot's IK, returning valid shoulder/elbow branches.

	The supported DH geometry has two J1 plane branches and two planar elbow
	branches. Joints 3 and 4 are coaxial, so ``preferred_theta3`` selects one
	valid split of their observable sum. ``geometry`` theta values are static
	DH offsets; returned angles are variable joint angles in radians. Unreachable
	or pose-inconsistent targets return an empty tuple.
	"""
	_validate_supported_geometry(geometry, tolerance)
	if not math.isfinite(preferred_theta3) or not math.isfinite(tolerance) or tolerance <= 0:
		raise ValueError("preferred_theta3 must be finite and tolerance must be positive")
	if len(target_pose) != 4 or any(len(row) != 4 for row in target_pose):
		raise ValueError("target_pose must be a 4x4 homogeneous transform")
	if not all(math.isfinite(value) for row in target_pose for value in row):
		raise ValueError("target_pose must contain only finite values")
	if any(abs(target_pose[3][column] - expected) > tolerance for column, expected in enumerate((0, 0, 0, 1))):
		raise ValueError("target_pose must have homogeneous bottom row [0, 0, 0, 1]")

	target_position: Vector3 = tuple(target_pose[row][3] for row in range(3))  # type: ignore[assignment]
	target_rotation = _rotation(target_pose)
	wrist_center: Vector3 = tuple(
		target_position[axis]
		- geometry[5].a * target_rotation[axis][0]
		- geometry[5].d * target_rotation[axis][2]
		for axis in range(3)
	)  # type: ignore[assignment]
	base_radius = math.hypot(wrist_center[0], wrist_center[1])
	if base_radius <= tolerance:
		return ()

	a1 = geometry[0].a
	d1 = geometry[0].d
	link_one = geometry[1].a
	link_two = geometry[3].a
	wrist_height = wrist_center[2] - d1
	preferred_theta3 = _wrap_angle(preferred_theta3)
	solutions: list[InverseKinematicsSolution] = []

	for shoulder_branch in (1, -1):
		total_theta1 = math.atan2(
			shoulder_branch * wrist_center[1], shoulder_branch * wrist_center[0]
		)
		radial_target = shoulder_branch * base_radius - a1
		distance = math.hypot(radial_target, wrist_height)
		cosine = (distance * distance - link_one * link_one - link_two * link_two) / (
			2 * link_one * link_two
		)
		if cosine < -1 - tolerance or cosine > 1 + tolerance:
			continue
		cosine = max(-1.0, min(1.0, cosine))

		for elbow_branch in (1, -1):
			psi = elbow_branch * math.acos(cosine)
			total_theta2 = math.atan2(wrist_height, radial_target) - math.atan2(
				link_two * math.sin(psi), link_one + link_two * math.cos(psi)
			)
			theta3 = preferred_theta3
			total_theta3 = geometry[2].theta + theta3
			theta4 = _wrap_angle(psi - total_theta3 - geometry[3].theta)
			partial = tuple(
				replace(joint, theta=joint.theta + angle)
				for joint, angle in zip(
					geometry,
					(
						total_theta1 - geometry[0].theta,
						total_theta2 - geometry[1].theta,
						theta3,
						theta4,
						-geometry[4].theta,
						-geometry[5].theta,
					),
				)
			)
			frame_four = forward_kinematics(partial)[3]
			rotation_four = _rotation(frame_four)
			relative_rotation = _multiply3(_transpose3(rotation_four), target_rotation)
			theta5 = math.atan2(-relative_rotation[0][2], relative_rotation[1][2])
			theta6 = math.atan2(-relative_rotation[2][0], -relative_rotation[2][1])
			angles = (
				total_theta1 - geometry[0].theta,
				total_theta2 - geometry[1].theta,
				theta3,
				theta4,
				theta5 - geometry[4].theta,
				theta6 - geometry[5].theta,
			)
			reconstructed = forward_kinematics(
				tuple(
					replace(joint, theta=joint.theta + angle)
					for joint, angle in zip(geometry, angles)
				)
			)[-1]
			position_error = math.sqrt(
				sum((reconstructed[row][3] - target_position[row]) ** 2 for row in range(3))
			)
			orientation_error = math.sqrt(
				sum(
					(reconstructed[row][column] - target_pose[row][column]) ** 2
					for row in range(3)
					for column in range(3)
				)
			)
			if position_error <= tolerance and orientation_error <= tolerance:
				solutions.append(
					InverseKinematicsSolution(
						angles=angles,
						shoulder_branch=shoulder_branch,
						elbow_branch=elbow_branch,
						position_error=position_error,
						orientation_error=orientation_error,
					)
				)

	return tuple(solutions)