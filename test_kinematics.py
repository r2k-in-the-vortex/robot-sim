"""Round-trip tests for six-axis standard-DH kinematics."""

from __future__ import annotations

import json
import math
import random
import unittest
from dataclasses import replace
from pathlib import Path

from kinematics import (
	DHParameters,
	compose_dh_parameters,
	forward_kinematics,
	frame_origin,
	inverse_kinematics,
	inverse_kinematics_position,
	inverse_kinematics_position_preserving_roll_yaw,
)


def rotation_to_rpy_degrees(transform: tuple[tuple[float, ...], ...]) -> tuple[float, float, float]:
	"""Extract roll, pitch, yaw for R = Rz(yaw) Ry(pitch) Rx(roll)."""
	r00, r01 = transform[0][0], transform[0][1]
	r10, r11 = transform[1][0], transform[1][1]
	r20, r21, r22 = transform[2][0], transform[2][1], transform[2][2]
	pitch = math.atan2(-r20, math.hypot(r00, r10))
	if math.hypot(r00, r10) > 1e-9:
		roll = math.atan2(r21, r22)
		yaw = math.atan2(r10, r00)
	else:
		roll = 0.0
		yaw = math.atan2(-r01, r11)
	return tuple(math.degrees(angle) for angle in (roll, pitch, yaw))


def pose_translated(
	pose: tuple[tuple[float, ...], ...], axis: int, distance: float
) -> tuple[tuple[float, ...], ...]:
	"""Return a pose translated along one base-frame axis, preserving orientation."""
	result = [list(row) for row in pose]
	result[axis][3] += distance
	return tuple(tuple(row) for row in result)


def pose_rotated_about_world_axis(
	pose: tuple[tuple[float, ...], ...], axis: int, angle: float
) -> tuple[tuple[float, ...], ...]:
	"""Return a pose rotated about a base-frame axis, keeping its origin fixed."""
	cosine = math.cos(angle)
	sine = math.sin(angle)
	if axis == 0:
		rotation = ((1.0, 0.0, 0.0), (0.0, cosine, -sine), (0.0, sine, cosine))
	elif axis == 1:
		rotation = ((cosine, 0.0, sine), (0.0, 1.0, 0.0), (-sine, 0.0, cosine))
	else:
		rotation = ((cosine, -sine, 0.0), (sine, cosine, 0.0), (0.0, 0.0, 1.0))
	result = [list(row) for row in pose]
	for row in range(3):
		for column in range(3):
			result[row][column] = sum(rotation[row][index] * pose[index][column] for index in range(3))
	return tuple(tuple(row) for row in result)


def configured_geometry() -> tuple[DHParameters, ...]:
	configuration_path = Path(__file__).with_name("robot_parameters.json")
	configuration = json.loads(configuration_path.read_text(encoding="utf-8"))
	return tuple(
		DHParameters(
			theta=math.radians(float(joint.get("theta_offset_deg", joint.get("theta_deg", 0.0)))),
			d=float(joint["d"]),
			a=float(joint["a"]),
			alpha=math.radians(float(joint["alpha_deg"])),
		)
		for joint in configuration["joints"]
	)


def parameters_at_angles(
	geometry: tuple[DHParameters, ...], angles: tuple[float, ...]
) -> tuple[DHParameters, ...]:
	return tuple(replace(joint, theta=joint.theta + angle) for joint, angle in zip(geometry, angles))


def angle_error(first: float, second: float) -> float:
	return math.atan2(math.sin(first - second), math.cos(first - second))


class InverseKinematicsRoundTripTests(unittest.TestCase):
	@classmethod
	def setUpClass(cls) -> None:
		cls.geometry = configured_geometry()

	def test_static_theta_offsets_compose_with_runtime_angles(self) -> None:
		static_values = (
			(12.0, 0.3, 0.1, 90.0),
			(-25.0, 0.0, 0.4, 0.0),
			(5.0, 0.0, 0.0, 0.0),
			(0.0, 0.0, 0.3, 90.0),
			(0.0, 0.0, 0.0, -90.0),
			(0.0, 0.0, 0.12, 0.0),
		)
		startup_parameters = compose_dh_parameters(static_values)
		self.assertAlmostEqual(startup_parameters[0].theta, math.radians(12.0))
		self.assertAlmostEqual(startup_parameters[1].theta, math.radians(-25.0))

		joint_angles = (30.0, 10.0, -15.0, 0.0, 5.0, -20.0)
		moving_parameters = compose_dh_parameters(static_values, joint_angles)
		for parameters, static_row, variable_angle in zip(moving_parameters, static_values, joint_angles):
			self.assertAlmostEqual(parameters.theta, math.radians(static_row[0] + variable_angle))
			self.assertEqual((parameters.d, parameters.a), (static_row[1], static_row[2]))

	def test_configuration_persists_offsets_not_runtime_angles(self) -> None:
		configuration = json.loads(
			Path(__file__).with_name("robot_parameters.json").read_text(encoding="utf-8")
		)
		gizmo_visibility = configuration["show_coordinate_gizmos"]
		self.assertEqual(len(gizmo_visibility), 7)
		for visible in gizmo_visibility:
			self.assertIsInstance(visible, bool)
		for joint in configuration["joints"]:
			self.assertIn("theta_offset_deg", joint)
			self.assertNotIn("theta_deg", joint)
			self.assertNotIn("joint_angle_deg", joint)

		startup_parameters = compose_dh_parameters(
			tuple(
				(
					float(joint["theta_offset_deg"]),
					float(joint["d"]),
					float(joint["a"]),
					float(joint["alpha_deg"]),
				)
				for joint in configuration["joints"]
			)
		)
		for parameters, joint in zip(startup_parameters, configuration["joints"]):
			self.assertAlmostEqual(parameters.theta, math.radians(joint["theta_offset_deg"]))

	def test_random_fk_poses_recover_angles_and_branch_labels(self) -> None:
		random_source = random.Random(20261009)
		for trial in range(100):
			angles = tuple(random_source.uniform(-math.pi, math.pi) for _ in range(6))
			transforms = forward_kinematics(parameters_at_angles(self.geometry, angles))
			target_pose = transforms[-1]
			frame_five_position = tuple(target_pose[row][3] for row in range(3))
			frame_five_position = tuple(
				frame_five_position[axis]
				- self.geometry[5].a * target_pose[axis][0]
				- self.geometry[5].d * target_pose[axis][2]
				for axis in range(3)
			)
			projected_radius = (
				frame_five_position[0] * math.cos(self.geometry[0].theta + angles[0])
				+ frame_five_position[1] * math.sin(self.geometry[0].theta + angles[0])
			)
			expected_shoulder_branch = 1 if projected_radius >= 0 else -1
			elbow_angle = angle_error(
				self.geometry[2].theta + angles[2] - math.pi / 2, 0.0
			)
			expected_elbow_branch = 1 if math.sin(elbow_angle) >= 0 else -1

			solutions = inverse_kinematics(target_pose, self.geometry)
			matching_branches = [
				solution
				for solution in solutions
				if solution.shoulder_branch == expected_shoulder_branch
				and solution.elbow_branch == expected_elbow_branch
			]
			self.assertTrue(matching_branches, f"trial {trial}: expected branch was not returned")

			best_solution = min(
				matching_branches,
				key=lambda solution: max(
					abs(angle_error(recovered, expected))
					for recovered, expected in zip(solution.angles, angles)
				),
			)
			for recovered, expected in zip(best_solution.angles, angles):
				self.assertAlmostEqual(angle_error(recovered, expected), 0.0, delta=1e-7)

			recovered_pose = forward_kinematics(
				parameters_at_angles(self.geometry, best_solution.angles)
			)[-1]
			for actual_row, expected_row in zip(recovered_pose, target_pose):
				for actual, expected in zip(actual_row, expected_row):
					self.assertAlmostEqual(actual, expected, delta=1e-8)

	def test_unreachable_target_returns_no_solutions(self) -> None:
		identity = (
			(1.0, 0.0, 0.0, 100.0),
			(0.0, 1.0, 0.0, 100.0),
			(0.0, 0.0, 1.0, 100.0),
			(0.0, 0.0, 0.0, 1.0),
		)
		self.assertEqual(inverse_kinematics(identity, self.geometry), ())

	def test_orientation_inconsistent_with_target_position_is_rejected(self) -> None:
		angles = (0.7, -0.3, 0.8, -0.2, 1.1, -0.6)
		target = list(forward_kinematics(parameters_at_angles(self.geometry, angles))[-1])
		target_rotation_row = list(target[0])
		target_rotation_row[0] *= -1
		target[0] = tuple(target_rotation_row)
		self.assertEqual(inverse_kinematics(tuple(target), self.geometry), ())

	def test_position_only_solvers_reach_known_targets(self) -> None:
		commanded_degrees = (25.0, -35.0, 30.0, 40.0, -55.0, 15.0)
		commanded = tuple(math.radians(value) for value in commanded_degrees)
		start_pose = forward_kinematics(parameters_at_angles(self.geometry, commanded))[-1]
		start_position = frame_origin(start_pose)
		self.assertTrue(inverse_kinematics(start_pose, self.geometry))

		start_solution = inverse_kinematics_position(
			start_position, self.geometry, initial_angles=(0.0,) * 6
		)
		self.assertIsNotNone(start_solution)
		assert start_solution is not None
		start_pose = forward_kinematics(
			parameters_at_angles(self.geometry, start_solution.angles)
		)[-1]
		for actual, expected in zip(frame_origin(start_pose), start_position):
			self.assertAlmostEqual(actual, expected, delta=1e-5)
		start_rpy = tuple(math.radians(value) for value in rotation_to_rpy_degrees(start_pose))
		position_solution = inverse_kinematics_position_preserving_roll_yaw(
			(start_position[0], start_position[1] + 1.0, start_position[2]),
			self.geometry,
			initial_angles=start_solution.angles,
			preserved_roll_yaw=(start_rpy[0], start_rpy[2]),
		)
		self.assertIsNotNone(position_solution)
		assert position_solution is not None
		achieved_pose = forward_kinematics(
			parameters_at_angles(self.geometry, position_solution.angles)
		)[-1]
		for actual, expected in zip(
			frame_origin(achieved_pose), (start_position[0], start_position[1] + 1.0, start_position[2])
		):
			self.assertAlmostEqual(actual, expected, delta=1e-5)
		achieved_rpy = rotation_to_rpy_degrees(achieved_pose)
		# The delta is the solver's own: `inverse_kinematics_position_preserving_roll_yaw`
		# stops as soon as roll, yaw and position are inside `tolerance = 1e-5` radians
		# (kinematics.py:261), so the assertion cannot ask for more than that. A `1e-4`
		# *degree* delta is six times tighter and held only at the previous link lengths,
		# by where the iteration happened to stop.
		delta = math.degrees(1e-5)
		self.assertAlmostEqual(achieved_rpy[0], math.degrees(start_rpy[0]), delta=delta)
		self.assertAlmostEqual(achieved_rpy[2], math.degrees(start_rpy[2]), delta=delta)


class JointwiseInverseKinematicsTests(unittest.TestCase):
	"""Check inverse kinematics one joint at a time against known FK answers.

	Every target pose below is built by forward kinematics from a joint vector
	that is known before the solver runs, so each case has an exact expected
	answer. Sweeps move a single joint at a time, so a failure names the joint at
	fault, and the geometry comes from ``robot_parameters.json``, so the checks
	follow whatever DH table the parameter tab was last saved with.
	"""

	sweep_angles_degrees = tuple(range(-180, 181, 15))
	base_configurations_degrees = (
		(0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
		(0.0, 0.0, 0.0, 0.0, 40.0, 0.0),
		(30.0, -25.0, 20.0, 45.0, -50.0, 10.0),
	)
	point_to_point_degrees = (25.0, -35.0, 30.0, 40.0, -55.0, 15.0)

	@classmethod
	def setUpClass(cls) -> None:
		cls.geometry = configured_geometry()

	def known_pose(self, joint_angles_degrees) -> tuple[tuple[tuple[float, ...], ...], tuple[float, ...]]:
		"""Return the pose a known joint vector produces, with its radians."""
		angles = tuple(math.radians(value) for value in joint_angles_degrees)
		return forward_kinematics(parameters_at_angles(self.geometry, angles))[-1], angles

	def assert_pose_reproduced(self, solutions, target_pose, message: str) -> None:
		"""Fail unless at least one solution exists and all of them match the pose."""
		self.assertTrue(solutions, f"{message}: no inverse-kinematics solution")
		for solution in solutions:
			recovered = forward_kinematics(parameters_at_angles(self.geometry, solution.angles))[-1]
			position_error = math.dist(frame_origin(recovered), frame_origin(target_pose))
			orientation_error = math.sqrt(
				sum(
					(recovered[row][column] - target_pose[row][column]) ** 2
					for row in range(3)
					for column in range(3)
				)
			)
			self.assertLessEqual(position_error, 1e-8, f"{message}: position error {position_error:g}")
			self.assertLessEqual(orientation_error, 1e-8, f"{message}: orientation error {orientation_error:g}")

	def pose_pins_down_every_joint(self, target_pose, angles) -> bool:
		"""Whether the target determines this joint vector uniquely.

		Three configurations leave a joint free, so the commanded angles are not
		the only valid answer and angle recovery cannot be asserted for them: a
		wrist center on the base axis frees joint 1, one sitting on frame 1 frees
		joint 2 whenever the two links are equal, and sin(theta5) = 0 makes joints
		4 and 6 share an axis, leaving only their sum observable. Such poses are
		still solvable, and the sweeps assert the pose for them.
		"""
		wrist_center = tuple(
			target_pose[axis][3]
			- self.geometry[5].a * target_pose[axis][0]
			- self.geometry[5].d * target_pose[axis][2]
			for axis in range(3)
		)
		frame_one_origin = (
			self.geometry[0].a * math.cos(self.geometry[0].theta + angles[0]),
			self.geometry[0].a * math.sin(self.geometry[0].theta + angles[0]),
			self.geometry[0].d,
		)
		return (
			math.hypot(wrist_center[0], wrist_center[1]) > 1e-6
			and math.dist(wrist_center, frame_one_origin) > 1e-6
			and abs(math.sin(self.geometry[4].theta + angles[4])) > 1e-6
		)

	def test_each_joint_sweep_round_trips(self) -> None:
		for joint_index in range(6):
			for base_degrees in self.base_configurations_degrees:
				for sweep_degrees in self.sweep_angles_degrees:
					commanded_degrees = list(base_degrees)
					commanded_degrees[joint_index] = float(sweep_degrees)
					label = f"J{joint_index + 1} at {sweep_degrees:g} deg from {base_degrees}"
					with self.subTest(joint=joint_index + 1, base=base_degrees, angle=sweep_degrees):
						target_pose, commanded = self.known_pose(commanded_degrees)
						solutions = inverse_kinematics(target_pose, self.geometry)
						self.assert_pose_reproduced(solutions, target_pose, label)
						if self.pose_pins_down_every_joint(target_pose, commanded):
							best_recovery = min(
								max(
									abs(angle_error(recovered, expected))
									for recovered, expected in zip(solution.angles, commanded)
								)
								for solution in solutions
							)
							self.assertLessEqual(
								best_recovery, 1e-7, f"{label}: commanded angles were not recovered"
							)

	def test_point_to_point_steps_stay_on_the_same_branch(self) -> None:
		start_pose, commanded = self.known_pose(self.point_to_point_degrees)
		step = 1.0
		requests = [
			pose_translated(start_pose, axis, direction * step)
			for axis in range(3)
			for direction in (-1, 1)
		] + [
			pose_rotated_about_world_axis(start_pose, axis, math.radians(5.0)) for axis in range(3)
		]
		for index, target_pose in enumerate(requests):
			with self.subTest(target=index):
				solutions = inverse_kinematics(target_pose, self.geometry)
				self.assert_pose_reproduced(solutions, target_pose, f"step target {index}")
				nearest = min(
					solutions,
					key=lambda solution: sum(
						angle_error(recovered, expected) ** 2
						for recovered, expected in zip(solution.angles, commanded)
					),
				)
				for recovered, expected in zip(nearest.angles, commanded):
					self.assertLessEqual(
						abs(angle_error(recovered, expected)),
						math.radians(20.0),
						f"step target {index} jumped to another branch",
					)

	def test_random_fk_poses_return_only_matching_solutions(self) -> None:
		random_source = random.Random(20261014)
		for trial in range(50):
			angles = tuple(random_source.uniform(-math.pi, math.pi) for _ in range(6))
			target_pose = forward_kinematics(parameters_at_angles(self.geometry, angles))[-1]
			with self.subTest(trial=trial):
				solutions = inverse_kinematics(target_pose, self.geometry)
				self.assert_pose_reproduced(solutions, target_pose, f"trial {trial}")
				self.assertLessEqual(len(solutions), 8)
				best_recovery = min(
					max(
						abs(angle_error(recovered, expected))
						for recovered, expected in zip(solution.angles, angles)
					)
					for solution in solutions
				)
				self.assertLessEqual(best_recovery, 1e-7, f"trial {trial}: commanded angles were not recovered")

	def test_wrist_singularity_is_solvable(self) -> None:
		for base_degrees in ((0.0,) * 6, (20.0, -30.0, 40.0, 0.0, 0.0, 60.0)):
			commanded_degrees = list(base_degrees)
			commanded_degrees[4] = math.degrees(-self.geometry[4].theta)
			with self.subTest(base=base_degrees):
				target_pose, commanded = self.known_pose(commanded_degrees)
				solutions = inverse_kinematics(target_pose, self.geometry)
				self.assert_pose_reproduced(solutions, target_pose, "wrist singularity")
				self.assertFalse(self.pose_pins_down_every_joint(target_pose, commanded))
				self.assertTrue(
					any(
						abs(math.sin(self.geometry[4].theta + solution.angles[4])) < 1e-6
						for solution in solutions
					),
					"expected a solution that sits at the wrist singularity",
				)

	def test_structure_validation_names_the_unsupported_parameter(self) -> None:
		target_pose = forward_kinematics(self.geometry)[-1]
		perturbations = (
			(2, "alpha", math.radians(45.0), "joint 3 alpha"),
			(1, "d", 5.0, "joint 2 d"),
			(3, "a", 5.0, "joint 4 a"),
			(3, "d", 0.0, "d4"),
		)
		for joint_index, field, value, expected_text in perturbations:
			geometry = tuple(
				replace(joint, **{field: value}) if index == joint_index else joint
				for index, joint in enumerate(self.geometry)
			)
			with self.subTest(joint=joint_index + 1, field=field):
				with self.assertRaises(ValueError) as context:
					inverse_kinematics(target_pose, geometry)
				self.assertIn(expected_text, str(context.exception))


if __name__ == "__main__":
	unittest.main()