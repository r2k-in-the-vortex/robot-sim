"""Round-trip tests for six-axis standard-DH kinematics."""

from __future__ import annotations

import json
import math
import random
import unittest
from dataclasses import replace
from pathlib import Path

from kinematics import DHParameters, compose_dh_parameters, forward_kinematics, inverse_kinematics


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
			combined_elbow_angle = angle_error(
				self.geometry[2].theta + angles[2] + self.geometry[3].theta + angles[3], 0.0
			)
			expected_elbow_branch = 1 if math.sin(combined_elbow_angle) >= 0 else -1

			solutions = inverse_kinematics(
				target_pose,
				self.geometry,
				preferred_theta3=angles[2],
			)
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


if __name__ == "__main__":
	unittest.main()