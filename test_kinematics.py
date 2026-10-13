"""Round-trip tests for six-axis standard-DH kinematics."""

from __future__ import annotations

import json
import math
import random
import unittest
from dataclasses import replace
from pathlib import Path
import tkinter as tk

from kinematics import (
	DHParameters,
	compose_dh_parameters,
	forward_kinematics,
	frame_origin,
	inverse_kinematics,
	inverse_kinematics_position,
	inverse_kinematics_position_preserving_roll_yaw,
)
from simulator import (
	_rotation_to_rpy_degrees,
	offset_pose_translation,
	rotate_pose_world_axis,
)


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

	def test_cartesian_jogs_preserve_orientation_and_remain_solvable(self) -> None:
		current_pose = forward_kinematics(self.geometry)[-1]
		step = 0.01
		for axis in range(3):
			for direction in (-1, 1):
				target_pose = offset_pose_translation(current_pose, axis, direction * step)
				for row in range(3):
					for column in range(3):
						self.assertEqual(target_pose[row][column], current_pose[row][column])
					self.assertAlmostEqual(
						target_pose[row][3] - current_pose[row][3],
						direction * step if row == axis else 0.0,
					)
				self.assertTrue(inverse_kinematics(target_pose, self.geometry))

	def test_world_rotation_jog_premultiplies_rotation_and_preserves_position(self) -> None:
		pose = forward_kinematics(parameters_at_angles(self.geometry, (0.2, -0.3, 0.4, -0.1, 0.5, -0.6)))[-1]
		rotated = rotate_pose_world_axis(pose, 2, math.pi / 2)
		self.assertEqual(frame_origin(rotated), frame_origin(pose))
		for column in range(3):
			self.assertAlmostEqual(rotated[0][column], -pose[1][column], delta=1e-12)
			self.assertAlmostEqual(rotated[1][column], pose[0][column], delta=1e-12)
			self.assertAlmostEqual(rotated[2][column], pose[2][column], delta=1e-12)

	def test_plus_y_jog_from_requested_t6_position_is_reachable(self) -> None:
		startup_pose = [list(row) for row in forward_kinematics(self.geometry)[-1]]
		startup_pose[0][3] = 36.0
		startup_pose[1][3] = 0.0
		startup_pose[2][3] = 58.0
		current_pose = tuple(tuple(row) for row in startup_pose)
		self.assertTrue(inverse_kinematics(current_pose, self.geometry))

		target_pose = offset_pose_translation(current_pose, 1, 1.0)
		self.assertFalse(inverse_kinematics(target_pose, self.geometry))
		start_solution = inverse_kinematics_position(
			(36.0, 0.0, 58.0), self.geometry, initial_angles=(0.0,) * 6
		)
		self.assertIsNotNone(start_solution)
		assert start_solution is not None
		start_pose = forward_kinematics(
			parameters_at_angles(self.geometry, start_solution.angles)
		)[-1]
		start_rpy = tuple(math.radians(value) for value in _rotation_to_rpy_degrees(start_pose))
		position_solution = inverse_kinematics_position_preserving_roll_yaw(
			(36.0, 1.0, 58.0),
			self.geometry,
			initial_angles=start_solution.angles,
			preserved_roll_yaw=(start_rpy[0], start_rpy[2]),
		)
		self.assertIsNotNone(position_solution)
		assert position_solution is not None
		achieved_pose = forward_kinematics(
			parameters_at_angles(self.geometry, position_solution.angles)
		)[-1]
		for actual, expected in zip(frame_origin(achieved_pose), (36.0, 1.0, 58.0)):
			self.assertAlmostEqual(actual, expected, delta=1e-5)
		achieved_rpy = _rotation_to_rpy_degrees(achieved_pose)
		self.assertAlmostEqual(achieved_rpy[0], math.degrees(start_rpy[0]), delta=1e-4)
		self.assertAlmostEqual(achieved_rpy[2], math.degrees(start_rpy[2]), delta=1e-4)

	def test_tk_y_jog_preserves_orientation_or_refuses_move(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			self.assertEqual(app.jog_step_entry.get(), "1")
			start_solution = inverse_kinematics_position(
				(36.0, 0.0, 58.0), self.geometry, initial_angles=(0.0,) * 6
			)
			self.assertIsNotNone(start_solution)
			assert start_solution is not None
			for entry, angle in zip(app.joint_angle_entries, start_solution.angles):
				entry.delete(0, tk.END)
				entry.insert(0, str(math.degrees(angle)))
			self.assertTrue(app._apply_from_entries())
			start_position = frame_origin(forward_kinematics(app.parameters)[-1])
			for actual, expected in zip(start_position, (36.0, 0.0, 58.0)):
				self.assertAlmostEqual(actual, expected, delta=1e-5)
			start_pose = forward_kinematics(app.parameters)[-1]
			app._jog_cartesian(1, 1)
			end_pose = forward_kinematics(app.parameters)[-1]
			self.assertIn("No exact-pose IK solution", app.jog_status_label.cget("text"))
			for before_row, after_row in zip(start_pose, end_pose):
				for before_value, after_value in zip(before_row, after_row):
					self.assertAlmostEqual(before_value, after_value, delta=1e-9)
			app._copy_t6_position()
			copied_lines = app.root.clipboard_get().splitlines()
			self.assertEqual(copied_lines[0], "T6 position (model units):")
			self.assertEqual(copied_lines[4], "T6 orientation (RPY, ZYX, degrees):")
			self.assertEqual(copied_lines[8], "Runtime joint angles (degrees):")
			self.assertEqual(len(copied_lines), 15)
			copied_position = tuple(float(copied_lines[index].split(": ", 1)[1]) for index in (1, 2, 3))
			for actual, expected in zip(copied_position, (36.0, 0.0, 58.0)):
				self.assertAlmostEqual(actual, expected, delta=1e-5)
			copied_angles = tuple(float(copied_lines[index].split(": ", 1)[1]) for index in range(9, 15))
			for actual, entry in zip(copied_angles, app.joint_angle_entries):
				self.assertAlmostEqual(actual, float(entry.get()), delta=1e-10)
		finally:
			app.root.destroy()

	def test_tk_unreachable_minus_z_jog_does_not_change_orientation(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			start_rows = [list(row) for row in forward_kinematics(self.geometry)[-1]]
			start_rows[0][3], start_rows[1][3], start_rows[2][3] = 52.0, -1.0, 70.0
			start_pose = tuple(tuple(row) for row in start_rows)
			start_solutions = inverse_kinematics(start_pose, self.geometry)
			self.assertTrue(start_solutions)
			start_angles = start_solutions[0].angles
			for entry, angle in zip(app.joint_angle_entries, start_angles):
				entry.delete(0, tk.END)
				entry.insert(0, str(math.degrees(angle)))
			self.assertTrue(app._apply_from_entries())
			before = forward_kinematics(app.parameters)[-1]
			app._jog_cartesian(2, -1)
			after = forward_kinematics(app.parameters)[-1]
			self.assertIn("No exact-pose IK solution", app.jog_status_label.cget("text"))
			for before_row, after_row in zip(before, after):
				for before_value, after_value in zip(before_row, after_row):
					self.assertAlmostEqual(before_value, after_value, delta=1e-9)
		finally:
			app.root.destroy()

	def test_tk_world_rotation_jog_keeps_t6_position_fixed(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			self.assertEqual(app.rotation_step_entry.get(), "5")
			before = forward_kinematics(app.parameters)[-1]
			expected = rotate_pose_world_axis(before, 1, math.radians(5.0))
			app._jog_rotation_world(1, 1)
			self.assertEqual(app.jog_status_label.cget("text"), "Rotated RY +5 deg")
			after = forward_kinematics(app.parameters)[-1]
			for actual, position in zip(frame_origin(after), frame_origin(before)):
				self.assertAlmostEqual(actual, position, delta=1e-7)
			for actual_row, expected_row in zip(after, expected):
				for actual, expected_value in zip(actual_row[:3], expected_row[:3]):
					self.assertAlmostEqual(actual, expected_value, delta=1e-7)
		finally:
			app.root.destroy()

	def test_tk_joint_jogs_mirror_parameters_tab_angles(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			self.assertEqual(app.joint_step_entry.get(), "5")
			app._jog_joint(0, 1)
			self.assertEqual(float(app.joint_angle_entries[0].get()), 5.0)
			self.assertEqual(app.front_joint_angle_vars[0].get(), "5.0°")
			pose_after_front_jog = forward_kinematics(app.parameters)[-1]
			self.assertNotEqual(frame_origin(pose_after_front_jog), frame_origin(forward_kinematics(self.geometry)[-1]))

			app.joint_angle_entries[2].delete(0, tk.END)
			app.joint_angle_entries[2].insert(0, "-12.5")
			self.assertTrue(app._apply_from_entries())
			self.assertEqual(app.front_joint_angle_vars[2].get(), "-12.5°")
			self.assertAlmostEqual(app.parameters[2].theta, self.geometry[2].theta + math.radians(-12.5))
		finally:
			app.root.destroy()


if __name__ == "__main__":
	unittest.main()