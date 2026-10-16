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
	offset_pose_tool_translation,
	offset_pose_translation,
	rotate_pose_tool_axis,
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

	def test_tool_translation_moves_along_the_tool_axis(self) -> None:
		pose = forward_kinematics(
			parameters_at_angles(self.geometry, (0.2, -0.3, 0.4, -0.1, 0.5, -0.6))
		)[-1]
		step = 2.5
		for axis in range(3):
			with self.subTest(axis=axis):
				moved = offset_pose_tool_translation(pose, axis, step)
				for row in range(3):
					for column in range(3):
						self.assertEqual(moved[row][column], pose[row][column])
					self.assertAlmostEqual(
						moved[row][3] - pose[row][3], step * pose[row][axis], delta=1e-12
					)

	def test_tool_rotation_postmultiplies_and_keeps_position(self) -> None:
		pose = forward_kinematics(
			parameters_at_angles(self.geometry, (0.2, -0.3, 0.4, -0.1, 0.5, -0.6))
		)[-1]
		turned = rotate_pose_tool_axis(pose, 2, math.pi / 2)
		self.assertEqual(frame_origin(turned), frame_origin(pose))
		# Turning about the tool's own Z carries its X axis onto its Y axis,
		# which is what separates this from the world-axis rotation below.
		for row in range(3):
			self.assertAlmostEqual(turned[row][0], pose[row][1], delta=1e-12)
			self.assertAlmostEqual(turned[row][1], -pose[row][0], delta=1e-12)
			self.assertAlmostEqual(turned[row][2], pose[row][2], delta=1e-12)

	def test_tool_rotation_differs_from_world_rotation(self) -> None:
		pose = forward_kinematics(
			parameters_at_angles(self.geometry, (0.2, -0.3, 0.4, -0.1, 0.5, -0.6))
		)[-1]
		angle = math.radians(30.0)
		tool_rotated = rotate_pose_tool_axis(pose, 1, angle)
		world_rotated = rotate_pose_world_axis(pose, 1, angle)
		largest_difference = max(
			abs(tool_rotated[row][column] - world_rotated[row][column])
			for row in range(3)
			for column in range(3)
		)
		self.assertGreater(largest_difference, 0.1)
		restored = rotate_pose_tool_axis(tool_rotated, 1, -angle)
		for row in range(3):
			for column in range(3):
				self.assertAlmostEqual(restored[row][column], pose[row][column], delta=1e-12)

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
		start_rpy = tuple(math.radians(value) for value in _rotation_to_rpy_degrees(start_pose))
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
		achieved_rpy = _rotation_to_rpy_degrees(achieved_pose)
		# The delta is the solver's own: `inverse_kinematics_position_preserving_roll_yaw`
		# stops as soon as roll, yaw and position are inside `tolerance = 1e-5` radians
		# (kinematics.py:261), so the assertion cannot ask for more than that. A `1e-4`
		# *degree* delta is six times tighter and held only at the previous link lengths,
		# by where the iteration happened to stop.
		delta = math.degrees(1e-5)
		self.assertAlmostEqual(achieved_rpy[0], math.degrees(start_rpy[0]), delta=delta)
		self.assertAlmostEqual(achieved_rpy[2], math.degrees(start_rpy[2]), delta=delta)

	def test_tk_cartesian_jog_moves_to_requested_pose(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			self.assertEqual(app.jog_step_entry.get(), "1")
			for entry, value in zip(app.joint_angle_entries, (25.0, -35.0, 30.0, 40.0, -55.0, 15.0)):
				entry.delete(0, tk.END)
				entry.insert(0, str(value))
			self.assertTrue(app._apply_from_entries())
			start_pose = forward_kinematics(app.parameters)[-1]
			app._jog_cartesian(1, 1)
			self.assertEqual(app.jog_status_label.cget("text"), "Moved base Y +1")
			end_pose = forward_kinematics(app.parameters)[-1]
			for actual, expected in zip(
				frame_origin(end_pose), (start_pose[0][3], start_pose[1][3] + 1.0, start_pose[2][3])
			):
				self.assertAlmostEqual(actual, expected, delta=1e-5)
			for row in range(3):
				for column in range(3):
					self.assertAlmostEqual(end_pose[row][column], start_pose[row][column], delta=1e-7)
			app._copy_t6_position()
			copied_lines = app.root.clipboard_get().splitlines()
			self.assertEqual(copied_lines[0], "T6 position (model units):")
			self.assertEqual(copied_lines[4], "T6 orientation (RPY, ZYX, degrees):")
			self.assertEqual(copied_lines[8], "Runtime joint angles (degrees):")
			self.assertEqual(len(copied_lines), 15)
			copied_position = tuple(float(copied_lines[index].split(": ", 1)[1]) for index in (1, 2, 3))
			for actual, expected in zip(copied_position, frame_origin(end_pose)):
				self.assertAlmostEqual(actual, expected, delta=1e-5)
			# The clipboard carries the runtime angles at full precision, while the
			# entry fields show them rounded, so compare against the stored angles
			# and check the fields only agree to display precision.
			copied_angles = tuple(float(copied_lines[index].split(": ", 1)[1]) for index in range(9, 15))
			for actual, current, entry in zip(copied_angles, app.joint_angles_degrees, app.joint_angle_entries):
				self.assertAlmostEqual(actual, current, delta=1e-12)
				self.assertAlmostEqual(float(entry.get()), current, delta=1e-3)
		finally:
			app.root.destroy()

	def test_tk_tool_jogs_move_along_and_about_the_tool_axes(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			for entry, value in zip(app.joint_angle_entries, (25.0, -35.0, 30.0, 40.0, -55.0, 15.0)):
				entry.delete(0, tk.END)
				entry.insert(0, str(value))
			self.assertTrue(app._apply_from_entries())
			start_pose = forward_kinematics(app.parameters)[-1]

			# Jogs run at full precision, so these land within the solver's own
			# 1e-7 pose tolerance rather than within the fields' display rounding.
			app._jog_tool_translation(2, 1)
			self.assertEqual(app.jog_status_label.cget("text"), "Moved tool Z +1")
			moved_pose = forward_kinematics(app.parameters)[-1]
			for row in range(3):
				for column in range(3):
					self.assertAlmostEqual(moved_pose[row][column], start_pose[row][column], delta=1e-6)
				self.assertAlmostEqual(
					moved_pose[row][3] - start_pose[row][3], start_pose[row][2], delta=1e-6
				)

			before_rotation = forward_kinematics(app.parameters)[-1]
			app._jog_rotation_tool(0, 1)
			self.assertEqual(app.jog_status_label.cget("text"), "Rotated tool RX +5 deg")
			turned_pose = forward_kinematics(app.parameters)[-1]
			for actual, expected in zip(frame_origin(turned_pose), frame_origin(before_rotation)):
				self.assertAlmostEqual(actual, expected, delta=1e-6)
			expected_rotation = rotate_pose_tool_axis(before_rotation, 0, math.radians(5.0))
			for row in range(3):
				for column in range(3):
					self.assertAlmostEqual(
						turned_pose[row][column], expected_rotation[row][column], delta=1e-6
					)
		finally:
			app.root.destroy()

	def test_tk_editing_one_joint_keeps_the_other_angles_exact(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			app._jog_cartesian(1, 1)
			solved_angles = app.joint_angles_degrees
			displayed_angles = tuple(float(entry.get()) for entry in app.joint_angle_entries)
			self.assertNotEqual(
				displayed_angles, tuple(solved_angles),
				"the jog was expected to land on angles the fields cannot show exactly",
			)

			edited_entry = app.joint_angle_entries[5]
			edited_entry.delete(0, tk.END)
			edited_entry.insert(0, "-12.5")
			self.assertTrue(app._apply_from_entries())

			self.assertEqual(app.joint_angles_degrees[5], -12.5)
			for index in range(5):
				self.assertEqual(
					app.joint_angles_degrees[index], solved_angles[index],
					f"applying an edit to J6 changed J{index + 1}",
				)
		finally:
			app.root.destroy()

	def test_tk_jog_beyond_reach_is_refused_and_keeps_pose(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			for entry, value in zip(app.joint_angle_entries, (25.0, -35.0, 30.0, 40.0, -55.0, 15.0)):
				entry.delete(0, tk.END)
				entry.insert(0, str(value))
			self.assertTrue(app._apply_from_entries())
			before = forward_kinematics(app.parameters)[-1]
			app.jog_step_entry.delete(0, tk.END)
			app.jog_step_entry.insert(0, "1000")
			app._jog_cartesian(2, -1)
			after = forward_kinematics(app.parameters)[-1]
			self.assertIn("No exact-pose IK solution", app.jog_status_label.cget("text"))
			for before_row, after_row in zip(before, after):
				for before_value, after_value in zip(before_row, after_row):
					self.assertAlmostEqual(before_value, after_value, delta=1e-9)
		finally:
			app.root.destroy()

	def test_tk_jog_reports_unsupported_dh_table(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			alpha_entry = app.parameter_entries[2][3]
			alpha_entry.delete(0, tk.END)
			alpha_entry.insert(0, "45")
			before = forward_kinematics(app.parameters)[-1]
			app._jog_cartesian(0, 1)
			self.assertIn("joint 3 alpha", app.jog_status_label.cget("text"))
			for before_row, after_row in zip(before, forward_kinematics(app.parameters)[-1]):
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
			self.assertEqual(app.jog_status_label.cget("text"), "Rotated base RY +5 deg")
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

	def test_tk_coordinate_gizmo_visibility_is_independent_per_frame(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			# The saved configuration keeps whatever the user toggled last, so
			# assert that the frames are independent rather than that all start on.
			saved_visibility = tuple(variable.get() for variable in app.coordinate_gizmo_vars)
			self.assertEqual(len(saved_visibility), 7)
			self.assertTrue(app.show_joint_labels.get())
			self.assertEqual(len(app.axes.texts), 7)
			self.assertGreaterEqual(len(app.axes.lines), 20)
			app.coordinate_gizmo_vars[3].set(not saved_visibility[3])
			app._render_scene()
			self.assertEqual(len(app.axes.texts), 7)
			for index, variable in enumerate(app.coordinate_gizmo_vars):
				expected = not saved_visibility[3] if index == 3 else saved_visibility[index]
				self.assertEqual(variable.get(), expected)
			app.show_joint_labels.set(False)
			app._render_scene()
			self.assertEqual(len(app.axes.texts), 0)
		finally:
			app.root.destroy()

	def test_tk_view_starts_isometric_and_preserves_orbit_on_redraw(self) -> None:
		try:
			from simulator import RobotArmSimulator
			app = RobotArmSimulator()
		except tk.TclError as error:
			self.skipTest(f"Tk display unavailable: {error}")
		try:
			self.assertAlmostEqual(app.axes.elev, 35.264, delta=1e-3)
			self.assertAlmostEqual(app.axes.azim, -45.0, delta=1e-3)
			self.assertEqual(app.axes.name, "3d")
			app.axes.view_init(elev=22.0, azim=61.0)
			app._render_scene()
			self.assertAlmostEqual(app.axes.elev, 22.0, delta=1e-3)
			self.assertAlmostEqual(app.axes.azim, 61.0, delta=1e-3)
		finally:
			app.root.destroy()


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
			offset_pose_translation(start_pose, axis, direction * step)
			for axis in range(3)
			for direction in (-1, 1)
		] + [
			rotate_pose_world_axis(start_pose, axis, math.radians(5.0)) for axis in range(3)
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