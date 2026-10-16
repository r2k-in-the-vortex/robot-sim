"""Interactive 3D viewport for developing the robot-arm simulator."""

from __future__ import annotations

import json
import math
import tkinter as tk
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

import numpy as np
from matplotlib.axes import Axes
from matplotlib.backend_bases import MouseEvent
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.colors import to_rgba
from matplotlib.figure import Figure
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from stl import mesh as stl_mesh

from kinematics import (
	DHParameters,
	compose_dh_parameters,
	forward_kinematics,
	frame_origin,
	inverse_kinematics,
)

DEFAULT_DH_VALUES = (
	(0.0, 32.0, 10.0, 90.0),
	(90.0, 0.0, 25.0, 0.0),
	(0.0, 0.0, 0.0, 90.0),
	(0.0, 25.0, 0.0, 90.0),
	(0.0, 0.0, 0.0, -90.0),
	(0.0, 6.0, 0.0, 0.0),
)
MESH_FRAME_NAMES = ("Base", "J1", "J2", "J3", "J4", "J5", "J6")
# Standard DH: joint i rotates about Z of frame i - 1, so frames 0-5 are labeled
# as the joints whose axes they carry and frame 6 is the flange.
AXIS_FRAME_NAMES = ("J1", "J2", "J3", "J4", "J5", "J6", "Tool/Flange")
MESH_COLORS = ("#536d7a", "#d94a45", "#31845b", "#3978c5", "#d18b2c", "#7655a5", "#278b8b")


def _rotation_to_rpy_degrees(transform: tuple[tuple[float, ...], ...]) -> tuple[float, float, float]:
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


def offset_pose_translation(
	pose: tuple[tuple[float, ...], ...], axis: int, distance: float
) -> tuple[tuple[float, ...], ...]:
	"""Return a pose translated along one base-frame axis, preserving orientation."""
	if len(pose) != 4 or any(len(row) != 4 for row in pose):
		raise ValueError("pose must be a 4x4 homogeneous transform")
	if axis not in (0, 1, 2):
		raise ValueError("axis must be 0 (X), 1 (Y), or 2 (Z)")
	if not math.isfinite(distance):
		raise ValueError("translation distance must be finite")
	result = [list(row) for row in pose]
	result[axis][3] += distance
	return tuple(tuple(row) for row in result)


def offset_pose_tool_translation(
	pose: tuple[tuple[float, ...], ...], axis: int, distance: float
) -> tuple[tuple[float, ...], ...]:
	"""Return a pose translated along one of the tool frame's own axes.

	The tool axes are the columns of the pose's rotation block, so the offset
	runs along a column rather than along a base axis. Orientation is preserved.
	"""
	if len(pose) != 4 or any(len(row) != 4 for row in pose):
		raise ValueError("pose must be a 4x4 homogeneous transform")
	if axis not in (0, 1, 2):
		raise ValueError("axis must be 0 (X), 1 (Y), or 2 (Z)")
	if not math.isfinite(distance):
		raise ValueError("translation distance must be finite")
	result = [list(row) for row in pose]
	for row in range(3):
		result[row][3] += pose[row][axis] * distance
	return tuple(tuple(row) for row in result)


def _axis_rotation(axis: int, angle: float) -> tuple[tuple[float, ...], ...]:
	"""Return the rotation matrix about one coordinate axis."""
	cosine = math.cos(angle)
	sine = math.sin(angle)
	if axis == 0:
		return ((1.0, 0.0, 0.0), (0.0, cosine, -sine), (0.0, sine, cosine))
	if axis == 1:
		return ((cosine, 0.0, sine), (0.0, 1.0, 0.0), (-sine, 0.0, cosine))
	return ((cosine, -sine, 0.0), (sine, cosine, 0.0), (0.0, 0.0, 1.0))


def rotate_pose_world_axis(
	pose: tuple[tuple[float, ...], ...], axis: int, angle: float
) -> tuple[tuple[float, ...], ...]:
	"""Rotate a pose about a base-frame axis, keeping its origin fixed."""
	if len(pose) != 4 or any(len(row) != 4 for row in pose):
		raise ValueError("pose must be a 4x4 homogeneous transform")
	if axis not in (0, 1, 2):
		raise ValueError("axis must be 0 (X), 1 (Y), or 2 (Z)")
	if not math.isfinite(angle):
		raise ValueError("rotation angle must be finite")
	rotation = _axis_rotation(axis, angle)
	result = [list(row) for row in pose]
	for row in range(3):
		for column in range(3):
			result[row][column] = sum(rotation[row][index] * pose[index][column] for index in range(3))
	return tuple(tuple(row) for row in result)


def rotate_pose_tool_axis(
	pose: tuple[tuple[float, ...], ...], axis: int, angle: float
) -> tuple[tuple[float, ...], ...]:
	"""Rotate a pose about one of the tool frame's own axes, keeping its origin fixed.

	Post-multiplying turns the pose about the axes it already carries, which is
	what makes this the tool-frame counterpart of ``rotate_pose_world_axis``;
	that one pre-multiplies to turn about the base axes instead.
	"""
	if len(pose) != 4 or any(len(row) != 4 for row in pose):
		raise ValueError("pose must be a 4x4 homogeneous transform")
	if axis not in (0, 1, 2):
		raise ValueError("axis must be 0 (X), 1 (Y), or 2 (Z)")
	if not math.isfinite(angle):
		raise ValueError("rotation angle must be finite")
	rotation = _axis_rotation(axis, angle)
	result = [list(row) for row in pose]
	for row in range(3):
		for column in range(3):
			result[row][column] = sum(pose[row][index] * rotation[index][column] for index in range(3))
	return tuple(tuple(row) for row in result)


@dataclass(frozen=True)
class MeshSetting:
	path: str
	offset: tuple[float, float, float]
	rotation: tuple[float, float, float]
	opacity: float


@dataclass(frozen=True)
class MeshEntryWidgets:
	path: ttk.Entry
	offset: tuple[ttk.Entry, ttk.Entry, ttk.Entry]
	rotation: tuple[ttk.Entry, ttk.Entry, ttk.Entry]
	opacity: ttk.Spinbox


class RobotArmSimulator:
	"""Display a navigable robot scene and editable DH and STL parameters."""

	def __init__(self) -> None:
		self.root = tk.Tk()
		self.root.title("6-Axis Robot Simulator")
		self.root.geometry("1120x760")
		self.root.minsize(820, 600)
		self.config_path = Path(__file__).with_name("robot_parameters.json")
		self._drag_button: int | None = None
		self._last_mouse_position: tuple[float, float] | None = None
		self._camera_initialized = False
		self.parameters = self._to_dh_parameters(DEFAULT_DH_VALUES)
		# Runtime joint angles are held here at full precision; the entry fields and
		# front readouts only ever render them at display precision.
		self.joint_angles_degrees: tuple[float, ...] = (0.0,) * 6
		self.mesh_settings = self._default_mesh_settings()
		self.show_mesh_edges = tk.BooleanVar(master=self.root, value=False)
		self.show_joint_labels = tk.BooleanVar(master=self.root, value=True)
		self.coordinate_gizmo_vars = [tk.BooleanVar(master=self.root, value=True) for _ in MESH_FRAME_NAMES]

		self.notebook = ttk.Notebook(self.root)
		self.notebook.pack(fill=tk.BOTH, expand=True)
		self.view_tab = ttk.Frame(self.notebook, padding=8)
		self.parameters_tab = ttk.Frame(self.notebook, padding=8)
		self.notebook.add(self.view_tab, text="3D View")
		self.notebook.add(self.parameters_tab, text="Parameters")

		self.figure = Figure(figsize=(8, 6), facecolor="#f4f6f7")
		self.axes: Axes = self.figure.add_subplot(111, projection="3d")
		self.canvas = FigureCanvasTkAgg(self.figure, master=self.view_tab)
		self._build_jog_controls()
		pose_row = ttk.Frame(self.view_tab)
		pose_row.pack(fill=tk.X)
		self.pose_label = ttk.Label(pose_row, anchor=tk.W, padding=(4, 4))
		self.pose_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
		ttk.Button(pose_row, text="Copy XYZ", command=self._copy_t6_position).pack(
			side=tk.RIGHT, padx=(8, 4)
		)
		self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
		self.figure.subplots_adjust(left=0, right=1, bottom=0, top=1)

		self._build_parameter_tab()
		if self.config_path.exists():
			try:
				dh_values, mesh_settings, show_mesh_edges, gizmo_visibility, show_joint_labels = self._read_json_configuration()
				self._populate_dh_entries(dh_values)
				self._populate_mesh_entries(mesh_settings)
				self.show_mesh_edges.set(show_mesh_edges)
				for variable, visible in zip(self.coordinate_gizmo_vars, gizmo_visibility):
					variable.set(visible)
				self.show_joint_labels.set(show_joint_labels)
			except (OSError, ValueError, TypeError, KeyError) as error:
				messagebox.showerror("Parameter file error", str(error), parent=self.root)
		self.parameters = self._read_entry_parameters()
		self.mesh_settings = self._read_mesh_entries()
		self._render_scene()
		self.axes.mouse_init(rotate_btn=[], pan_btn=[], zoom_btn=[])
		self.canvas.mpl_connect("button_press_event", self._on_mouse_press)
		self.canvas.mpl_connect("button_release_event", self._on_mouse_release)
		self.canvas.mpl_connect("motion_notify_event", self._on_mouse_move)
		canvas_widget = self.canvas.get_tk_widget()
		canvas_widget.bind("<MouseWheel>", self._on_tk_mousewheel)
		canvas_widget.bind("<Button-4>", self._on_tk_mousewheel)
		canvas_widget.bind("<Button-5>", self._on_tk_mousewheel)

	def _build_jog_controls(self) -> None:
		controls = ttk.Frame(self.view_tab, padding=(4, 1))
		controls.pack(fill=tk.X)
		steps = ttk.Frame(controls)
		steps.grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 4))
		ttk.Label(steps, text="Jog step").grid(row=0, column=0, sticky=tk.W)
		self.jog_step_entry = ttk.Spinbox(steps, from_=0.001, to=1_000_000.0, increment=0.01, width=6)
		self.jog_step_entry.insert(0, "1")
		self.jog_step_entry.grid(row=0, column=1, padx=(4, 16))
		ttk.Label(steps, text="Rotation step").grid(row=0, column=2, sticky=tk.W)
		self.rotation_step_entry = ttk.Spinbox(steps, from_=0.1, to=360.0, increment=1.0, width=6)
		self.rotation_step_entry.insert(0, "5")
		self.rotation_step_entry.grid(row=0, column=3, padx=(4, 0))

		frame_groups = (
			("Base frame", self._jog_cartesian, self._jog_rotation_world),
			("Tool frame", self._jog_tool_translation, self._jog_rotation_tool),
		)
		for column, (title, translate, rotate) in enumerate(frame_groups):
			group = ttk.LabelFrame(controls, text=title, padding=(8, 4))
			group.grid(row=1, column=column, sticky=tk.NW, padx=(0, 8))
			self._build_frame_jog_buttons(group, translate, rotate)

		joints = ttk.LabelFrame(controls, text="Joint jogs", padding=(8, 4))
		joints.grid(row=2, column=0, columnspan=len(frame_groups), sticky=tk.EW, pady=(6, 0))
		ttk.Label(joints, text="Joint step").grid(row=0, column=0, sticky=tk.W)
		self.joint_step_entry = ttk.Spinbox(joints, from_=0.1, to=360.0, increment=1.0, width=6)
		self.joint_step_entry.insert(0, "5")
		self.joint_step_entry.grid(row=0, column=1, padx=(4, 16))
		self.front_joint_angle_vars: list[tk.StringVar] = []
		for joint_index in range(6):
			column = 2 + joint_index * 3
			ttk.Label(joints, text=f"J{joint_index + 1}").grid(row=0, column=column)
			ttk.Button(
				joints, text="-", width=1,
				command=lambda index=joint_index: self._jog_joint(index, -1),
			).grid(row=0, column=column + 1, padx=1)
			angle_var = tk.StringVar(master=self.root, value="0.0°")
			self.front_joint_angle_vars.append(angle_var)
			ttk.Button(
				joints, text="+", width=1,
				command=lambda index=joint_index: self._jog_joint(index, 1),
			).grid(row=0, column=column + 2, padx=1)
			ttk.Label(joints, textvariable=angle_var, width=6, anchor=tk.CENTER).grid(
				row=1, column=column, columnspan=3
			)
		self.jog_status_label = ttk.Label(self.view_tab, anchor=tk.W, padding=(4, 1))
		self.jog_status_label.pack(fill=tk.X)

	def _build_frame_jog_buttons(
		self,
		group: ttk.LabelFrame,
		translate: Callable[[int, int], None],
		rotate: Callable[[int, int], None],
	) -> None:
		"""Fill one frame group with its translation and rotation jog buttons."""
		for axis, name in enumerate(("X", "Y", "Z")):
			for direction, suffix in ((-1, "-"), (1, "+")):
				column = axis * 2 + (1 if direction > 0 else 0)
				ttk.Button(
					group, text=f"{name}{suffix}", width=3,
					command=lambda axis=axis, direction=direction: translate(axis, direction),
				).grid(row=0, column=column, padx=1, pady=1)
				ttk.Button(
					group, text=f"R{name}{suffix}", width=4,
					command=lambda axis=axis, direction=direction: rotate(axis, direction),
				).grid(row=1, column=column, padx=1, pady=1)

	def _copy_t6_position(self) -> None:
		transform = forward_kinematics(self.parameters)[-1]
		tool_position = frame_origin(transform)
		roll, pitch, yaw = _rotation_to_rpy_degrees(transform)
		joint_angles = self.joint_angles_degrees
		clipboard_text = "\n".join((
			"T6 position (model units):",
			f"X: {tool_position[0]:.15g}",
			f"Y: {tool_position[1]:.15g}",
			f"Z: {tool_position[2]:.15g}",
			"T6 orientation (RPY, ZYX, degrees):",
			f"Roll: {roll:.15g}",
			f"Pitch: {pitch:.15g}",
			f"Yaw: {yaw:.15g}",
			"Runtime joint angles (degrees):",
			*(f"J{index}: {angle:.15g}" for index, angle in enumerate(joint_angles, start=1)),
		))
		self.root.clipboard_clear()
		self.root.clipboard_append(clipboard_text)
		self.jog_status_label.configure(text="Copied T6 pose and joint angles")

	def _sync_joint_angle_views(self, joint_angles_degrees: tuple[float, ...]) -> None:
		"""Render joint angles into the entry fields and front readouts."""
		for entry, angle, display_var in zip(
			self.joint_angle_entries, joint_angles_degrees, self.front_joint_angle_vars
		):
			entry.delete(0, tk.END)
			entry.insert(0, self._format_value(angle))
			display_var.set(f"{angle:.1f}°")

	def _jog_joint(self, joint_index: int, direction: int) -> None:
		try:
			static_values = self._read_entry_values()
			joint_angles = list(self.joint_angles_degrees)
			step = self._read_step(self.joint_step_entry, "Joint step must be a finite positive angle.")
		except ValueError as error:
			self.jog_status_label.configure(text=str(error))
			return
		joint_angles[joint_index] += direction * step
		updated_angles = tuple(joint_angles)
		self.joint_angles_degrees = updated_angles
		self._sync_joint_angle_views(updated_angles)
		self.parameters = self._to_dh_parameters(static_values, updated_angles)
		self._render_scene()
		self.jog_status_label.configure(text=f"Jogged J{joint_index + 1} {direction * step:+g} deg")

	def _apply_joint_solution(
		self,
		static_values: tuple[tuple[float, float, float, float], ...],
		joint_angles_radians: tuple[float, ...],
	) -> None:
		"""Store a solved pose at full precision and refresh the views from it."""
		joint_angles_degrees = tuple(math.degrees(angle) for angle in joint_angles_radians)
		self.joint_angles_degrees = joint_angles_degrees
		self._sync_joint_angle_views(joint_angles_degrees)
		self.parameters = self._to_dh_parameters(static_values, joint_angles_degrees)
		self._render_scene()

	def _read_step(self, entry: ttk.Spinbox, message: str) -> float:
		"""Return a step entry's value, rejecting anything but a positive number."""
		step = float(entry.get())
		if not math.isfinite(step) or step <= 0:
			raise ValueError(message)
		return step

	def _pose_jog(
		self,
		step_entry: ttk.Spinbox,
		step_error: str,
		target_builder: Callable[[tuple[tuple[float, ...], ...], float], tuple[tuple[float, ...], ...]],
		describe: Callable[[float], str],
	) -> None:
		"""Solve one Cartesian jog and move to the branch nearest the current pose.

		``target_builder(pose, step)`` returns the requested pose for that step and
		``describe(step)`` the status text to show once it is reached. Reading the
		DH table or the step, and the solve itself, all report through the status
		label instead of raising into Tk's handler.
		"""
		try:
			static_values = self._read_entry_values()
			joint_angles_degrees = self.joint_angles_degrees
			step = self._read_step(step_entry, step_error)
			geometry = self._to_dh_parameters(static_values)
			current_pose = forward_kinematics(
				self._to_dh_parameters(static_values, joint_angles_degrees)
			)[-1]
			solutions = inverse_kinematics(target_builder(current_pose, step), geometry)
		except ValueError as error:
			self.jog_status_label.configure(text=str(error))
			return
		if not solutions:
			self.jog_status_label.configure(text="No exact-pose IK solution; robot was not moved.")
			return
		current_angles = tuple(math.radians(angle) for angle in joint_angles_degrees)
		new_angles = min(solutions, key=lambda solution: sum(
			math.atan2(math.sin(candidate - current), math.cos(candidate - current)) ** 2
			for candidate, current in zip(solution.angles, current_angles)
		)).angles
		self._apply_joint_solution(static_values, new_angles)
		self.jog_status_label.configure(text=describe(step))

	def _jog_cartesian(self, axis: int, direction: int) -> None:
		"""Offset T6 along a base-frame axis, keeping its orientation."""
		self._pose_jog(
			self.jog_step_entry,
			"Jog step must be a finite positive length.",
			lambda pose, step: offset_pose_translation(pose, axis, direction * step),
			lambda step: f"Moved base {'XYZ'[axis]} {direction * step:+g}",
		)

	def _jog_tool_translation(self, axis: int, direction: int) -> None:
		"""Offset T6 along one of the tool frame's own axes, keeping its orientation."""
		self._pose_jog(
			self.jog_step_entry,
			"Jog step must be a finite positive length.",
			lambda pose, step: offset_pose_tool_translation(pose, axis, direction * step),
			lambda step: f"Moved tool {'XYZ'[axis]} {direction * step:+g}",
		)

	def _jog_rotation_world(self, axis: int, direction: int) -> None:
		"""Turn T6 about a base-frame axis, keeping its origin fixed."""
		self._pose_jog(
			self.rotation_step_entry,
			"Rotation step must be a finite positive angle.",
			lambda pose, step: rotate_pose_world_axis(pose, axis, math.radians(direction * step)),
			lambda step: f"Rotated base R{'XYZ'[axis]} {direction * step:+g} deg",
		)

	def _jog_rotation_tool(self, axis: int, direction: int) -> None:
		"""Turn T6 about one of the tool frame's own axes, keeping its origin fixed."""
		self._pose_jog(
			self.rotation_step_entry,
			"Rotation step must be a finite positive angle.",
			lambda pose, step: rotate_pose_tool_axis(pose, axis, math.radians(direction * step)),
			lambda step: f"Rotated tool R{'XYZ'[axis]} {direction * step:+g} deg",
		)

	def _build_parameter_tab(self) -> None:
		self.parameter_notebook = ttk.Notebook(self.parameters_tab)
		self.parameter_notebook.pack(fill=tk.BOTH, expand=True)
		self.dh_tab = ttk.Frame(self.parameter_notebook, padding=16)
		self.mesh_tab = ttk.Frame(self.parameter_notebook, padding=16)
		self.parameter_notebook.add(self.dh_tab, text="DH Parameters")
		self.parameter_notebook.add(self.mesh_tab, text="Meshes")

		ttk.Label(
			self.dh_tab,
			text="Denavit–Hartenberg parameters",
			font=("Segoe UI", 16, "bold"),
		).grid(row=0, column=0, columnspan=6, sticky=tk.W, pady=(0, 6))
		tk.Label(
			self.dh_tab,
			text="Theta offset and joint angle are in degrees; d and a use consistent length units.",
		).grid(row=1, column=0, columnspan=6, sticky=tk.W, pady=(0, 18))

		for column, heading in enumerate((
			"Joint", "Theta offset (deg)", "Joint angle (deg)", "d", "a", "Alpha (deg)"
		)):
			ttk.Label(self.dh_tab, text=heading, font=("Segoe UI", 10, "bold")).grid(
				row=2, column=column, sticky=tk.W, padx=(0, 12), pady=(0, 8)
			)

		self.parameter_entries: list[tuple[ttk.Entry, ...]] = []
		self.joint_angle_entries: list[ttk.Spinbox] = []
		for joint_index, values in enumerate(DEFAULT_DH_VALUES, start=1):
			ttk.Label(self.dh_tab, text=f"J{joint_index}").grid(
				row=joint_index + 2, column=0, sticky=tk.W, padx=(0, 12), pady=4
			)
			angle_entry = ttk.Spinbox(self.dh_tab, from_=-360.0, to=360.0, increment=1.0, width=16)
			angle_entry.insert(0, "0")
			angle_entry.grid(row=joint_index + 2, column=2, sticky=tk.W, padx=(0, 12), pady=4)
			self.joint_angle_entries.append(angle_entry)
			entries = []
			for column, value in zip((1, 3, 4, 5), values):
				entry = ttk.Entry(self.dh_tab, width=16)
				entry.grid(row=joint_index + 2, column=column, sticky=tk.W, padx=(0, 12), pady=4)
				entry.insert(0, self._format_value(value))
				entries.append(entry)
			self.parameter_entries.append(tuple(entries))

		button_row = ttk.Frame(self.dh_tab)
		button_row.grid(row=10, column=0, columnspan=6, sticky=tk.W, pady=(18, 8))
		ttk.Button(button_row, text="Apply to View", command=self._apply_from_entries).pack(
			side=tk.LEFT, padx=(0, 8)
		)
		ttk.Button(button_row, text="Save JSON", command=self._save_json).pack(
			side=tk.LEFT, padx=(0, 8)
		)
		ttk.Button(button_row, text="Load JSON", command=self._load_json).pack(side=tk.LEFT)
		ttk.Label(self.dh_tab, text=f"File: {self.config_path.name} · Joint angles start at zero and are not saved.").grid(
			row=11, column=0, columnspan=6, sticky=tk.W, pady=(4, 0)
		)
		ttk.Checkbutton(
			self.dh_tab,
			text="Show joint labels in 3D View",
			variable=self.show_joint_labels,
			command=self._render_scene,
		).grid(row=12, column=0, columnspan=6, sticky=tk.W, pady=(10, 2))
		ttk.Label(self.dh_tab, text="Coordinate gizmos").grid(
			row=13, column=0, sticky=tk.W, pady=(4, 2)
		)
		gizmo_controls = ttk.Frame(self.dh_tab)
		gizmo_controls.grid(row=14, column=0, columnspan=6, sticky=tk.W)
		for index, (frame_name, variable) in enumerate(zip(AXIS_FRAME_NAMES, self.coordinate_gizmo_vars)):
			ttk.Checkbutton(
				gizmo_controls,
				text=frame_name,
				variable=variable,
				command=self._render_scene,
			).grid(row=0, column=index, sticky=tk.W, padx=(0, 8))
		self._build_mesh_tab()

	def _build_mesh_tab(self) -> None:
		ttk.Label(
			self.mesh_tab,
			text="Frame-attached STL meshes",
			font=("Segoe UI", 16, "bold"),
		).grid(row=0, column=0, columnspan=7, sticky=tk.W, pady=(0, 6))
		ttk.Label(
			self.mesh_tab,
			text="Offsets use model length units. Rotations are local X, then Y, then Z, in degrees.",
		).grid(row=1, column=0, columnspan=10, sticky=tk.W, pady=(0, 14))
		ttk.Checkbutton(
			self.mesh_tab,
			text="Show triangle edges",
			variable=self.show_mesh_edges,
			command=self._render_scene,
		).grid(row=2, column=0, columnspan=10, sticky=tk.W, pady=(0, 8))

		headings = (
			"Frame", "STL file", "", "Offset X", "Offset Y", "Offset Z",
			"Rot X", "Rot Y", "Rot Z", "Opacity",
		)
		for column, heading in enumerate(headings):
			ttk.Label(self.mesh_tab, text=heading, font=("Segoe UI", 9, "bold")).grid(
				row=3, column=column, sticky=tk.W, padx=(0, 5), pady=(0, 6)
			)

		self.mesh_entries: list[MeshEntryWidgets] = []
		for row_index, frame_name in enumerate(MESH_FRAME_NAMES, start=4):
			ttk.Label(self.mesh_tab, text=frame_name).grid(
				row=row_index, column=0, sticky=tk.W, padx=(0, 8), pady=4
			)
			path_entry = ttk.Entry(self.mesh_tab, width=24)
			path_entry.grid(row=row_index, column=1, sticky=tk.EW, padx=(0, 6), pady=4)
			ttk.Button(
				self.mesh_tab,
				text="Browse...",
				command=lambda entry=path_entry: self._browse_stl(entry),
			).grid(row=row_index, column=2, padx=(0, 8), pady=4)
			offset_entries = []
			for column in range(3, 6):
				entry = ttk.Entry(self.mesh_tab, width=7)
				entry.insert(0, "0")
				entry.grid(row=row_index, column=column, sticky=tk.W, padx=(0, 8), pady=4)
				offset_entries.append(entry)
			rotation_entries = []
			for column in range(6, 9):
				entry = ttk.Entry(self.mesh_tab, width=7)
				entry.insert(0, "0")
				entry.grid(row=row_index, column=column, sticky=tk.W, padx=(0, 8), pady=4)
				rotation_entries.append(entry)
			opacity_entry = ttk.Spinbox(self.mesh_tab, from_=0.0, to=1.0, increment=0.05, width=6)
			opacity_entry.insert(0, "1")
			opacity_entry.grid(row=row_index, column=9, sticky=tk.W, pady=4)
			self.mesh_entries.append(
				MeshEntryWidgets(path_entry, tuple(offset_entries), tuple(rotation_entries), opacity_entry)
			)
		self.mesh_tab.columnconfigure(1, weight=1)
		self.mesh_status = ttk.Label(self.mesh_tab, text="No meshes configured.")
		self.mesh_status.grid(row=11, column=0, columnspan=10, sticky=tk.W, pady=(10, 2))
		ttk.Button(self.mesh_tab, text="Apply Meshes", command=self._apply_from_entries).grid(
			row=12, column=0, sticky=tk.W, padx=(0, 8), pady=(10, 0)
		)
		ttk.Button(self.mesh_tab, text="Save JSON", command=self._save_json).grid(
			row=12, column=1, sticky=tk.W, pady=(10, 0)
		)

	@staticmethod
	def _default_mesh_settings() -> tuple[MeshSetting, ...]:
		return tuple(MeshSetting("", (0.0, 0.0, 0.0), (0.0, 0.0, 0.0), 1.0) for _ in MESH_FRAME_NAMES)

	def _browse_stl(self, entry: ttk.Entry) -> None:
		selected_path = filedialog.askopenfilename(
			parent=self.root,
			title="Select STL mesh",
			filetypes=(("STL mesh", "*.stl"), ("All files", "*.*")),
		)
		if selected_path:
			entry.delete(0, tk.END)
			entry.insert(0, selected_path)

	@staticmethod
	def _format_value(value: float) -> str:
		return f"{value:g}"

	@staticmethod
	def _to_dh_parameters(
		values: tuple[tuple[float, float, float, float], ...],
		joint_angles_degrees: tuple[float, ...] | None = None,
	) -> tuple[DHParameters, ...]:
		return compose_dh_parameters(values, joint_angles_degrees)

	def _read_entry_values(self) -> tuple[tuple[float, float, float, float], ...]:
		rows = tuple(tuple(float(entry.get()) for entry in row) for row in self.parameter_entries)
		if len(rows) != 6 or any(len(row) != 4 for row in rows):
			raise ValueError("Exactly six joints with four DH values each are required.")
		if not all(math.isfinite(value) for row in rows for value in row):
			raise ValueError("All DH values must be finite numbers.")
		return rows

	def _read_entry_parameters(self) -> tuple[DHParameters, ...]:
		return self._to_dh_parameters(self._read_entry_values(), self._read_joint_angle_values())

	def _read_joint_angle_values(self) -> tuple[float, ...]:
		"""Return the runtime joint angles the entry fields ask for.

		A field still showing the rendering of the current angle yields that angle
		at full precision, so applying an edit to one joint does not round the
		others down to display precision. A field the user retyped is taken at
		face value.
		"""
		if len(self.joint_angle_entries) != 6 or len(self.joint_angles_degrees) != 6:
			raise ValueError("Exactly six runtime joint angles are required.")
		joint_angles = tuple(
			current if entry.get() == self._format_value(current) else float(entry.get())
			for entry, current in zip(self.joint_angle_entries, self.joint_angles_degrees)
		)
		if not all(math.isfinite(value) for value in joint_angles):
			raise ValueError("All runtime joint angles must be finite numbers.")
		return joint_angles

	def _read_mesh_entries(self) -> tuple[MeshSetting, ...]:
		settings = []
		for widgets in self.mesh_entries:
			offset = tuple(float(entry.get()) for entry in widgets.offset)
			rotation = tuple(float(entry.get()) for entry in widgets.rotation)
			opacity = float(widgets.opacity.get())
			if not all(math.isfinite(value) for value in (*offset, *rotation, opacity)):
				raise ValueError("Mesh offsets, rotations, and opacity must be finite numbers.")
			if not 0.0 <= opacity <= 1.0:
				raise ValueError("Mesh opacity must be from 0 to 1.")
			mesh_path = widgets.path.get().strip()
			if mesh_path and Path(mesh_path).suffix.lower() != ".stl":
				raise ValueError(f"Mesh path must point to an STL file: {mesh_path}")
			settings.append(MeshSetting(mesh_path, offset, rotation, opacity))
		return tuple(settings)

	def _populate_dh_entries(self, values: tuple[tuple[float, float, float, float], ...]) -> None:
		for row_entries, row_values in zip(self.parameter_entries, values):
			for entry, value in zip(row_entries, row_values):
				entry.delete(0, tk.END)
				entry.insert(0, self._format_value(value))

	def _populate_mesh_entries(self, settings: tuple[MeshSetting, ...]) -> None:
		for widgets, setting in zip(self.mesh_entries, settings):
			widgets.path.delete(0, tk.END)
			widgets.path.insert(0, setting.path)
			for entry, value in zip(widgets.offset, setting.offset):
				entry.delete(0, tk.END)
				entry.insert(0, self._format_value(value))
			for entry, value in zip(widgets.rotation, setting.rotation):
				entry.delete(0, tk.END)
				entry.insert(0, self._format_value(value))
			widgets.opacity.delete(0, tk.END)
			widgets.opacity.insert(0, self._format_value(setting.opacity))

	def _apply_from_entries(self) -> bool:
		try:
			joint_angles = self._read_joint_angle_values()
			parameters = self._to_dh_parameters(self._read_entry_values(), joint_angles)
			mesh_settings = self._read_mesh_entries()
		except ValueError as error:
			messagebox.showerror("Invalid parameters", str(error), parent=self.root)
			return False
		self.joint_angles_degrees = joint_angles
		self.parameters = parameters
		self.mesh_settings = mesh_settings
		self._sync_joint_angle_views(joint_angles)
		self._render_scene()
		return True

	def _save_json(self) -> None:
		try:
			values = self._read_entry_values()
			mesh_settings = self._read_mesh_entries()
		except ValueError as error:
			messagebox.showerror("Invalid parameters", str(error), parent=self.root)
			return

		data = {
			"schema_version": 1,
			"units": {"angles": "degrees", "lengths": "model_units"},
			"show_mesh_edges": self.show_mesh_edges.get(),
			"show_coordinate_gizmos": [variable.get() for variable in self.coordinate_gizmo_vars],
			"show_joint_labels": self.show_joint_labels.get(),
			"joints": [
				{"theta_offset_deg": theta, "d": d, "a": a, "alpha_deg": alpha}
				for theta, d, a, alpha in values
			],
			"meshes": [self._serialize_mesh_setting(setting) for setting in mesh_settings],
		}
		try:
			self.config_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
		except OSError as error:
			messagebox.showerror("Could not save parameters", str(error), parent=self.root)
			return
		joint_angles = self.joint_angles_degrees
		self.parameters = self._to_dh_parameters(values, joint_angles)
		self._sync_joint_angle_views(joint_angles)
		self.mesh_settings = mesh_settings
		self._render_scene()
		messagebox.showinfo("Parameters saved", f"Saved to {self.config_path.name}.", parent=self.root)

	def _serialize_mesh_setting(self, setting: MeshSetting) -> dict[str, object]:
		path = setting.path
		if path:
			mesh_path = Path(path).expanduser().resolve()
			try:
				path = mesh_path.relative_to(self.config_path.parent.resolve()).as_posix()
			except ValueError:
				path = str(mesh_path)
		return {
			"path": path,
			"offset": list(setting.offset),
			"rotation_deg": list(setting.rotation),
			"opacity": setting.opacity,
		}

	def _read_json_configuration(
		self,
	) -> tuple[
		tuple[tuple[float, float, float, float], ...],
		tuple[MeshSetting, ...],
		bool,
		tuple[bool, ...],
		bool,
	]:
		data = json.loads(self.config_path.read_text(encoding="utf-8"))
		if not isinstance(data, dict):
			raise ValueError("Parameter file must contain a JSON object.")
		if data.get("schema_version") != 1:
			raise ValueError("Unsupported parameter file schema version.")
		units = data.get("units")
		if not isinstance(units, dict) or units.get("angles") != "degrees":
			raise ValueError("Parameter file angles must use degrees.")
		joints = data.get("joints")
		if not isinstance(joints, list) or len(joints) != 6:
			raise ValueError("Parameter file must contain exactly six joints.")
		dh_values = tuple(
			(
				float(joint.get("theta_offset_deg", joint.get("theta_deg"))),
				float(joint["d"]),
				float(joint["a"]),
				float(joint["alpha_deg"]),
			)
			for joint in joints
		)
		if not all(math.isfinite(value) for row in dh_values for value in row):
			raise ValueError("DH parameter values must all be finite numbers.")

		mesh_data = data.get("meshes")
		show_mesh_edges = data.get("show_mesh_edges", False)
		if not isinstance(show_mesh_edges, bool):
			raise ValueError("show_mesh_edges must be true or false.")
		gizmo_visibility = data.get("show_coordinate_gizmos", [True] * len(MESH_FRAME_NAMES))
		if (
			not isinstance(gizmo_visibility, list)
			or len(gizmo_visibility) != len(MESH_FRAME_NAMES)
			or not all(isinstance(visible, bool) for visible in gizmo_visibility)
		):
			raise ValueError("show_coordinate_gizmos must contain seven true/false values.")
		gizmo_visibility = tuple(gizmo_visibility)
		show_joint_labels = data.get("show_joint_labels", True)
		if not isinstance(show_joint_labels, bool):
			raise ValueError("show_joint_labels must be true or false.")
		if mesh_data is None:
			return dh_values, self._default_mesh_settings(), show_mesh_edges, gizmo_visibility, show_joint_labels
		if not isinstance(mesh_data, list) or len(mesh_data) != len(MESH_FRAME_NAMES):
			raise ValueError("Parameter file must contain seven mesh settings: base and joints 1-6.")
		mesh_settings = []
		for mesh_setting in mesh_data:
			if not isinstance(mesh_setting, dict):
				raise ValueError("Each mesh setting must be a JSON object.")
			path = mesh_setting.get("path", "")
			if not isinstance(path, str):
				raise ValueError("Mesh paths must be strings.")
			offset = mesh_setting.get("offset", (0.0, 0.0, 0.0))
			if not isinstance(offset, list | tuple) or len(offset) != 3:
				raise ValueError("Each mesh offset must contain exactly three values.")
			offset_values = tuple(float(value) for value in offset)
			rotation = mesh_setting.get("rotation_deg", (0.0, 0.0, 0.0))
			if not isinstance(rotation, list | tuple) or len(rotation) != 3:
				raise ValueError("Each mesh rotation must contain exactly three values.")
			rotation_values = tuple(float(value) for value in rotation)
			opacity = float(mesh_setting.get("opacity", 1.0))
			if not all(math.isfinite(value) for value in (*offset_values, *rotation_values, opacity)):
				raise ValueError("Mesh offsets, rotations, and opacity must be finite numbers.")
			if not 0.0 <= opacity <= 1.0:
				raise ValueError("Mesh opacity must be from 0 to 1.")
			if path:
				mesh_path = Path(path).expanduser()
				if not mesh_path.is_absolute():
					mesh_path = self.config_path.parent / mesh_path
				path = str(mesh_path.resolve())
			mesh_settings.append(MeshSetting(path, offset_values, rotation_values, opacity))
		return dh_values, tuple(mesh_settings), show_mesh_edges, gizmo_visibility, show_joint_labels

	def _read_json_parameters(self) -> tuple[tuple[float, float, float, float], ...]:
		return self._read_json_configuration()[0]

	def _load_json(self) -> None:
		try:
			values, mesh_settings, show_mesh_edges, gizmo_visibility, show_joint_labels = self._read_json_configuration()
		except (OSError, ValueError, TypeError, KeyError) as error:
			messagebox.showerror("Could not load parameters", str(error), parent=self.root)
			return
		self._populate_dh_entries(values)
		self._populate_mesh_entries(mesh_settings)
		joint_angles = self.joint_angles_degrees
		self.parameters = self._to_dh_parameters(values, joint_angles)
		self._sync_joint_angle_views(joint_angles)
		self.mesh_settings = mesh_settings
		self.show_mesh_edges.set(show_mesh_edges)
		for variable, visible in zip(self.coordinate_gizmo_vars, gizmo_visibility):
			variable.set(visible)
		self.show_joint_labels.set(show_joint_labels)
		self._render_scene()

	def _draw_xy_background_grid(
		self,
		x_min: float,
		x_max: float,
		y_min: float,
		y_max: float,
		radius: float,
	) -> None:
		"""Draw a subdued, scale-adaptive XY reference grid on the Z=0 plane."""
		raw_spacing = max(radius / 5.0, 1e-9)
		magnitude = 10.0 ** math.floor(math.log10(raw_spacing))
		spacing = next(
			(multiplier * magnitude for multiplier in (1.0, 2.0, 5.0, 10.0)
			 if multiplier * magnitude >= raw_spacing),
			10.0 * magnitude,
		)
		first_x = math.ceil(x_min / spacing) * spacing
		last_x = math.floor(x_max / spacing) * spacing
		first_y = math.ceil(y_min / spacing) * spacing
		last_y = math.floor(y_max / spacing) * spacing
		for x_value in np.arange(first_x, last_x + spacing * 0.5, spacing):
			self.axes.plot(
				[x_value, x_value], [y_min, y_max], [0.0, 0.0],
				color="#cbd5da", linewidth=0.55, alpha=0.65,
			)
		for y_value in np.arange(first_y, last_y + spacing * 0.5, spacing):
			self.axes.plot(
				[x_min, x_max], [y_value, y_value], [0.0, 0.0],
				color="#cbd5da", linewidth=0.55, alpha=0.65,
			)

	def _render_scene(self) -> None:
		if self._camera_initialized:
			camera_elevation = self.axes.elev
			camera_azimuth = self.axes.azim
		else:
			camera_elevation = 35.264
			camera_azimuth = -45.0
		transforms = forward_kinematics(self.parameters)
		frame_origins = ((0.0, 0.0, 0.0),) + tuple(frame_origin(transform) for transform in transforms)
		frame_transforms = (None,) + transforms
		self.axes.clear()
		self.axes.set_proj_type("ortho")
		self.axes.view_init(elev=camera_elevation, azim=camera_azimuth)
		self._camera_initialized = True
		self.axes.set_facecolor("#f4f6f7")
		self.axes.set_axis_off()
		self.axes.set_box_aspect((1, 1, 1))
		mesh_errors = []
		mesh_vertices = []
		for frame_index, (setting, origin, transform) in enumerate(
			zip(self.mesh_settings, frame_origins, frame_transforms)
		):
			if not setting.path or setting.opacity == 0.0:
				continue
			try:
				triangles = stl_mesh.Mesh.from_file(setting.path).vectors.astype(float)
				if triangles.size == 0:
					mesh_errors.append(f"{MESH_FRAME_NAMES[frame_index]}: STL contains no vertices")
					continue
				local_rotation = np.asarray(self._rotation_matrix(setting.rotation))
				frame_rotation = np.eye(3) if transform is None else np.asarray(
					[[transform[row][column] for column in range(3)] for row in range(3)]
				)
				rotated_local = triangles @ local_rotation.T + np.asarray(setting.offset)
				placed_triangles = rotated_local @ frame_rotation.T + np.asarray(origin)
				mesh_vertices.append(placed_triangles.reshape(-1, 3))
				face_colors = self._two_sided_face_colors(
					placed_triangles, MESH_COLORS[frame_index], setting.opacity
				)
				collection = Poly3DCollection(
					placed_triangles,
					facecolors=face_colors,
					edgecolors="#25343b" if self.show_mesh_edges.get() else "none",
					linewidths=0.25 if self.show_mesh_edges.get() else 0,
				)
				collection.set_alpha(setting.opacity)
				self.axes.add_collection3d(collection)
			except (OSError, RuntimeError, ValueError) as error:
				mesh_errors.append(f"{MESH_FRAME_NAMES[frame_index]}: {error}")

		minimums = tuple(min(point[axis] for point in frame_origins) for axis in range(3))
		maximums = tuple(max(point[axis] for point in frame_origins) for axis in range(3))
		if mesh_vertices:
			all_vertices = np.concatenate(mesh_vertices)
			minimums = tuple(min(minimums[axis], float(all_vertices[:, axis].min())) for axis in range(3))
			maximums = tuple(max(maximums[axis], float(all_vertices[:, axis].max())) for axis in range(3))
		center = tuple((minimums[axis] + maximums[axis]) / 2 for axis in range(3))
		radius = max(max(maximums[axis] - minimums[axis] for axis in range(3)) / 2, 0.5)
		half_span = radius * 1.45
		self.axes.set_xlim(center[0] - half_span, center[0] + half_span)
		self.axes.set_ylim(center[1] - half_span, center[1] + half_span)
		self.axes.set_zlim(center[2] - half_span, center[2] + half_span)
		self._draw_xy_background_grid(
			center[0] - half_span,
			center[0] + half_span,
			center[1] - half_span,
			center[1] + half_span,
			radius,
		)
		self.axes.plot(
			[point[0] for point in frame_origins],
			[point[1] for point in frame_origins],
			[point[2] for point in frame_origins],
			color="#5c6872",
			linewidth=2,
		)
		self.axes.scatter(*zip(*frame_origins), color="#202a33", s=20, depthshade=False)
		axis_colors = ("#d94a45", "#31845b", "#3978c5")
		marker_length = radius * 0.14
		for frame_index, (origin, transform) in enumerate(zip(frame_origins, frame_transforms)):
			if not self.coordinate_gizmo_vars[frame_index].get():
				continue
			rotation = (
				((1.0, 0.0, 0.0), (0.0, 1.0, 0.0), (0.0, 0.0, 1.0))
				if transform is None
				else tuple(tuple(transform[row][column] for row in range(3)) for column in range(3))
			)
			for direction, color in zip(rotation, axis_colors):
				self.axes.quiver(
					*origin,
					*(component * marker_length for component in direction),
					color=color,
					linewidth=1.5,
					arrow_length_ratio=0.24,
				)
		if self.show_joint_labels.get():
			for frame_index, origin in enumerate(frame_origins):
				self.axes.text(
					origin[0], origin[1], origin[2] + marker_length * 0.2,
					AXIS_FRAME_NAMES[frame_index],
					color="#26323b", fontsize=8,
				)

		if mesh_errors:
			self.mesh_status.configure(text="Mesh load issue: " + "; ".join(mesh_errors))
		else:
			loaded_count = sum(bool(setting.path) and setting.opacity > 0 for setting in self.mesh_settings)
			self.mesh_status.configure(text=f"{loaded_count} mesh(es) configured.")
		self.canvas.draw_idle()
		tool_transform = transforms[-1]
		tool_position = frame_origin(tool_transform)
		roll, pitch, yaw = _rotation_to_rpy_degrees(tool_transform)
		self.pose_label.configure(
			text=(
				f"T6 position: X {tool_position[0]:.3f}   Y {tool_position[1]:.3f}   "
				f"Z {tool_position[2]:.3f}\n"
				f"Orientation RPY (ZYX, deg): roll {roll:.1f}   pitch {pitch:.1f}   yaw {yaw:.1f}"
			)
		)

	@staticmethod
	def _rotation_matrix(rotation_deg: tuple[float, float, float]) -> tuple[tuple[float, float, float], ...]:
		rx, ry, rz = (math.radians(value) for value in rotation_deg)
		cx, sx = math.cos(rx), math.sin(rx)
		cy, sy = math.cos(ry), math.sin(ry)
		cz, sz = math.cos(rz), math.sin(rz)
		return (
			(cz * cy, cz * sy * sx - sz * cx, cz * sy * cx + sz * sx),
			(sz * cy, sz * sy * sx + cz * cx, sz * sy * cx - cz * sx),
			(-sy, cy * sx, cy * cx),
		)

	@staticmethod
	def _two_sided_face_colors(triangles: np.ndarray, color: str, opacity: float) -> np.ndarray:
		face_normals = np.cross(triangles[:, 1] - triangles[:, 0], triangles[:, 2] - triangles[:, 0])
		vertices = triangles.reshape(-1, 3)
		mesh_scale = max(float(np.ptp(vertices, axis=0).max()), 1.0)
		vertex_keys, inverse = np.unique(
			np.rint(vertices / (mesh_scale * 1e-7)).astype(np.int64),
			axis=0,
			return_inverse=True,
		)
		face_areas = np.linalg.norm(face_normals, axis=1)
		face_normals = np.divide(
			face_normals,
			face_areas[:, None],
			out=np.zeros_like(face_normals),
			where=face_areas[:, None] > 0,
		)
		corner_normals = np.zeros((len(vertices), 3), dtype=float)
		vertex_order = np.argsort(inverse)
		vertex_counts = np.bincount(inverse, minlength=len(vertex_keys))
		vertex_offsets = np.concatenate(([0], np.cumsum(vertex_counts)))
		crease_cosine = math.cos(math.radians(50.0))
		for vertex_index in range(len(vertex_keys)):
			incident_corners = vertex_order[vertex_offsets[vertex_index]:vertex_offsets[vertex_index + 1]]
			incident_faces = incident_corners // 3
			incident_normals = face_normals[incident_faces]
			compatible = incident_normals @ incident_normals.T >= crease_cosine
			weighted_normals = compatible @ (face_normals[incident_faces] * face_areas[incident_faces, None])
			corner_normals[incident_corners] = weighted_normals
		corner_lengths = np.linalg.norm(corner_normals, axis=1)
		corner_normals = np.divide(
			corner_normals,
			corner_lengths[:, None],
			out=np.zeros_like(corner_normals),
			where=corner_lengths[:, None] > 0,
		)
		smooth_normals = corner_normals.reshape(-1, 3, 3).mean(axis=1)
		normal_lengths = np.linalg.norm(smooth_normals, axis=1)
		smooth_normals = np.divide(
			smooth_normals,
			normal_lengths[:, None],
			out=np.zeros_like(smooth_normals),
			where=normal_lengths[:, None] > 0,
		)
		light_direction = np.asarray((0.35, -0.45, 0.82), dtype=float)
		light_direction /= np.linalg.norm(light_direction)
		diffuse = np.abs(smooth_normals @ light_direction)
		illumination = 0.32 + 0.68 * diffuse
		base_color = np.asarray(to_rgba(color)[:3])
		rgb = np.clip(base_color[None, :] * illumination[:, None], 0, 1)
		return np.column_stack((rgb, np.full(len(triangles), opacity)))

	def _on_mouse_press(self, event: MouseEvent) -> None:
		if event.inaxes is self.axes and event.button in (1, 3):
			self._drag_button = int(event.button)
			self._last_mouse_position = (event.x, event.y)

	def _on_mouse_release(self, _event: MouseEvent) -> None:
		self._drag_button = None
		self._last_mouse_position = None

	def _on_mouse_move(self, event: MouseEvent) -> None:
		if self._drag_button is None or self._last_mouse_position is None:
			return
		if event.x is None or event.y is None:
			return
		previous_x, previous_y = self._last_mouse_position
		delta_x = event.x - previous_x
		delta_y = event.y - previous_y
		self._last_mouse_position = (event.x, event.y)
		if self._drag_button == 1:
			self.axes.view_init(
				elev=max(-85, min(85, self.axes.elev + delta_y * 0.5)),
				azim=self.axes.azim - delta_x * 0.5,
			)
		else:
			self._pan(delta_x, delta_y)
		self.figure.canvas.draw_idle()

	def _pan(self, delta_x: float, delta_y: float) -> None:
		bounds = (self.axes.get_xlim3d(), self.axes.get_ylim3d(), self.axes.get_zlim3d())
		spans = [upper - lower for lower, upper in bounds]
		pixels = max(1, min(self.axes.bbox.width, self.axes.bbox.height))
		units_per_pixel = max(spans) / pixels
		azimuth = math.radians(self.axes.azim)
		elevation = math.radians(self.axes.elev)
		right = (-math.sin(azimuth), math.cos(azimuth), 0)
		up = (
			-math.sin(elevation) * math.cos(azimuth),
			-math.sin(elevation) * math.sin(azimuth),
			math.cos(elevation),
		)
		shift = tuple(
			-(delta_x * right[index] + delta_y * up[index]) * units_per_pixel
			for index in range(3)
		)
		for axis, limits, offset in zip(
			(self.axes.set_xlim3d, self.axes.set_ylim3d, self.axes.set_zlim3d), bounds, shift
		):
			axis(limits[0] + offset, limits[1] + offset)

	def _on_tk_mousewheel(self, event: tk.Event) -> str:
		delta = getattr(event, "delta", 0)
		if delta:
			steps = max(abs(delta) / 120, 1)
			factor = 0.88**steps if delta > 0 else (1 / 0.88) ** steps
		elif getattr(event, "num", None) == 4:
			factor = 0.88
		elif getattr(event, "num", None) == 5:
			factor = 1 / 0.88
		else:
			return "break"
		self._zoom(factor)
		return "break"

	def _zoom(self, factor: float) -> None:
		for get_limits, set_limits in (
			(self.axes.get_xlim3d, self.axes.set_xlim3d),
			(self.axes.get_ylim3d, self.axes.set_ylim3d),
			(self.axes.get_zlim3d, self.axes.set_zlim3d),
		):
			lower, upper = get_limits()
			center = (lower + upper) / 2
			half_span = (upper - lower) * factor / 2
			if 0.025 <= half_span <= 1e9:
				set_limits(center - half_span, center + half_span)
		self.figure.canvas.draw_idle()

	def show(self) -> None:
		"""Open the interactive simulator window."""
		self.root.mainloop()


def main() -> None:
	RobotArmSimulator().show()


if __name__ == "__main__":
	main()
