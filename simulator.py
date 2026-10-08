"""Interactive 3D viewport for developing the robot-arm simulator."""

from __future__ import annotations

import json
import math
import tkinter as tk
from pathlib import Path
from tkinter import messagebox, ttk

from matplotlib.axes import Axes
from matplotlib.backend_bases import MouseEvent
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure

from kinematics import DHParameters, forward_kinematics, frame_origin

DEFAULT_DH_VALUES = (
	(0.0, 0.30, 0.0, 90.0),
	(0.0, 0.0, 0.40, 0.0),
	(0.0, 0.0, 0.35, 0.0),
	(0.0, 0.30, 0.0, 90.0),
	(0.0, 0.0, 0.0, -90.0),
	(0.0, 0.12, 0.0, 0.0),
)


class RobotArmSimulator:
	"""Display a navigable robot scene and editable six-joint DH parameters."""

	def __init__(self) -> None:
		self.root = tk.Tk()
		self.root.title("6-Axis Robot Simulator")
		self.root.geometry("1120x760")
		self.root.minsize(820, 600)
		self.config_path = Path(__file__).with_name("robot_parameters.json")
		self._drag_button: int | None = None
		self._last_mouse_position: tuple[float, float] | None = None
		self.parameters = self._to_dh_parameters(DEFAULT_DH_VALUES)

		self.notebook = ttk.Notebook(self.root)
		self.notebook.pack(fill=tk.BOTH, expand=True)
		self.view_tab = ttk.Frame(self.notebook, padding=8)
		self.parameters_tab = ttk.Frame(self.notebook, padding=16)
		self.notebook.add(self.view_tab, text="3D View")
		self.notebook.add(self.parameters_tab, text="DH Parameters")

		self.figure = Figure(figsize=(8, 6), facecolor="#f4f6f7")
		self.axes: Axes = self.figure.add_subplot(111, projection="3d")
		self.canvas = FigureCanvasTkAgg(self.figure, master=self.view_tab)
		self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
		self.pose_label = ttk.Label(self.view_tab, anchor=tk.W, padding=(4, 8))
		self.pose_label.pack(fill=tk.X)
		self.figure.subplots_adjust(left=0, right=1, bottom=0, top=1)

		self._build_parameter_tab()
		if self.config_path.exists():
			try:
				self._populate_entries(self._read_json_parameters())
			except (OSError, ValueError, TypeError, KeyError) as error:
				messagebox.showerror("Parameter file error", str(error), parent=self.root)
		self.parameters = self._read_entry_parameters()
		self._render_scene()

		self.axes.mouse_init(rotate_btn=[], pan_btn=[], zoom_btn=[])
		self.canvas.mpl_connect("button_press_event", self._on_mouse_press)
		self.canvas.mpl_connect("button_release_event", self._on_mouse_release)
		self.canvas.mpl_connect("motion_notify_event", self._on_mouse_move)
		self.canvas.mpl_connect("scroll_event", self._on_scroll)

	def _build_parameter_tab(self) -> None:
		ttk.Label(
			self.parameters_tab,
			text="Denavit–Hartenberg parameters",
			font=("Segoe UI", 16, "bold"),
		).grid(row=0, column=0, columnspan=5, sticky=tk.W, pady=(0, 6))
		ttk.Label(
			self.parameters_tab,
			text="Angles are in degrees. Use consistent units for d and a.",
		).grid(row=1, column=0, columnspan=5, sticky=tk.W, pady=(0, 18))

		headings = ("Joint", "Theta (deg)", "d", "a", "Alpha (deg)")
		for column, heading in enumerate(headings):
			ttk.Label(self.parameters_tab, text=heading, font=("Segoe UI", 10, "bold")).grid(
				row=2, column=column, sticky=tk.W, padx=(0, 12), pady=(0, 8)
			)

		self.parameter_entries: list[tuple[ttk.Entry, ...]] = []
		for joint_index, values in enumerate(DEFAULT_DH_VALUES, start=1):
			ttk.Label(self.parameters_tab, text=f"J{joint_index}").grid(
				row=joint_index + 2, column=0, sticky=tk.W, padx=(0, 12), pady=4
			)
			entries: list[ttk.Entry] = []
			for column, value in enumerate(values, start=1):
				entry = ttk.Entry(self.parameters_tab, width=16)
				entry.grid(row=joint_index + 2, column=column, sticky=tk.W, padx=(0, 12), pady=4)
				entry.insert(0, self._format_value(value))
				entries.append(entry)
			self.parameter_entries.append(tuple(entries))

		button_row = ttk.Frame(self.parameters_tab)
		button_row.grid(row=10, column=0, columnspan=5, sticky=tk.W, pady=(18, 8))
		ttk.Button(button_row, text="Apply to View", command=self._apply_from_entries).pack(
			side=tk.LEFT, padx=(0, 8)
		)
		ttk.Button(button_row, text="Save JSON", command=self._save_json).pack(
			side=tk.LEFT, padx=(0, 8)
		)
		ttk.Button(button_row, text="Load JSON", command=self._load_json).pack(side=tk.LEFT)
		ttk.Label(self.parameters_tab, text=f"File: {self.config_path.name}").grid(
			row=11, column=0, columnspan=5, sticky=tk.W, pady=(4, 0)
		)

	@staticmethod
	def _format_value(value: float) -> str:
		return f"{value:g}"

	@staticmethod
	def _to_dh_parameters(values: tuple[tuple[float, float, float, float], ...]) -> tuple[DHParameters, ...]:
		return tuple(
			DHParameters(math.radians(theta), d, a, math.radians(alpha))
			for theta, d, a, alpha in values
		)

	def _read_entry_values(self) -> tuple[tuple[float, float, float, float], ...]:
		rows = tuple(tuple(float(entry.get()) for entry in row) for row in self.parameter_entries)
		if len(rows) != 6 or any(len(row) != 4 for row in rows):
			raise ValueError("Exactly six joints with four DH values each are required.")
		if not all(math.isfinite(value) for row in rows for value in row):
			raise ValueError("All DH values must be finite numbers.")
		return rows

	def _read_entry_parameters(self) -> tuple[DHParameters, ...]:
		return self._to_dh_parameters(self._read_entry_values())

	def _populate_entries(self, values: tuple[tuple[float, float, float, float], ...]) -> None:
		for row_entries, row_values in zip(self.parameter_entries, values):
			for entry, value in zip(row_entries, row_values):
				entry.delete(0, tk.END)
				entry.insert(0, self._format_value(value))

	def _apply_from_entries(self) -> bool:
		try:
			self.parameters = self._read_entry_parameters()
		except ValueError as error:
			messagebox.showerror("Invalid DH parameters", str(error), parent=self.root)
			return False
		self._render_scene()
		return True

	def _save_json(self) -> None:
		try:
			values = self._read_entry_values()
		except ValueError as error:
			messagebox.showerror("Invalid DH parameters", str(error), parent=self.root)
			return

		self.parameters = self._to_dh_parameters(values)
		self._render_scene()
		data = {
			"schema_version": 1,
			"units": {"angles": "degrees", "lengths": "model_units"},
			"joints": [
				{
					"theta_deg": theta,
					"d": d,
					"a": a,
					"alpha_deg": alpha,
				}
				for theta, d, a, alpha in values
			],
		}
		try:
			self.config_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
		except OSError as error:
			messagebox.showerror("Could not save parameters", str(error), parent=self.root)
			return
		messagebox.showinfo("Parameters saved", f"Saved to {self.config_path.name}.", parent=self.root)

	def _read_json_parameters(self) -> tuple[tuple[float, float, float, float], ...]:
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
		rows = tuple(
			(
				float(joint["theta_deg"]),
				float(joint["d"]),
				float(joint["a"]),
				float(joint["alpha_deg"]),
			)
			for joint in joints
		)
		if not all(math.isfinite(value) for row in rows for value in row):
			raise ValueError("Parameter file values must all be finite numbers.")
		return rows

	def _load_json(self) -> None:
		try:
			values = self._read_json_parameters()
		except (OSError, ValueError, TypeError, KeyError) as error:
			messagebox.showerror("Could not load parameters", str(error), parent=self.root)
			return
		self._populate_entries(values)
		self.parameters = self._to_dh_parameters(values)
		self._render_scene()

	def _render_scene(self) -> None:
		elevation, azimuth = self.axes.elev, self.axes.azim
		transforms = forward_kinematics(self.parameters)
		frame_origins = ((0.0, 0.0, 0.0),) + tuple(frame_origin(transform) for transform in transforms)
		self.axes.clear()
		self.axes.set_facecolor("#f4f6f7")
		self.axes.set_axis_off()
		self.axes.set_box_aspect((1, 1, 1))
		self.axes.view_init(elev=elevation, azim=azimuth)

		minimums = tuple(min(point[axis] for point in frame_origins) for axis in range(3))
		maximums = tuple(max(point[axis] for point in frame_origins) for axis in range(3))
		center = tuple((minimums[axis] + maximums[axis]) / 2 for axis in range(3))
		radius = max(max(maximums[axis] - minimums[axis] for axis in range(3)) / 2, 0.5)
		half_span = radius * 1.45
		self.axes.set_xlim(center[0] - half_span, center[0] + half_span)
		self.axes.set_ylim(center[1] - half_span, center[1] + half_span)
		self.axes.set_zlim(center[2] - half_span, center[2] + half_span)

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
		for frame_index, (origin, transform) in enumerate(zip(frame_origins, (None,) + transforms)):
			if transform is None:
				rotation = ((1.0, 0.0, 0.0), (0.0, 1.0, 0.0), (0.0, 0.0, 1.0))
			else:
				rotation = tuple(tuple(transform[row][column] for row in range(3)) for column in range(3))
			for direction, color in zip(rotation, axis_colors):
				self.axes.quiver(
					*origin,
					*(component * marker_length for component in direction),
					color=color,
					linewidth=1.5,
					arrow_length_ratio=0.24,
				)
			self.axes.text(
				origin[0],
				origin[1],
				origin[2] + marker_length * 0.2,
				"Base" if frame_index == 0 else f"J{frame_index}",
				color="#26323b",
				fontsize=8,
			)
		self.canvas.draw_idle()
		tool_position = frame_origins[-1]
		self.pose_label.configure(
			text=f"Frame 6 origin: X {tool_position[0]:.3f}   Y {tool_position[1]:.3f}   Z {tool_position[2]:.3f}"
		)

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
		bounds = (
			self.axes.get_xlim3d(),
			self.axes.get_ylim3d(),
			self.axes.get_zlim3d(),
		)
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
			(self.axes.set_xlim3d, self.axes.set_ylim3d, self.axes.set_zlim3d),
			bounds,
			shift,
		):
			axis(limits[0] + offset, limits[1] + offset)

	def _on_scroll(self, event: MouseEvent) -> None:
		if event.inaxes is not self.axes:
			return
		factor = 0.88 if event.button == "up" else 1 / 0.88
		for get_limits, set_limits in (
			(self.axes.get_xlim3d, self.axes.set_xlim3d),
			(self.axes.get_ylim3d, self.axes.set_ylim3d),
			(self.axes.get_zlim3d, self.axes.set_zlim3d),
		):
			lower, upper = get_limits()
			center = (lower + upper) / 2
			half_span = (upper - lower) * factor / 2
			if 0.025 <= half_span <= 50:
				set_limits(center - half_span, center + half_span)
		self.figure.canvas.draw_idle()

	def show(self) -> None:
		"""Open the interactive simulator window."""
		self.root.mainloop()


def main() -> None:
	RobotArmSimulator().show()


if __name__ == "__main__":
	main()
