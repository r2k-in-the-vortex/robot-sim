"""Interactive 3D viewport for developing the robot-arm simulator."""

from __future__ import annotations

import math

import matplotlib.pyplot as plt
from matplotlib.axes import Axes
from matplotlib.backend_bases import MouseEvent


class RobotArmSimulator:
	"""Display a navigable 3D scene with a coordinate frame at the origin."""

	def __init__(self) -> None:
		self.figure = plt.figure("6-Axis Robot Simulator", figsize=(9, 7))
		self.axes: Axes = self.figure.add_subplot(111, projection="3d")
		self._drag_button: int | None = None
		self._last_mouse_position: tuple[float, float] | None = None

		self._configure_scene()
		self._draw_origin_frame()
		self.axes.mouse_init(rotate_btn=[], pan_btn=[], zoom_btn=[])
		self.figure.canvas.mpl_connect("button_press_event", self._on_mouse_press)
		self.figure.canvas.mpl_connect("button_release_event", self._on_mouse_release)
		self.figure.canvas.mpl_connect("motion_notify_event", self._on_mouse_move)
		self.figure.canvas.mpl_connect("scroll_event", self._on_scroll)

	def _configure_scene(self) -> None:
		self.figure.patch.set_facecolor("#f4f6f7")
		self.axes.set_facecolor("#f4f6f7")
		self.axes.set_xlim(-1.4, 1.4)
		self.axes.set_ylim(-1.4, 1.4)
		self.axes.set_zlim(-1.4, 1.4)
		self.axes.set_box_aspect((1, 1, 1))
		self.axes.view_init(elev=24, azim=-55)
		self.axes.set_axis_off()
		self.figure.subplots_adjust(left=0, right=1, bottom=0, top=1)

	def _draw_origin_frame(self) -> None:
		axis_length = 1.0
		axes = (
			((1, 0, 0), "X", "#d94a45"),
			((0, 1, 0), "Y", "#31845b"),
			((0, 0, 1), "Z", "#3978c5"),
		)
		for direction, label, color in axes:
			self.axes.quiver(
				0,
				0,
				0,
				direction[0],
				direction[1],
				direction[2],
				color=color,
				linewidth=2.5,
				arrow_length_ratio=0.12,
			)
			self.axes.text(
				direction[0] * (axis_length + 0.14),
				direction[1] * (axis_length + 0.14),
				direction[2] * (axis_length + 0.14),
				label,
				color=color,
				fontsize=12,
				fontweight="bold",
			)
		self.axes.scatter([0], [0], [0], color="#202a33", s=24, depthshade=False)

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
		plt.show()


def main() -> None:
	RobotArmSimulator().show()


if __name__ == "__main__":
	main()
