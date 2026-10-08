"""Forward kinematics for a six-axis robot using standard DH parameters."""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Sequence

Matrix4 = tuple[tuple[float, float, float, float], ...]


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