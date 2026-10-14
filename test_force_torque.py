"""Check the Lean-generated force/torque ground truth in ``test_data/``.

The data comes from ``lean/ForceTorqueTestData.lean``, which evaluates the transforms
proved in ``lean/TorqueWrench.lean`` over the rationals: regenerate it with, from
``lean/``::

	lake exe force_torque_test_data

Every numeral is exact, so the checks below compare ``Fraction`` values with ``==``
instead of a tolerance -- a failure here is a real disagreement, not floating-point
drift.

The transforms themselves are not implemented in Python yet (``kinematics.py`` has no
sensor frame). When they are, this module is where they get checked: recompute the
``expected`` blocks of each case from its inputs and assert equality with what Lean
computed, using the helpers here for the row-major convention.

What is checked now is that the data is internally consistent -- the properties
``TorqueWrench`` proves, re-derived here from the stored numbers. Two of those are
convention-sensitive and worth stating: the chains check that folding two frames as
``p1 + R1 @ p2`` agrees with converting twice, and that the routes agree in both
directions.
"""

from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path

#: The blocks of a case that hold numbers: the rest (names, source, conventions) is prose.
CASE_NUMERIC_BLOCKS = ("p", "R", "tip_wrench", "sensor_twist", "tip_twist", "expected")

#: The same for a chain.
CHAIN_NUMERIC_BLOCKS = ("p1", "R1", "p2", "R2", "tip_wrench", "sensor_twist", "expected")


def load_document() -> dict:
	"""Return the ground-truth document, parsed from JSON."""
	data_path = Path(__file__).with_name("test_data") / "force_torque_frames.json"
	return json.loads(data_path.read_text(encoding="utf-8"))


def exact(value: str) -> Fraction:
	"""Parse one numeral: an integer or a ``"num/den"`` string, exactly."""
	return Fraction(value)


def vector(entries: list[str]) -> tuple[Fraction, Fraction, Fraction]:
	"""Parse a three-component vector."""
	components = tuple(exact(entry) for entry in entries)
	if len(components) != 3:
		raise ValueError(f"expected a 3-vector, got {len(components)} components")
	return components  # type: ignore[return-value]


def matrix(rows: list[list[str]]) -> tuple[tuple[Fraction, ...], ...]:
	"""Parse a 3x3 block, row-major: ``matrix(rows)[row][column]``."""
	return tuple(vector(row) for row in rows)


def wrench(block: dict) -> tuple[tuple[Fraction, ...], tuple[Fraction, ...]]:
	"""Parse a ``{force, torque}`` block."""
	return vector(block["force"]), vector(block["torque"])


def twist(block: dict) -> tuple[tuple[Fraction, ...], tuple[Fraction, ...]]:
	"""Parse a ``{v, omega}`` block."""
	return vector(block["v"]), vector(block["omega"])


def mat_vec(rotation: tuple[tuple[Fraction, ...], ...], components) -> tuple[Fraction, ...]:
	"""Rotate a vector, matching ``kinematics.py``'s row-by-column convention."""
	return tuple(
		sum(rotation[row][column] * components[column] for column in range(3))
		for row in range(3)
	)


def transpose(rotation: tuple[tuple[Fraction, ...], ...]):
	return tuple(zip(*rotation))


def mat_mul(
	left: tuple[tuple[Fraction, ...], ...], right: tuple[tuple[Fraction, ...], ...]
) -> tuple[tuple[Fraction, ...], ...]:
	return tuple(
		tuple(
			sum(left[row][index] * right[index][column] for index in range(3))
			for column in range(3)
		)
		for row in range(3)
	)


def add(left, right):
	return tuple(a + b for a, b in zip(left, right))


def identity() -> tuple[tuple[Fraction, ...], ...]:
	return tuple(
		tuple(Fraction(1) if row == column else Fraction(0) for column in range(3))
		for row in range(3)
	)


def dot(left, right) -> Fraction:
	return sum(a * b for a, b in zip(left, right))


def virtual_work(wrench_block, twist_block) -> Fraction:
	"""The power of a wrench on a twist: ``F . v + tau . omega``."""
	force, torque = wrench_block
	linear, angular = twist_block
	return dot(force, linear) + dot(torque, angular)


def numerals(entries) -> list[str]:
	"""Every string leaf of the given blocks, i.e. every numeral they store."""
	found: list[str] = []
	pending = list(entries)
	while pending:
		item = pending.pop()
		if isinstance(item, str):
			found.append(item)
		elif isinstance(item, dict):
			pending.extend(item.values())
		elif isinstance(item, list):
			pending.extend(item)
		elif isinstance(item, float):
			raise AssertionError(f"ground truth contains a float: {item!r}")
	return found


class ForceTorqueGroundTruthTests(unittest.TestCase):
	"""The generated cases load exactly and are consistent with the proved theory."""

	@classmethod
	def setUpClass(cls) -> None:
		cls.document = load_document()
		cls.cases = cls.document["cases"]
		cls.chains = cls.document["chains"]

	def test_document_declares_a_supported_schema(self) -> None:
		self.assertEqual(self.document["schema_version"], 2)
		self.assertTrue(self.cases, "the ground-truth file has no cases")
		self.assertTrue(self.chains, "the ground-truth file has no chains")

	def test_every_numeral_is_exact(self) -> None:
		blocks = [
			case[key] for case in self.cases for key in CASE_NUMERIC_BLOCKS
		] + [chain[key] for chain in self.chains for key in CHAIN_NUMERIC_BLOCKS]
		for text in numerals(blocks):
			with self.subTest(numeral=text):
				exact(text)

	def test_rotation_blocks_are_orthogonal(self) -> None:
		"""``R`` has to be a rotation for the cases to mean anything physically."""
		rotations = [(case["name"], matrix(case["R"])) for case in self.cases]
		rotations += [(chain["name"] + " R1", matrix(chain["R1"])) for chain in self.chains]
		rotations += [(chain["name"] + " R2", matrix(chain["R2"])) for chain in self.chains]
		rotations += [
			(chain["name"] + " composed_R", matrix(chain["expected"]["composed_R"]))
			for chain in self.chains
		]
		for name, rotation in rotations:
			with self.subTest(rotation=name):
				self.assertEqual(mat_mul(transpose(rotation), rotation), identity())
				self.assertEqual(mat_mul(rotation, transpose(rotation)), identity())

	def test_virtual_work_agrees_in_both_frames(self) -> None:
		"""The property ``TorqueWrench.virtualWork_invariant`` proves, per case."""
		for case in self.cases:
			with self.subTest(case=case["name"]):
				expected = case["expected"]
				self.assertEqual(
					exact(expected["virtual_work_sensor_frame"]),
					exact(expected["virtual_work_tip_frame"]),
				)

	def test_stored_virtual_work_matches_the_stored_vectors(self) -> None:
		"""The work fields are consistent with the vectors they were computed from."""
		for case in self.cases:
			with self.subTest(case=case["name"]):
				expected = case["expected"]
				self.assertEqual(
					exact(expected["virtual_work_sensor_frame"]),
					virtual_work(wrench(expected["sensor_wrench"]), twist(case["sensor_twist"])),
				)
				self.assertEqual(
					exact(expected["virtual_work_tip_frame"]),
					virtual_work(
						wrench(case["tip_wrench"]), twist(expected["tip_twist_from_sensor"])
					),
				)

	def test_sensor_to_tip_recovers_the_applied_wrench(self) -> None:
		"""Converting back to the sensor frame and forward again is lossless."""
		for case in self.cases:
			with self.subTest(case=case["name"]):
				self.assertEqual(
					wrench(case["expected"]["sensor_to_tip_wrench"]),
					wrench(case["tip_wrench"]),
				)

	def test_pure_translation_only_shifts_the_torque(self) -> None:
		"""With ``R = 1`` the force is untouched and the torque moves by ``p x F``."""
		for case in self.cases:
			if case["name"] != "pure_translation_lever_arm":
				continue
			with self.subTest(case=case["name"]):
				offset = vector(case["p"])
				force, torque = wrench(case["tip_wrench"])
				lever_arm = (
					offset[1] * force[2] - offset[2] * force[1],
					offset[2] * force[0] - offset[0] * force[2],
					offset[0] * force[1] - offset[1] * force[0],
				)
				shifted_force, shifted_torque = wrench(case["expected"]["sensor_wrench"])
				self.assertEqual(shifted_force, force)
				self.assertEqual(shifted_torque, add(torque, lever_arm))

	def test_identity_case_is_the_identity_transform(self) -> None:
		"""With ``R = 1`` and ``p = 0`` every direction has to return its input."""
		for case in self.cases:
			if case["name"] != "identity_no_offset":
				continue
			with self.subTest(case=case["name"]):
				expected = case["expected"]
				self.assertEqual(wrench(expected["sensor_wrench"]), wrench(case["tip_wrench"]))
				self.assertEqual(wrench(expected["sensor_to_tip_wrench"]), wrench(case["tip_wrench"]))
				self.assertEqual(
					twist(expected["tip_twist_from_sensor"]), twist(case["sensor_twist"])
				)
				self.assertEqual(
					twist(expected["sensor_twist_from_tip"]), twist(case["tip_twist"])
				)

	def test_chains_fold_the_pose_the_way_the_theorem_says(self) -> None:
		"""``(p1, R1)`` then ``(p2, R2)`` is ``p1 + R1 @ p2`` with ``R1 * R2``."""
		for chain in self.chains:
			with self.subTest(chain=chain["name"]):
				expected = chain["expected"]
				self.assertEqual(
					vector(expected["composed_p"]),
					add(vector(chain["p1"]), mat_vec(matrix(chain["R1"]), vector(chain["p2"]))),
				)
				self.assertEqual(
					matrix(expected["composed_R"]),
					mat_mul(matrix(chain["R1"]), matrix(chain["R2"])),
				)

	def test_chain_routes_agree(self) -> None:
		"""One step with the folded pose equals two steps through the middle frame."""
		for chain in self.chains:
			with self.subTest(chain=chain["name"]):
				expected = chain["expected"]
				self.assertEqual(
					wrench(expected["sensor_wrench_one_step"]),
					wrench(expected["sensor_wrench_two_steps"]),
				)
				self.assertEqual(
					twist(expected["tip_twist_one_step"]),
					twist(expected["tip_twist_two_steps"]),
				)


if __name__ == "__main__":
	unittest.main()
