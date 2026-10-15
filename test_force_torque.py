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

#: The same for a dynamics case. `parts` is `None` or two mass-property blocks, so it is swept
#: separately rather than listed here.
DYNAMICS_NUMERIC_BLOCKS = (
	"p",
	"R",
	"mass_properties",
	"gravity",
	"sensor_twist",
	"sensor_accel",
	"tip_wrench",
	"expected",
)


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


def accel(block: dict) -> tuple[tuple[Fraction, ...], tuple[Fraction, ...]]:
	"""Parse an ``{a, alpha}`` block."""
	return vector(block["a"]), vector(block["alpha"])


def wrench_add(left, right):
	"""Add two wrenches, i.e. their forces and their torques separately."""
	return add(left[0], right[0]), add(left[1], right[1])


def wrench_sub(left, right):
	return sub(left[0], right[0]), sub(left[1], right[1])


def sub(left, right):
	return tuple(a - b for a, b in zip(left, right))


def scale(factor: Fraction, components):
	return tuple(factor * component for component in components)


def cross(left, right):
	"""The cross product, matching ``TorqueWrench.cross``."""
	return (
		left[1] * right[2] - left[2] * right[1],
		left[2] * right[0] - left[0] * right[2],
		left[0] * right[1] - left[1] * right[0],
	)


def mass_properties(block: dict):
	"""Parse a ``{mass, com, inertia}`` block."""
	return exact(block["mass"]), vector(block["com"]), matrix(block["inertia"])


def outer(left, right):
	return tuple(tuple(a * b for b in right) for a in left)


def mat_add(left, right):
	return tuple(tuple(a + b for a, b in zip(row_l, row_r)) for row_l, row_r in zip(left, right))


def mat_sub(left, right):
	return tuple(tuple(a - b for a, b in zip(row_l, row_r)) for row_l, row_r in zip(left, right))


def mat_scale(factor: Fraction, entries):
	return tuple(tuple(factor * entry for entry in row) for row in entries)


def origin_inertia(mass: Fraction, com, inertia):
	"""The inertia about the frame origin: ``I_c + m (⟨c,c⟩ 1 - c cᵀ)``."""
	identity_block = identity()
	square = dot(com, com)
	return mat_add(
		inertia,
		mat_scale(mass, mat_sub(mat_scale(square, identity_block), outer(com, com))),
	)


def inertial_wrench(mass: Fraction, com, inertia, linear, angular, acc_linear, acc_angular):
	"""Newton-Euler about the frame origin, as ``Dynamics.inertialWrench``."""
	centred = add(add(acc_linear, cross(acc_angular, com)), cross(angular, cross(angular, com)))
	force = scale(mass, centred)
	torque = add(
		add(mat_vec(inertia, acc_angular), cross(angular, mat_vec(inertia, angular))),
		cross(com, force),
	)
	return force, torque


def gravity_wrench(mass: Fraction, com, gravity):
	"""The wrench of gravity on the body, as ``Dynamics.gravityWrench``."""
	return scale(mass, gravity), cross(com, scale(mass, gravity))


def sensor_twist_to_tip(p, rotation, sensor_twist):
	"""A sensor twist, in tip coordinates, as ``TorqueWrench.sensorTwistToTip``."""
	linear, angular = sensor_twist
	return (
		mat_vec(transpose(rotation), add(linear, cross(angular, p))),
		mat_vec(transpose(rotation), angular),
	)


def sensor_accel_to_tip(p, rotation, sensor_twist, sensor_accel):
	"""A sensor acceleration, in tip coordinates, as ``Dynamics.sensorAccelToTip``."""
	linear, angular = sensor_accel
	_, omega = sensor_twist
	return (
		mat_vec(
			transpose(rotation),
			add(add(linear, cross(angular, p)), cross(omega, cross(omega, p))),
		),
		mat_vec(transpose(rotation), angular),
	)


def tip_to_sensor(p, rotation, tip_wrench):
	"""A tip wrench, in sensor coordinates, as ``TorqueWrench.tipToSensor``."""
	force, torque = tip_wrench
	moved_force = mat_vec(rotation, force)
	return moved_force, add(mat_vec(rotation, torque), cross(p, moved_force))


def sensor_to_tip(p, rotation, sensor_wrench):
	"""A sensor wrench, in tip coordinates, as ``TorqueWrench.sensorToTip``."""
	force, torque = sensor_wrench
	return (
		mat_vec(transpose(rotation), force),
		mat_vec(transpose(rotation), sub(torque, cross(p, force))),
	)


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
		self.assertEqual(self.document["schema_version"], 3)
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


class DynamicsGroundTruthTests(unittest.TestCase):
	"""The dynamics cases recompute, from their inputs, to the numbers Lean stored.

	This is the reference recomputation the module docstring promises: every entry of a case's
	``expected`` block is re-derived here in exact ``Fraction`` arithmetic from the case's inputs,
	using the definitions of ``lean/Dynamics.lean``. A disagreement is either a mistake in Lean's
	model or a mistake in this transcription of it -- both worth failing on.
	"""

	@classmethod
	def setUpClass(cls) -> None:
		cls.document = load_document()
		cls.cases = cls.document["dynamics_cases"]
		cls.by_name = {case["name"]: case for case in cls.cases}

	def recompute(self, case: dict) -> dict:
		"""Every ``expected`` entry of a dynamics case, re-derived from its inputs."""
		p = vector(case["p"])
		rotation = matrix(case["R"])
		mass, com, inertia = mass_properties(case["mass_properties"])
		gravity = vector(case["gravity"])
		sensor_twist = twist(case["sensor_twist"])
		sensor_accel = accel(case["sensor_accel"])
		contact = wrench(case["tip_wrench"])

		# the same body, described in sensor coordinates
		sensor_com = add(p, mat_vec(rotation, com))
		sensor_inertia = mat_mul(mat_mul(rotation, inertia), transpose(rotation))

		# the same motion, described in tip coordinates
		tip_twist = sensor_twist_to_tip(p, rotation, sensor_twist)
		tip_accel = sensor_accel_to_tip(p, rotation, sensor_twist, sensor_accel)
		tip_linear, tip_angular = tip_twist
		tip_acc_linear, tip_acc_angular = tip_accel
		centred_accel = add(
			add(tip_acc_linear, cross(tip_acc_angular, com)),
			cross(tip_angular, cross(tip_angular, com)),
		)
		centred_velocity = add(tip_linear, cross(tip_angular, com))

		sensor_inertial = inertial_wrench(
			mass, sensor_com, sensor_inertia, *sensor_twist, *sensor_accel
		)
		tip_inertial = inertial_wrench(mass, com, inertia, *tip_twist, *tip_accel)
		tip_gravity = gravity_wrench(mass, com, mat_vec(transpose(rotation), gravity))
		sensor_gravity = gravity_wrench(mass, sensor_com, gravity)

		measured = wrench_sub(
			wrench_add(tip_to_sensor(p, rotation, contact), sensor_inertial), sensor_gravity
		)
		recovered = sensor_to_tip(
			p, rotation, wrench_add(wrench_sub(measured, sensor_inertial), sensor_gravity)
		)

		return {
			"mass_properties_in_sensor_frame": {
				"mass": mass,
				"com": sensor_com,
				"inertia": sensor_inertia,
			},
			"tip_twist": tip_twist,
			"tip_accel": tip_accel,
			"com_accel": centred_accel,
			"first_moment": scale(mass, com),
			"origin_inertia": origin_inertia(mass, com, inertia),
			"inertial_wrench": sensor_inertial,
			"inertial_wrench_from_tip": tip_to_sensor(p, rotation, tip_inertial),
			"gravity_wrench": sensor_gravity,
			"gravity_wrench_from_tip": tip_to_sensor(p, rotation, tip_gravity),
			"power_inertial_work": virtual_work(tip_inertial, tip_twist),
			"power_inertial_formula": mass * dot(centred_accel, centred_velocity)
			+ dot(tip_acc_angular, mat_vec(inertia, tip_angular)),
			"power_gravity_work": virtual_work(tip_gravity, tip_twist),
			"power_gravity_formula": mass * dot(mat_vec(transpose(rotation), gravity), centred_velocity),
			"measured_wrench": measured,
			"recovered_contact_wrench": recovered,
		}

	def test_dynamics_cases_are_present(self) -> None:
		self.assertTrue(self.cases, "the ground-truth file has no dynamics cases")
		self.assertEqual(len(self.by_name), len(self.cases))

	def test_every_dynamics_numeral_is_exact(self) -> None:
		blocks = []
		for case in self.cases:
			blocks += [case[key] for key in DYNAMICS_NUMERIC_BLOCKS]
			if case["parts"] is not None:
				blocks += list(case["parts"])
		for text in numerals(blocks):
			with self.subTest(numeral=text):
				exact(text)

	def test_recomputed_values_match(self) -> None:
		"""Every stored quantity is re-derived from the inputs, entry by entry."""
		for case in self.cases:
			with self.subTest(case=case["name"]):
				mine = self.recompute(case)
				expected = case["expected"]
				mass, com, inertia = mass_properties(expected["mass_properties_in_sensor_frame"])
				self.assertEqual(
					mine["mass_properties_in_sensor_frame"],
					{"mass": mass, "com": com, "inertia": inertia},
				)
				self.assertEqual(mine["tip_twist"], twist(expected["tip_twist"]))
				self.assertEqual(mine["tip_accel"], accel(expected["tip_accel"]))
				self.assertEqual(mine["com_accel"], vector(expected["com_accel"]))
				self.assertEqual(mine["first_moment"], vector(expected["first_moment"]))
				self.assertEqual(mine["origin_inertia"], matrix(expected["origin_inertia"]))
				self.assertEqual(mine["inertial_wrench"], wrench(expected["inertial_wrench"]))
				self.assertEqual(
					mine["inertial_wrench_from_tip"],
					wrench(expected["inertial_wrench_from_tip"]),
				)
				self.assertEqual(mine["gravity_wrench"], wrench(expected["gravity_wrench"]))
				self.assertEqual(
					mine["gravity_wrench_from_tip"], wrench(expected["gravity_wrench_from_tip"])
				)
				self.assertEqual(
					mine["power_inertial_work"], exact(expected["power_inertial_work"])
				)
				self.assertEqual(
					mine["power_inertial_formula"], exact(expected["power_inertial_formula"])
				)
				self.assertEqual(
					mine["power_gravity_work"], exact(expected["power_gravity_work"])
				)
				self.assertEqual(
					mine["power_gravity_formula"], exact(expected["power_gravity_formula"])
				)
				self.assertEqual(mine["measured_wrench"], wrench(expected["measured_wrench"]))
				self.assertEqual(
					mine["recovered_contact_wrench"],
					wrench(expected["recovered_contact_wrench"]),
				)

	def test_state_is_frame_independent(self) -> None:
		"""Both sides of the covariance theorems agree, for every case."""
		for case in self.cases:
			with self.subTest(case=case["name"]):
				expected = case["expected"]
				self.assertEqual(
					wrench(expected["inertial_wrench"]),
					wrench(expected["inertial_wrench_from_tip"]),
				)
				self.assertEqual(
					wrench(expected["gravity_wrench"]),
					wrench(expected["gravity_wrench_from_tip"]),
				)

	def test_compensation_recovers_the_contact_wrench(self) -> None:
		for case in self.cases:
			with self.subTest(case=case["name"]):
				self.assertEqual(
					wrench(case["expected"]["recovered_contact_wrench"]),
					wrench(case["tip_wrench"]),
				)

	def test_a_body_at_rest_reads_minus_its_gravity_wrench(self) -> None:
		"""The sign convention: gravity pulls down, the sensor feels the reaction."""
		case = self.by_name["rest_gravity_only"]
		expected = case["expected"]
		mass, com, inertia = mass_properties(expected["mass_properties_in_sensor_frame"])
		gravity = vector(case["gravity"])
		force, torque = gravity_wrench(mass, com, gravity)
		self.assertEqual(wrench(expected["measured_wrench"]),
			(tuple(-component for component in force), tuple(-component for component in torque)))
		self.assertTrue(any(component != 0 for component in force))
		self.assertTrue(any(component != 0 for component in torque))
		self.assertEqual(wrench(case["tip_wrench"]), ((0, 0, 0), (0, 0, 0)))

	def test_a_body_at_rest_has_no_inertial_wrench(self) -> None:
		for name in ("rest_gravity_only", "rest_gravity_rotated", "rest_gravity_with_contact"):
			with self.subTest(case=name):
				force, torque = wrench(self.by_name[name]["expected"]["inertial_wrench"])
				self.assertEqual(force, (0, 0, 0))
				self.assertEqual(torque, (0, 0, 0))

	def tip_frame_inertial_wrench(self, case: dict):
		"""The stored sensor-frame inertial wrench, carried back down to the tip frame."""
		return sensor_to_tip(
			vector(case["p"]), matrix(case["R"]), wrench(case["expected"]["inertial_wrench"])
		)

	def test_spinning_body_force_is_the_centripetal_term(self) -> None:
		"""`centripetal_only` has `a = α = g = 0` *at the sensor origin*, so the sensor-frame
		force is exactly `m ω × (ω × c)`. A model missing the centripetal term reports zero.

		(The tip frame is a different matter: the tip origin genuinely accelerates, which is what
		the acceleration transport accounts for.)
		"""
		case = self.by_name["centripetal_only"]
		mass, sensor_com, _ = mass_properties(
			case["expected"]["mass_properties_in_sensor_frame"]
		)
		_, angular = twist(case["sensor_twist"])
		force = scale(mass, cross(angular, cross(angular, sensor_com)))
		self.assertTrue(any(component != 0 for component in force))
		expected_force, _ = wrench(case["expected"]["inertial_wrench"])
		self.assertEqual(expected_force, force)

	def test_gyroscopic_torque_is_present(self) -> None:
		"""`gyroscopic_only` has `a = α = g = 0` and `c = 0`: the torque is exactly `ω × (I ω)`."""
		case = self.by_name["gyroscopic_only"]
		_, com, inertia = mass_properties(case["mass_properties"])
		self.assertEqual(com, (0, 0, 0))
		_, angular = twist(case["expected"]["tip_twist"])
		torque = cross(angular, mat_vec(inertia, angular))
		self.assertTrue(any(component != 0 for component in torque))
		_, expected_torque = self.tip_frame_inertial_wrench(case)
		self.assertEqual(expected_torque, torque)

	def test_no_motion_and_no_gravity_is_the_static_transform(self) -> None:
		case = self.by_name["zero_motion"]
		p = vector(case["p"])
		rotation = matrix(case["R"])
		self.assertEqual(
			wrench(case["expected"]["measured_wrench"]),
			tip_to_sensor(p, rotation, wrench(case["tip_wrench"])),
		)

	def test_composition_parts_sum_to_the_composite(self) -> None:
		"""The composite's mass, first moment and origin inertia are the sums of the parts'."""
		for case in self.cases:
			if case["parts"] is None:
				continue
			with self.subTest(case=case["name"]):
				mass, com, inertia = mass_properties(case["mass_properties"])
				part_blocks = [mass_properties(block) for block in case["parts"]]
				self.assertEqual(mass, sum(part_mass for part_mass, _, _ in part_blocks))
				self.assertEqual(
					scale(mass, com),
					add(scale(part_blocks[0][0], part_blocks[0][1]),
						scale(part_blocks[1][0], part_blocks[1][1])),
				)
				self.assertEqual(
					origin_inertia(mass, com, inertia),
					mat_add(
						origin_inertia(part_blocks[0][0], part_blocks[0][1], part_blocks[0][2]),
						origin_inertia(part_blocks[1][0], part_blocks[1][1], part_blocks[1][2]),
					),
				)
				# and the wrenches add too, which is what `Dynamics.inertialWrench_add` proves
				tip_twist = twist(case["expected"]["tip_twist"])
				tip_accel = accel(case["expected"]["tip_accel"])
				composite = inertial_wrench(mass, com, inertia, *tip_twist, *tip_accel)
				summed_force = (Fraction(0), Fraction(0), Fraction(0))
				summed_torque = (Fraction(0), Fraction(0), Fraction(0))
				for part_mass, part_com, part_inertia in part_blocks:
					part_force, part_torque = inertial_wrench(
						part_mass, part_com, part_inertia, *tip_twist, *tip_accel
					)
					summed_force = add(summed_force, part_force)
					summed_torque = add(summed_torque, part_torque)
				self.assertEqual(composite, (summed_force, summed_torque))


if __name__ == "__main__":
	unittest.main()
