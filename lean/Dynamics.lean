module
-- `TorqueWrench` carries the frame algebra (`Wrench`, `Twist`, `cross`, `Rotation`); this
-- file builds the rigid-body side on top of it. As there, the imports are `public` because
-- the declarations below are exported (`@[expose] public section`).
public import TorqueWrench
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NoncommRing

open Matrix
open scoped Matrix

@[expose] public section

/-!
# Inertia, gravity, and the force/torque sensor measurement model

`TorqueWrench` proves the *static* frame algebra of a force/torque sensor: a wrench carried
from the tool tip to the sensor frame, with virtual power preserved. A real sensor, though,
measures the wrench *transmitted through it*, which is the contact wrench plus the
gravitational and inertial wrench of everything mounted distal to it. This file adds those
two terms, proves that subtracting them recovers the contact wrench exactly, and proves that
the whole model is frame-independent (covariance) and that bodies compose.

Everything stays algebraic over a commutative ring, so it lifts to `ℝ` for free and still
*evaluates* at `ℚ` — which is what `ForceTorqueTestData` uses to emit exact ground truth.
No calculus is needed: acceleration is an independent datum, not a derivative, so the power
identities below are polynomial statements (`virtualWork_inertialWrench`).

Conventions, all inherited from `TorqueWrench` unless stated:

* `p` is the tip origin in **sensor** coordinates and `R` maps tip coordinates to sensor
  coordinates. Both frames are rigidly attached to the same body (the sensor's distal face
  and the tool tip), which is what makes the acceleration transport an identity of
  rigid-body kinematics rather than a new assumption.
* The sensor measures the wrench the proximal side applies to the distal body. With `g` the
  gravitational *acceleration* (pointing down, not the reaction to it) a sensor at rest
  therefore reads `-gravityWrench`, and the model is

      measured = transport(contact) + inertial - gravity

* `MassProperties` carries the centre of mass and the inertia **about the centre of mass** —
  the intrinsic properties of the body. The inertia about the frame origin is derived
  (`originInertia`, the parallel-axis shift), and it is that derived quantity, together with
  the mass and the first moment, that makes bodies add.
* The lever arm in both acceleration directions is `p` in sensor coordinates, the same arm
  `tipTwistToSensor` subtracts, combined with the *rotated* angular parts. The acceleration
  transforms differ from the twist transforms only by the `ω × (ω × p)` centripetal term.
-/

variable {α : Type*} [CommRing α]
variable {β : Type*}

/-! ## Wrench and twist as vectors

The frame algebra below adds wrenches (a measured wrench is a sum of terms) and subtracts
them again during compensation, so the structures need the pointwise group and module
operations. Nothing here is more than `rfl`; `DecidableEq` is deliberately left out, since
the test data compares components.
-/

namespace Wrench

instance : Zero (Wrench α) := ⟨⟨0, 0⟩⟩
instance : Add (Wrench α) := ⟨fun a b => ⟨a.force + b.force, a.torque + b.torque⟩⟩
instance : Sub (Wrench α) := ⟨fun a b => ⟨a.force - b.force, a.torque - b.torque⟩⟩
instance : Neg (Wrench α) := ⟨fun a => ⟨-a.force, -a.torque⟩⟩
instance [SMul β α] : SMul β (Wrench α) := ⟨fun c a => ⟨c • a.force, c • a.torque⟩⟩

-- The operations are pointwise, stated as *equations* rather than as projection lemmas: `simp`
-- then rewrites a wrench expression into a structure literal, which is what lets `Wrench.mk.injEq`
-- split an equality into its two components (the pattern the rest of this file proves with).
@[simp] theorem zero_def : (0 : Wrench α) = ⟨0, 0⟩ := rfl
@[simp] theorem add_def (a b : Wrench α) : a + b = ⟨a.force + b.force, a.torque + b.torque⟩ := rfl
@[simp] theorem sub_def (a b : Wrench α) : a - b = ⟨a.force - b.force, a.torque - b.torque⟩ := rfl
@[simp] theorem neg_def (a : Wrench α) : -a = ⟨-a.force, -a.torque⟩ := rfl
omit [CommRing α] in
@[simp] theorem smul_def [SMul β α] (c : β) (a : Wrench α) :
    c • a = ⟨c • a.force, c • a.torque⟩ := rfl

end Wrench

namespace Twist

instance : Zero (Twist α) := ⟨⟨0, 0⟩⟩
instance : Add (Twist α) := ⟨fun a b => ⟨a.v + b.v, a.ω + b.ω⟩⟩
instance : Sub (Twist α) := ⟨fun a b => ⟨a.v - b.v, a.ω - b.ω⟩⟩
instance : Neg (Twist α) := ⟨fun a => ⟨-a.v, -a.ω⟩⟩
instance [SMul β α] : SMul β (Twist α) := ⟨fun c a => ⟨c • a.v, c • a.ω⟩⟩

-- Projections here, not the `_def` equations `Wrench` uses: a `Twist` or `Accel` never has to be
-- split with `mk.injEq` in this file, and leaving `0` folded is what lets `comAccel_zero` below
-- match `comAccel mp 0 0` before the zeros are unfolded.
@[simp] theorem zero_v : (0 : Twist α).v = 0 := rfl
@[simp] theorem zero_ω : (0 : Twist α).ω = 0 := rfl
@[simp] theorem add_v (a b : Twist α) : (a + b).v = a.v + b.v := rfl
@[simp] theorem add_ω (a b : Twist α) : (a + b).ω = a.ω + b.ω := rfl
@[simp] theorem sub_v (a b : Twist α) : (a - b).v = a.v - b.v := rfl
@[simp] theorem sub_ω (a b : Twist α) : (a - b).ω = a.ω - b.ω := rfl
@[simp] theorem neg_v (a : Twist α) : (-a).v = -a.v := rfl
@[simp] theorem neg_ω (a : Twist α) : (-a).ω = -a.ω := rfl
omit [CommRing α] in
@[simp] theorem smul_v [SMul β α] (c : β) (a : Twist α) : (c • a).v = c • a.v := rfl
omit [CommRing α] in
@[simp] theorem smul_ω [SMul β α] (c : β) (a : Twist α) : (c • a).ω = c • a.ω := rfl

end Twist

/-! ## The cross product and the dot product, continued

`TorqueWrench` proves bilinearity in the `+` direction only, and states everything in terms of
its own `dot`. What is added here completes that API — `cross` under negation, subtraction and
scalar multiplication, the bridge from `dot` to Mathlib's `⬝ᵥ` (without which the
`triple_product_*` and `dotProduct_*` families cannot fire), and cross-equivariance through a
transposed rotation, which is what the covariance proofs push every rotation inside a cross with.
-/

/-- A scalar slides out of the first factor of a cross product. Together with `cross_smul` this
is what lets a body's mass be carried by either the vector or the cross product, which is how
the centre of mass is replaced by the first moment. -/
theorem smul_cross (r : α) (u v : Fin 3 → α) : cross (r • u) v = r • cross u v := by
  simp only [cross_eq_crossProduct, map_smul, LinearMap.smul_apply]

theorem cross_smul (r : α) (u v : Fin 3 → α) : cross u (r • v) = r • cross u v := by
  simp only [cross_eq_crossProduct, map_smul]

theorem cross_neg (u v : Fin 3 → α) : cross u (-v) = -cross u v := by
  simp only [cross_eq_crossProduct, map_neg]

theorem sub_cross (u v w : Fin 3 → α) : cross (u - v) w = cross u w - cross v w := by
  simp only [cross_eq_crossProduct, map_sub, LinearMap.sub_apply]

theorem cross_sub (u v w : Fin 3 → α) : cross u (v - w) = cross u v - cross u w := by
  simp only [cross_eq_crossProduct, map_sub]

/-- This file's `dot` is Mathlib's `⬝ᵥ`, so the vector identities stated with `⬝ᵥ`
(`triple_product_permutation`, `dot_cross_self`, …) become available for `dot`. -/
theorem dot_eq_dotProduct (u v : Fin 3 → α) : dot u v = u ⬝ᵥ v := by
  simp only [dot, dotProduct, Fin.sum_univ_three]

/-- Cross products commute with a transposed rotation, both factors rotating together. This is
`Rotation.mulVec_cross` read through the inverse rotation; unlike `transpose_mulVec_cross`,
which takes one rotated and one unrotated factor, both factors here are transposed. -/
theorem Rotation.cross_transpose (ρ : Rotation α) (u v : Fin 3 → α) :
    cross (ρ.matᵀ *ᵥ u) (ρ.matᵀ *ᵥ v) = ρ.matᵀ *ᵥ cross u v :=
  (Rotation.mulVec_cross ρ⁻¹ u v).symm

/-! ## Mass properties and accelerations

`MassProperties` describes a rigid body by its mass, its centre of mass relative to the frame
origin, and its inertia tensor about that centre of mass. The inertia is required to be
symmetric — bundling that here, as `Rotation` bundles orthogonality and determinant one, keeps
it off every caller. Unlike velocity, acceleration is *not* a frame-independent quantity: the
frames below are rigidly attached to one body, which is what makes `sensorAccelToTip` a
transport rather than a new assumption.
-/

/-- The mass distribution of a rigid body, expressed in one frame: its mass, the centre of
mass relative to the frame origin, and the inertia tensor about the centre of mass. -/
structure MassProperties (α : Type*) [CommRing α] where
  mass : α
  com : Fin 3 → α
  inertia : Matrix (Fin 3) (Fin 3) α
  inertia_symm : inertiaᵀ = inertia

/-- The acceleration of a frame: `a` is the acceleration of the frame origin's material point
and `alpha` the angular acceleration, both in that frame's coordinates. -/
structure Accel (α : Type*) where
  a : Fin 3 → α
  alpha : Fin 3 → α

namespace Accel

instance : Zero (Accel α) := ⟨⟨0, 0⟩⟩
instance : Add (Accel α) := ⟨fun x y => ⟨x.a + y.a, x.alpha + y.alpha⟩⟩
instance : Sub (Accel α) := ⟨fun x y => ⟨x.a - y.a, x.alpha - y.alpha⟩⟩
instance : Neg (Accel α) := ⟨fun x => ⟨-x.a, -x.alpha⟩⟩
instance [SMul β α] : SMul β (Accel α) := ⟨fun c x => ⟨c • x.a, c • x.alpha⟩⟩

@[simp] theorem zero_a : (0 : Accel α).a = 0 := rfl
@[simp] theorem zero_alpha : (0 : Accel α).alpha = 0 := rfl
@[simp] theorem add_a (x y : Accel α) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_alpha (x y : Accel α) : (x + y).alpha = x.alpha + y.alpha := rfl
@[simp] theorem sub_a (x y : Accel α) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_alpha (x y : Accel α) : (x - y).alpha = x.alpha - y.alpha := rfl
@[simp] theorem neg_a (x : Accel α) : (-x).a = -x.a := rfl
@[simp] theorem neg_alpha (x : Accel α) : (-x).alpha = -x.alpha := rfl
omit [CommRing α] in
@[simp] theorem smul_a [SMul β α] (c : β) (x : Accel α) : (c • x).a = c • x.a := rfl
omit [CommRing α] in
@[simp] theorem smul_alpha [SMul β α] (c : β) (x : Accel α) : (c • x).alpha = c • x.alpha := rfl

end Accel

/-! ## The inertial and gravitational wrenches

The classical Newton–Euler equations about the frame origin, written in a frame that turns
with the body: the force is `m` times the acceleration of the centre of mass, and the torque
is the inertia couple `I α + ω × (I ω)` plus the moment of the force through the lever arm
`c`. `gravityWrench` is the wrench of a uniform gravitational field acting on the body: the
force `m g` applied at the centre of mass.
-/

/-- The acceleration of the centre of mass, given the frame's twist and acceleration: the
frame origin's acceleration, plus the angular contribution `α × c`, plus the centripetal term
`ω × (ω × c)`. -/
def comAccel (mp : MassProperties α) (t : Twist α) (acc : Accel α) : Fin 3 → α :=
  acc.a + cross acc.alpha mp.com + cross t.ω (cross t.ω mp.com)

/-- The inertial wrench of a rigid body: the wrench that has to be applied to produce the
motion `(t, acc)`, i.e. minus the wrench the body's inertia exerts on its surroundings. -/
def inertialWrench (mp : MassProperties α) (t : Twist α) (acc : Accel α) : Wrench α :=
  let F := mp.mass • comAccel mp t acc
  ⟨F, mp.inertia *ᵥ acc.alpha + cross t.ω (mp.inertia *ᵥ t.ω) + cross mp.com F⟩

/-- The wrench of a uniform gravitational field `g` acting on the body: the force `m g`, applied
at the centre of mass, so its moment about the frame origin is `c × (m g)`. `g` is the
gravitational *acceleration* (pointing down), so this is the wrench gravity exerts on the body
and a sensor holding the body at rest reads its negative. -/
def gravityWrench (mp : MassProperties α) (g : Fin 3 → α) : Wrench α :=
  ⟨mp.mass • g, cross mp.com (mp.mass • g)⟩

/-- The first moment of mass `m c`: the mass times the centre of mass. It is the quantity that
adds when bodies are combined, where the centre of mass itself would need division. -/
def firstMoment (mp : MassProperties α) : Fin 3 → α :=
  mp.mass • mp.com

/-- The inertia tensor about the *frame origin* rather than about the centre of mass: the
parallel-axis shift `I_c + m (⟨c, c⟩ 1 - c cᵀ)`. This is the form in which inertias add. -/
def originInertia (mp : MassProperties α) : Matrix (Fin 3) (Fin 3) α :=
  mp.inertia + mp.mass • (dot mp.com mp.com • (1 : Matrix (Fin 3) (Fin 3) α) -
    Matrix.vecMulVec mp.com mp.com)

@[simp] theorem comAccel_zero (mp : MassProperties α) : comAccel mp 0 0 = 0 := by
  simp only [comAccel, Accel.zero_a, Accel.zero_alpha, Twist.zero_ω, cross_eq_crossProduct,
    map_zero, LinearMap.zero_apply, zero_add]

/-- A body with no motion has no inertial wrench. Together with `measuredWrench_static` this is
what makes the new theory a conservative extension of `TorqueWrench`. -/
@[simp] theorem inertialWrench_zero (mp : MassProperties α) : inertialWrench mp 0 0 = 0 := by
  simp only [inertialWrench, comAccel_zero, Accel.zero_alpha, Twist.zero_ω, smul_zero,
    Matrix.mulVec_zero, cross_eq_crossProduct, map_zero, add_zero]
  rfl

@[simp] theorem gravityWrench_zero (mp : MassProperties α) : gravityWrench mp 0 = 0 := by
  simp only [gravityWrench, smul_zero, cross_eq_crossProduct, map_zero]
  rfl

/-! ## Transporting accelerations and mass properties between frames

`TorqueWrench` transports twists; a wrench is a covector and transports by the dual map. Both
of those are *linear* in the data, which is why the twist transform never mentions
acceleration. Acceleration is different: the material point at the tip is not the material
point at the sensor origin, so its transport picks up the centripetal difference
`ω × (ω × p)` and has to be told the twist as well. Mass properties are intrinsic to the body,
so transporting them rotates the inertia tensor and moves the centre of mass.
-/

/-- The acceleration of the tip, in tip coordinates, from the sensor's twist and acceleration.
Both frames are rigidly attached to the same body, so the tip's material point has acceleration
`a + α × p + ω × (ω × p)` in sensor coordinates — the `ω × (ω × p)` term is the centripetal
difference between the two points, and dropping it is the classic acceleration frame-change
error. The result rotates back by `Rᵀ`, as the twist transport does. -/
def sensorAccelToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (t : Twist α)
    (acc : Accel α) : Accel α :=
  ⟨Rᵀ *ᵥ (acc.a + cross acc.alpha p + cross t.ω (cross t.ω p)), Rᵀ *ᵥ acc.alpha⟩

/-- The inverse of `sensorAccelToTip`: the sensor's acceleration, in sensor coordinates, from the
tip's twist and acceleration in tip coordinates. The lever arm is `p` in sensor coordinates —
the same arm `tipTwistToSensor` subtracts — combined with the angular parts rotated forward, and
the centripetal term is subtracted along with the `α × p` one. -/
def tipAccelToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (t : Twist α)
    (acc : Accel α) : Accel α :=
  ⟨R *ᵥ acc.a - cross (R *ᵥ acc.alpha) p - cross (R *ᵥ t.ω) (cross (R *ᵥ t.ω) p),
    R *ᵥ acc.alpha⟩

/-- The same body described in sensor coordinates: the mass is unchanged, the centre of mass
moves to `p + R c`, and the inertia tensor rotates as `R I Rᵀ`. The symmetry of the result is
transpose algebra alone — no orthogonality and no determinant are needed even to state it. -/
def tipMassToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (mp : MassProperties α) :
    MassProperties α where
  mass := mp.mass
  com := p + R *ᵥ mp.com
  inertia := R * mp.inertia * Rᵀ
  inertia_symm := by
    calc (R * mp.inertia * Rᵀ)ᵀ = (Rᵀ)ᵀ * (R * mp.inertia)ᵀ := Matrix.transpose_mul _ _
      _ = R * (mp.inertiaᵀ * Rᵀ) := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = R * (mp.inertia * Rᵀ) := by rw [mp.inertia_symm]
      _ = R * mp.inertia * Rᵀ := (Matrix.mul_assoc _ _ _).symm

/-- The inverse of `tipMassToSensor`: the same body described in tip coordinates, with the centre
of mass taken back to `Rᵀ (c - p)` and the inertia tensor conjugated by `Rᵀ`. -/
def sensorMassToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (mp : MassProperties α) :
    MassProperties α where
  mass := mp.mass
  com := Rᵀ *ᵥ (mp.com - p)
  inertia := Rᵀ * mp.inertia * R
  inertia_symm := by
    calc (Rᵀ * mp.inertia * R)ᵀ = Rᵀ * (Rᵀ * mp.inertia)ᵀ := Matrix.transpose_mul _ _
      _ = Rᵀ * (mp.inertiaᵀ * R) := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = Rᵀ * (mp.inertia * R) := by rw [mp.inertia_symm]
      _ = Rᵀ * mp.inertia * R := (Matrix.mul_assoc _ _ _).symm

/-- Converting a sensor acceleration down to the tip and back is lossless. Mirrors
`tipTwistToSensor_sensorTwistToTip`, including consuming the same orthogonality. -/
theorem tipAccelToSensor_sensorAccelToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : R * Rᵀ = 1) (t : Twist α) (acc : Accel α) :
    tipAccelToSensor p R (sensorTwistToTip p R t) (sensorAccelToTip p R t acc) = acc := by
  obtain ⟨a, al⟩ := acc
  simp only [sensorAccelToTip, tipAccelToSensor, sensorTwistToTip, sensorTwistToTipVelocity,
    Accel.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    abel
  · simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

/-- Converting a tip acceleration up to the sensor frame and back is lossless. -/
theorem sensorAccelToTip_tipAccelToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (t : Twist α) (acc : Accel α) :
    sensorAccelToTip p R (tipTwistToSensor p R t) (tipAccelToSensor p R t acc) = acc := by
  obtain ⟨a, al⟩ := acc
  simp only [sensorAccelToTip, tipAccelToSensor, tipTwistToSensor, Accel.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hR,
      Matrix.one_mulVec]
    abel
  · simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

/-- Converting a sensor mass description down to the tip and back is lossless. -/
theorem sensorMassToTip_tipMassToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (mp : MassProperties α) :
    sensorMassToTip p R (tipMassToSensor p R mp) = mp := by
  obtain ⟨m, c, I, hI⟩ := mp
  -- the centre of mass: `Rᵀ ((p + R c) - p) = c`
  have hcom : Rᵀ *ᵥ ((p + R *ᵥ c) - p) = c := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    abel
  -- the inertia: `Rᵀ (R I Rᵀ) R = I`, with the orthogonality used on both sides
  have hin : Rᵀ * (R * I * Rᵀ) * R = I := by
    calc Rᵀ * (R * I * Rᵀ) * R = (Rᵀ * R) * I * (Rᵀ * R) := by noncomm_ring
      _ = I := by simp only [hR, Matrix.one_mul, Matrix.mul_one]
  simp only [sensorMassToTip, tipMassToSensor, hcom, hin]

/-- Converting a tip mass description up to the sensor frame and back is lossless. -/
theorem tipMassToSensor_sensorMassToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : R * Rᵀ = 1) (mp : MassProperties α) :
    tipMassToSensor p R (sensorMassToTip p R mp) = mp := by
  obtain ⟨m, c, I, hI⟩ := mp
  have hcom : p + R *ᵥ (Rᵀ *ᵥ (c - p)) = c := by
    simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    abel
  have hin : R * (Rᵀ * I * R) * Rᵀ = I := by
    calc R * (Rᵀ * I * R) * Rᵀ = (R * Rᵀ) * I * (R * Rᵀ) := by noncomm_ring
      _ = I := by simp only [hR, Matrix.one_mul, Matrix.mul_one]
  simp only [tipMassToSensor, sensorMassToTip, hcom, hin]

/-! ## Covariance: the physics does not depend on the frame

The point of these theorems is that the model can be evaluated in whichever frame is
convenient. The inertial wrench computed from the tip-frame description of a body and motion,
transported up to the sensor, is the inertial wrench computed from the sensor-frame
description — so a controller may identify mass properties in one frame and use them in the
other.

The one step that is *not* linear is the centre of mass acceleration, which is why it is
isolated below: `a_c` of the same material point seen from the two frames agrees only up to
the rotation, and only after the lever-arm and centripetal terms cancel. Getting that step
wrong (dropping `ω × (ω × p)`, say) silently breaks every covariance statement downstream.
-/

/-- The material-point acceleration of the centre of mass is frame-independent: computed from
the sensor-frame description it is the rotation of the tip-frame one. This is the isolated
non-linear step of the covariance theorems — the two lever arms `p` (in the transform) and
`p + R c` (in the transformed centre of mass) cancel, as do the two centripetal terms. -/
theorem comAccel_transport (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (hR : Rᵀ * R = 1)
    (hd : R.det = 1) (mp : MassProperties α) (t : Twist α) (acc : Accel α) :
    comAccel (tipMassToSensor p R mp) (tipTwistToSensor p R t) (tipAccelToSensor p R t acc) =
      R *ᵥ comAccel mp t acc := by
  obtain ⟨m, c, I, hI⟩ := mp
  obtain ⟨v, om⟩ := t
  obtain ⟨a, al⟩ := acc
  simp only [comAccel, tipMassToSensor, tipTwistToSensor, tipAccelToSensor, Matrix.mulVec_add,
    cross_add, mulVec_cross R hR hd]
  abel

/-- **Covariance of the inertial wrench.** Describing a body and its motion in the sensor frame
and computing the inertial wrench there gives the same wrench as computing it in the tip frame
and transporting it up. So mass properties identified in either frame may be used in the
other. -/
theorem inertialWrench_transport (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (hd : R.det = 1) (mp : MassProperties α) (t : Twist α) (acc : Accel α) :
    tipToSensor p R (inertialWrench mp t acc) =
      inertialWrench (tipMassToSensor p R mp) (tipTwistToSensor p R t)
        (tipAccelToSensor p R t acc) := by
  -- Both sides are unfolded to wrench literals, but `tipMassToSensor` and friends must stay
  -- *folded* until `comAccel_transport` has fired: it matches on their unapplied form.
  simp only [tipToSensor, inertialWrench, Wrench.mk.injEq]
  refine ⟨?_, ?_⟩
  · -- force: the centred acceleration transports, and `m` commutes with the rotation
    rw [comAccel_transport p R hR hd mp t acc]
    simp only [tipMassToSensor, Matrix.mulVec_smul]
  · -- torque: the inertia couple conjugates (`R I Rᵀ` acting on `R α`), the gyroscopic term
    -- rotates as a cross product, and the two lever arms of `c × F` merge with `p × F`
    rw [comAccel_transport p R hR hd mp t acc]
    simp only [tipMassToSensor, tipTwistToSensor, tipAccelToSensor, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_smul, mulVec_cross R hR hd, add_cross,
      Matrix.mul_assoc, hR, Matrix.mul_one]
    abel

/-- **Covariance of the gravity wrench.** With the gravity vector rotated into the sensor frame,
the gravitational wrench transports like any other wrench applied at the centre of mass. This
is the theorem an implementation uses to get gravity into the sensor frame from a world-frame
gravity vector. -/
theorem gravityWrench_transport (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (hd : R.det = 1) (mp : MassProperties α) (g : Fin 3 → α) :
    tipToSensor p R (gravityWrench mp g) =
      gravityWrench (tipMassToSensor p R mp) (R *ᵥ g) := by
  obtain ⟨m, c, I, hI⟩ := mp
  simp only [tipToSensor, gravityWrench, tipMassToSensor, Wrench.mk.injEq, Matrix.mulVec_smul,
    mulVec_cross R hR hd, add_cross]
  refine ⟨by simp, ?_⟩
  abel

/-! ## Power, and the form in which bodies add

Two more statements belong to the model itself. The first is that the inertial wrench's power is
the classical `m a_c ⋅ v_c + α ⋅ (I ω)` — so the gyroscopic term does no work, and the algebraic
statement stands in for the calculus one (`d/dt` of kinetic energy) without needing derivatives.
The second is the parallel-axis rewrite: the torque about the frame origin is
`I_O α + ω × (I_O ω) + h × a` with `I_O` the inertia *about the origin* and `h` the first moment.
That form exposes what a body contributes — the triple `(mass, firstMoment, originInertia)` — and
that triple is additive, which is what `inertialWrench_add` and `gravityWrench_add` below need.
-/

/-- The inertia tensor is symmetric, so pairing it with `u` against `v` is the same as pairing
`u` against `I v`. This is what makes the angular power `α ⋅ (I ω)` legitimate rather than
`(I α) ⋅ ω`, and it is the only place `inertia_symm` is used. -/
theorem dot_mulVec_self (mp : MassProperties α) (u v : Fin 3 → α) :
    dot (mp.inertia *ᵥ u) v = dot u (mp.inertia *ᵥ v) := by
  calc dot (mp.inertia *ᵥ u) v = (mp.inertia *ᵥ u) ⬝ᵥ v := dot_eq_dotProduct _ _
    _ = v ⬝ᵥ (mp.inertia *ᵥ u) := dotProduct_comm _ _
    _ = (v ᵥ* mp.inertia) ⬝ᵥ u := Matrix.dotProduct_mulVec v mp.inertia u
    _ = (mp.inertiaᵀ *ᵥ v) ⬝ᵥ u := by rw [← Matrix.mulVec_transpose]
    _ = (mp.inertia *ᵥ v) ⬝ᵥ u := by rw [mp.inertia_symm]
    _ = u ⬝ᵥ (mp.inertia *ᵥ v) := dotProduct_comm _ _
    _ = dot u (mp.inertia *ᵥ v) := (dot_eq_dotProduct _ _).symm

/-- The power the inertial wrench delivers, read straight off the definition: `m` times the
centred acceleration against the centred velocity, plus `(I α) ⋅ ω`. Neither the gyroscopic term
`ω × (I ω)` nor the lever-arm term `c × F` appears — they cancel out of the power, which is what
makes this identity the algebraic stand-in for `d/dt (kinetic energy) = power`, with no
derivatives anywhere. -/
theorem virtualWork_inertialWrench_mulVec (mp : MassProperties α) (t : Twist α) (acc : Accel α) :
    virtualWork (inertialWrench mp t acc) t =
      mp.mass * dot (comAccel mp t acc) (t.v + cross t.ω mp.com)
        + dot (mp.inertia *ᵥ acc.alpha) t.ω := by
  simp only [virtualWork, inertialWrench, comAccel, dot, cross_apply_zero, cross_apply_one,
    cross_apply_two, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The same power in its classical form: the angular acceleration against the angular momentum
`I ω`. The two forms agree because the inertia tensor is symmetric (`dot_mulVec_self`). -/
theorem virtualWork_inertialWrench (mp : MassProperties α) (t : Twist α) (acc : Accel α) :
    virtualWork (inertialWrench mp t acc) t =
      mp.mass * dot (comAccel mp t acc) (t.v + cross t.ω mp.com)
        + dot acc.alpha (mp.inertia *ᵥ t.ω) := by
  rw [virtualWork_inertialWrench_mulVec, dot_mulVec_self]

/-- The power gravity delivers on a twist of the body: `m g` acting at the centre of mass, which
is `m` times `g` against the *centred* velocity `v + ω × c`. This is the rate at which
gravitational potential energy is lost, and it is also the sign check for the whole gravity
convention: a tool held still against gravity has the sensor delivering the negative of it. -/
theorem virtualWork_gravityWrench (mp : MassProperties α) (g : Fin 3 → α) (t : Twist α) :
    virtualWork (gravityWrench mp g) t = mp.mass * dot g (t.v + cross t.ω mp.com) := by
  simp only [virtualWork, gravityWrench, dot, cross_apply_zero, cross_apply_one, cross_apply_two,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The inertial wrench written in terms of the additive triple — mass, first moment and
inertia about the frame *origin* — instead of the centre of mass and the inertia about it. The
two forms are the two textbook statements of the Newton–Euler equations; this one is the one
that can be summed, because none of its three ingredients needs division to combine. -/
def spatialInertialWrench (mass : α) (firstMoment : Fin 3 → α)
    (originInertia : Matrix (Fin 3) (Fin 3) α) (t : Twist α) (acc : Accel α) : Wrench α :=
  ⟨mass • acc.a + cross acc.alpha firstMoment + cross t.ω (cross t.ω firstMoment),
    originInertia *ᵥ acc.alpha + cross t.ω (originInertia *ᵥ t.ω) + cross firstMoment acc.a⟩

/-- The gravity wrench in the additive form: the force is `m g` and the moment is `h × g`, with
`h` the first moment — the centre of mass appears only through `h`. -/
def spatialGravityWrench (mass : α) (firstMoment : Fin 3 → α) (g : Fin 3 → α) : Wrench α :=
  ⟨mass • g, cross firstMoment g⟩

/-- **Parallel axis, and the equivalence of the two Newton–Euler forms.** The inertial wrench of
a body is the spatial wrench of its additive triple, i.e. the torque about the frame origin is
`I_O α + ω × (I_O ω) + h × a` with `I_O = I_c + m (⟨c,c⟩ 1 - c cᵀ)` the inertia about the origin.
Bodies therefore contribute to the dynamics only through `(mass, firstMoment, originInertia)`. -/
theorem inertialWrench_origin_form (mp : MassProperties α) (t : Twist α) (acc : Accel α) :
    inertialWrench mp t acc =
      spatialInertialWrench mp.mass (firstMoment mp) (originInertia mp) t acc := by
  simp only [inertialWrench, spatialInertialWrench, Wrench.mk.injEq]
  refine ⟨?_, ?_⟩
  · -- force: `m (a + α × c + ω × (ω × c)) = m a + α × (m c) + ω × (ω × (m c))`
    funext k
    fin_cases k <;>
      simp only [Fin.isValue, Fin.reduceFinMk, comAccel, firstMoment, cross_apply_zero,
        cross_apply_one, cross_apply_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  · -- torque: the parallel-axis term `m (⟨c,c⟩ 1 - c cᵀ)` supplies exactly the `α × c` and
    -- `ω × (ω × c)` pieces, and `h × a = (m c) × a` matches the lever arm on the force
    -- The identity matrix enters through `one_apply` as `if i = j then 1 else 0`, which only
    -- `simp`'s evaluator (not `simp only`) can decide for `Fin` indices, so the reduction runs
    -- in two steps before the polynomial identity is closed by `ring`.
    funext k
    fin_cases k <;>
      simp only [Fin.isValue, Fin.reduceFinMk, comAccel, firstMoment, originInertia,
        cross_apply_zero, cross_apply_one, cross_apply_two, Matrix.mulVec, dotProduct, dot,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec,
        Matrix.one_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] <;>
      simp <;>
      ring

/-- The gravity wrench depends on the body only through its mass and first moment. -/
theorem gravityWrench_firstMoment (mp : MassProperties α) (g : Fin 3 → α) :
    gravityWrench mp g = spatialGravityWrench mp.mass (firstMoment mp) g := by
  simp only [gravityWrench, spatialGravityWrench, firstMoment, Wrench.mk.injEq]
  refine ⟨by simp, ?_⟩
  calc cross mp.com (mp.mass • g) = mp.mass • cross mp.com g := cross_smul _ _ _
    _ = cross (mp.mass • mp.com) g := (smul_cross _ _ _).symm

/-- The spatial inertial wrench is additive in its triple: masses, first moments and inertias
about a common origin all add. This is the composition law for rigidly attached bodies. -/
theorem spatialInertialWrench_add (m₁ m₂ : α) (h₁ h₂ : Fin 3 → α)
    (I₁ I₂ : Matrix (Fin 3) (Fin 3) α) (t : Twist α) (acc : Accel α) :
    spatialInertialWrench (m₁ + m₂) (h₁ + h₂) (I₁ + I₂) t acc =
      spatialInertialWrench m₁ h₁ I₁ t acc + spatialInertialWrench m₂ h₂ I₂ t acc := by
  simp only [spatialInertialWrench, Wrench.add_def, Wrench.mk.injEq, add_smul, add_cross,
    cross_add, Matrix.add_mulVec]
  refine ⟨?_, ?_⟩ <;> abel

theorem spatialGravityWrench_add (m₁ m₂ : α) (h₁ h₂ g : Fin 3 → α) :
    spatialGravityWrench (m₁ + m₂) (h₁ + h₂) g =
      spatialGravityWrench m₁ h₁ g + spatialGravityWrench m₂ h₂ g := by
  simp only [spatialGravityWrench, Wrench.add_def, add_smul, add_cross]


/-- **Composition.** A body described by `mp` whose mass, first moment and inertia about the
origin are the sums of those of two parts has, for the same motion, the inertial wrench that is
the sum of the parts' inertial wrenches — tool plus payload folds into one body. The hypotheses
are exactly the three additive quantities; the centre of mass itself never has to be formed,
which is why this works over any commutative ring (recovering `com` from a first moment needs
division). -/
theorem inertialWrench_add (mp₁ mp₂ mp : MassProperties α)
    (hm : mp.mass = mp₁.mass + mp₂.mass)
    (hh : firstMoment mp = firstMoment mp₁ + firstMoment mp₂)
    (hI : originInertia mp = originInertia mp₁ + originInertia mp₂)
    (t : Twist α) (acc : Accel α) :
    inertialWrench mp t acc = inertialWrench mp₁ t acc + inertialWrench mp₂ t acc := by
  rw [inertialWrench_origin_form mp, inertialWrench_origin_form mp₁,
    inertialWrench_origin_form mp₂, hm, hh, hI, spatialInertialWrench_add]

/-- The same composition law for gravity, which needs only the mass and the first moment. -/
theorem gravityWrench_add (mp₁ mp₂ mp : MassProperties α)
    (hm : mp.mass = mp₁.mass + mp₂.mass)
    (hh : firstMoment mp = firstMoment mp₁ + firstMoment mp₂) (g : Fin 3 → α) :
    gravityWrench mp g = gravityWrench mp₁ g + gravityWrench mp₂ g := by
  rw [gravityWrench_firstMoment mp, gravityWrench_firstMoment mp₁,
    gravityWrench_firstMoment mp₂, hm, hh, spatialGravityWrench_add]

/-! ## The measurement model and gravity/inertia compensation

The sensor measures the wrench transmitted through it: the contact wrench transported up to the
sensor frame, plus the inertial wrench of everything distal to it, minus the gravitational wrench
of that same body (`g` points down, and the sensor feels the load the body puts on it, which is
the reaction to gravity). Compensation runs the model backwards, and
`recoveredContactWrench_measuredWrench` proves the two are exact inverses — no approximation, no
tuning, and over the rationals it is checkable by evaluation.
-/

/-- The wrench a force/torque sensor reads, given the contact wrench applied at the tip. `mp` is
the mass distribution of everything distal to the sensor, in tip coordinates; `t`, `acc` and `g`
are the body's twist, its acceleration and the gravitational acceleration in sensor coordinates;
`contact` is the external wrench at the tip in tip coordinates. Everything is exact: this is a
model of an ideal sensor, with no bias, noise or compliance. -/
def measuredWrench (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (mp : MassProperties α)
    (t : Twist α) (acc : Accel α) (g : Fin 3 → α) (contact : Wrench α) : Wrench α :=
  tipToSensor p R contact + inertialWrench (tipMassToSensor p R mp) t acc
    - gravityWrench (tipMassToSensor p R mp) g

/-- Gravity and inertia compensation: subtract the model's inertial wrench from the measurement,
add back gravity, and transport the result down to the tip, where the contact actually is. -/
def recoveredContactWrench (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (mp : MassProperties α)
    (t : Twist α) (acc : Accel α) (g : Fin 3 → α) (measured : Wrench α) : Wrench α :=
  sensorToTip p R (measured - inertialWrench (tipMassToSensor p R mp) t acc
    + gravityWrench (tipMassToSensor p R mp) g)

/-- Adding and subtracting the same wrench, in the shape the compensation below produces it. -/
theorem add_sub_sub_add_cancel (a b c : Wrench α) : a + b - c - b + c = a := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  obtain ⟨c₁, c₂⟩ := c
  simp only [Wrench.add_def, Wrench.sub_def, Wrench.mk.injEq]
  refine ⟨?_, ?_⟩ <;> abel

/-- **Compensation is exact.** Recovering the contact wrench from a measurement the model
produced returns the wrench that was applied, for any rotation, any motion and any gravity. This
is the theorem that says the gravity and inertia terms of a real controller are *removable*: no
residual is left behind by the frame algebra itself. -/
theorem recoveredContactWrench_measuredWrench (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (mp : MassProperties α) (t : Twist α) (acc : Accel α) (g : Fin 3 → α)
    (contact : Wrench α) :
    recoveredContactWrench p R mp t acc g (measuredWrench p R mp t acc g contact) = contact := by
  simp only [recoveredContactWrench, measuredWrench, add_sub_sub_add_cancel,
    sensorToTip_tipToSensor p R hR]

/-- With no motion and no gravity the model reduces to the static transform: the new theory is a
conservative extension of `TorqueWrench`, which is what the static test data pins down. -/
theorem measuredWrench_static (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (mp : MassProperties α) (contact : Wrench α) :
    measuredWrench p R mp 0 0 0 contact = tipToSensor p R contact := by
  simp only [measuredWrench, tipToSensor, Wrench.zero_def, Wrench.add_def, Wrench.sub_def,
    inertialWrench_zero, gravityWrench_zero, add_zero, sub_zero]

/-- A tool held at rest with no contact: the sensor reads exactly the negative of the tool's
gravity wrench. This is the sign convention of the whole model in one equation, and the case the
ground-truth data checks first. -/
theorem measuredWrench_at_rest (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (mp : MassProperties α) (g : Fin 3 → α) :
    measuredWrench p R mp 0 0 g 0 = -gravityWrench (tipMassToSensor p R mp) g := by
  simp only [measuredWrench, tipToSensor, Wrench.zero_def, Wrench.add_def, Wrench.sub_def,
    Wrench.neg_def, inertialWrench_zero, Matrix.mulVec_zero, cross_eq_crossProduct, map_zero,
    add_zero, zero_sub]

/-- A free-held tool at rest: compensation recovers a zero contact wrench, since nothing is
touching it. -/
theorem recoveredContactWrench_at_rest (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (mp : MassProperties α) (g : Fin 3 → α) :
    recoveredContactWrench p R mp 0 0 g (measuredWrench p R mp 0 0 g 0) = 0 := by
  rw [recoveredContactWrench_measuredWrench p R hR mp 0 0 g 0]

/-! ## Frames in series, and the `Rotation` layer

A chain of frames has to fold: converting through a middle frame must agree with converting once
through the composed pose `(p + ρ *ᵥ q, ρ * σ)`, or an implementation could not route a
measurement along a joint chain and still use a single identified body model. `TorqueWrench`
proves this for wrenches and twists; the mass description folds the same way below.

The rest of this section repeats the `Rotation`-namespace wrappers `TorqueWrench` provides, so a
caller holding a `Rotation` never has to discharge orthogonality or the determinant by hand.
-/

/-- The matrix of a composed rotation is the product of the matrices, as an *equation*: unification
does not see through the `Mul` instance, so the chain proofs below have to rewrite with it rather
than rely on definitional equality. -/
theorem Rotation.mul_mat (ρ σ : Rotation α) : (ρ * σ).mat = ρ.mat * σ.mat := rfl

/-- Accelerations fold through a frame chain: carrying a sensor acceleration to a middle frame and
then to the tip agrees with carrying it straight to the tip through the composed pose. The two
lever arms `p` and `q` merge into `p + ρ *ᵥ q` in the centripetal terms, which is what makes the
transport an honest change of frame rather than a one-step convention. -/
theorem sensorAccelToTip_comp (ρ σ : Rotation α) (p q : Fin 3 → α) (t : Twist α)
    (acc : Accel α) :
    sensorAccelToTip q σ.mat (sensorTwistToTip p ρ.mat t) (sensorAccelToTip p ρ.mat t acc) =
      sensorAccelToTip (p + ρ.mat *ᵥ q) (ρ.mat * σ.mat) t acc := by
  obtain ⟨v, om⟩ := t
  obtain ⟨a, al⟩ := acc
  -- Both factors of every surviving cross product are rotations of a common vector, so
  -- `cross_transpose` (read backwards) can push each `σᵀ` and `(ρ σ)ᵀ` inside.
  simp only [sensorAccelToTip, sensorTwistToTip, sensorTwistToTipVelocity, Accel.mk.injEq]
  refine ⟨?_, ?_⟩
  · -- push each rotation inside the cross products it multiplies, then cancel `ρᵀ ρ` in the
    -- `q` terms, which appear as `((ρ σ)ᵀ ρ) *ᵥ q` only after those rewrites
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      ← Rotation.mul_mat, ← Rotation.cross_transpose σ, ← Rotation.cross_transpose (ρ * σ),
      cross_add]
    simp only [Rotation.mul_mat, Matrix.transpose_mul, Matrix.mul_assoc, ρ.orth,
      Matrix.mul_one]
    abel
  · -- the angular parts collapse through the composed rotation
    simp only [Matrix.mulVec_mulVec, Matrix.transpose_mul]

/-- Mass descriptions fold through a frame chain: conjugating by `σᵀ` and then by `ρᵀ` is
conjugation by `(ρ σ)ᵀ`, and the two offset shifts compose into the folded origin. -/
theorem sensorMassToTip_comp (ρ σ : Rotation α) (p q : Fin 3 → α) (mp : MassProperties α) :
    sensorMassToTip q σ.mat (sensorMassToTip p ρ.mat mp) =
      sensorMassToTip (p + ρ.mat *ᵥ q) (ρ.mat * σ.mat) mp := by
  obtain ⟨m, c, I, hI⟩ := mp
  have hcom : σ.matᵀ *ᵥ ((ρ.matᵀ *ᵥ (c - p)) - q) =
      (ρ.mat * σ.mat)ᵀ *ᵥ (c - (p + ρ.mat *ᵥ q)) := by
    simp only [Matrix.transpose_mul, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, ρ.orth, Matrix.mul_one]
    abel
  have hin : σ.matᵀ * (ρ.matᵀ * I * ρ.mat) * σ.mat = (ρ.mat * σ.mat)ᵀ * I * (ρ.mat * σ.mat) := by
    simp only [Matrix.transpose_mul]
    noncomm_ring
  simp only [sensorMassToTip, hcom, hin]

namespace Rotation

/-- Converting a sensor acceleration down to the tip and back is lossless. -/
theorem tipAccelToSensor_sensorAccelToTip (ρ : Rotation α) (p : Fin 3 → α) (t : Twist α)
    (acc : Accel α) :
    tipAccelToSensor p ρ.mat (sensorTwistToTip p ρ.mat t) (sensorAccelToTip p ρ.mat t acc) =
      acc :=
  _root_.tipAccelToSensor_sensorAccelToTip p ρ.mat
    (mul_transpose_eq_one ρ.mat ρ.orth ρ.det_eq_one) t acc

/-- Converting a tip acceleration up to the sensor frame and back is lossless. -/
theorem sensorAccelToTip_tipAccelToSensor (ρ : Rotation α) (p : Fin 3 → α) (t : Twist α)
    (acc : Accel α) :
    sensorAccelToTip p ρ.mat (tipTwistToSensor p ρ.mat t) (tipAccelToSensor p ρ.mat t acc) =
      acc :=
  _root_.sensorAccelToTip_tipAccelToSensor p ρ.mat ρ.orth t acc

/-- Converting a sensor mass description down to the tip and back is lossless. -/
theorem sensorMassToTip_tipMassToSensor (ρ : Rotation α) (p : Fin 3 → α) (mp : MassProperties α) :
    sensorMassToTip p ρ.mat (tipMassToSensor p ρ.mat mp) = mp :=
  _root_.sensorMassToTip_tipMassToSensor p ρ.mat ρ.orth mp

/-- Converting a tip mass description up to the sensor frame and back is lossless. -/
theorem tipMassToSensor_sensorMassToTip (ρ : Rotation α) (p : Fin 3 → α) (mp : MassProperties α) :
    tipMassToSensor p ρ.mat (sensorMassToTip p ρ.mat mp) = mp :=
  _root_.tipMassToSensor_sensorMassToTip p ρ.mat
    (mul_transpose_eq_one ρ.mat ρ.orth ρ.det_eq_one) mp

/-- **Covariance of the inertial wrench**, with the frame hypotheses discharged. -/
theorem inertialWrench_transport (ρ : Rotation α) (p : Fin 3 → α) (mp : MassProperties α)
    (t : Twist α) (acc : Accel α) :
    tipToSensor p ρ.mat (inertialWrench mp t acc) =
      inertialWrench (tipMassToSensor p ρ.mat mp) (tipTwistToSensor p ρ.mat t)
        (tipAccelToSensor p ρ.mat t acc) :=
  _root_.inertialWrench_transport p ρ.mat ρ.orth ρ.det_eq_one mp t acc

/-- **Covariance of the gravity wrench**, with the frame hypotheses discharged. -/
theorem gravityWrench_transport (ρ : Rotation α) (p : Fin 3 → α) (mp : MassProperties α)
    (g : Fin 3 → α) :
    tipToSensor p ρ.mat (gravityWrench mp g) =
      gravityWrench (tipMassToSensor p ρ.mat mp) (ρ.mat *ᵥ g) :=
  _root_.gravityWrench_transport p ρ.mat ρ.orth ρ.det_eq_one mp g

/-- **Gravity and inertia compensation is exact**, with the frame hypotheses discharged. -/
theorem recoveredContactWrench_measuredWrench (ρ : Rotation α) (p : Fin 3 → α)
    (mp : MassProperties α) (t : Twist α) (acc : Accel α) (g : Fin 3 → α) (contact : Wrench α) :
    recoveredContactWrench p ρ.mat mp t acc g (measuredWrench p ρ.mat mp t acc g contact) =
      contact :=
  _root_.recoveredContactWrench_measuredWrench p ρ.mat ρ.orth mp t acc g contact

end Rotation

