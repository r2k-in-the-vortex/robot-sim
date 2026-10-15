module
-- `Lean.Data.Json` itself does not re-export its `Basic`/`Printer` halves publicly, so
-- the parts whose names this file uses are imported directly.
public import Lean.Data.Json.Basic
public import Lean.Data.Json.Printer
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TorqueWrench
public import Dynamics

open Lean (Json)
open Matrix
open scoped Matrix

@[expose] public section

/-!
# Exact ground-truth data for the wrench and twist frame transforms

`TorqueWrench` states the transforms over an arbitrary commutative ring, which is what
makes them *evaluable*: this file instantiates them at `ℚ` and writes the results out as
JSON for the Python implementation to be tested against.

Every number here is exact. `ℚ` has no rounding, so the Python side can parse these with
`fractions.Fraction` and compare against its own results with `==` rather than a
tolerance — a failing comparison means a real mistake, not drift.

Rotations have to be exactly representable in `ℚ`, so a case gives a rotation as an
axis rotation by its cosine and sine, using `(0, 1)`, `(1, 0)`, `(-1, 0)` or one of the
Pythagorean pairs `(4/5, 3/5)`, `(12/13, 5/13)`, `(15/17, 8/17)`, composed as needed. An
arbitrary angle would need `cos`/`sin` and would not be rational.

The document has two sections: `cases` for the four single-hop transforms, and `chains`
for two frames in series, which the Python side has to fold into one pose.

Regenerate the data with, from `lean/`:

    lake exe force_torque_test_data ../test_data/force_torque_frames.json

Every case is re-checked by evaluation before anything is written, and the generator
refuses to write a file if a check fails.
-/

namespace ForceTorqueTestData

/-- A vector in `R^3` with exact rational components. -/
abbrev Vec := Fin 3 → ℚ

/-- A 3x3 matrix with exact rational entries. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℚ

/-! ## Rotations -/

/-- Rotation about the x axis, given its cosine and sine. -/
def rotX (c s : ℚ) : Mat := !![1, 0, 0; 0, c, -s; 0, s, c]

/-- Rotation about the y axis, given its cosine and sine. -/
def rotY (c s : ℚ) : Mat := !![c, 0, s; 0, 1, 0; -s, 0, c]

/-- Rotation about the z axis, given its cosine and sine. -/
def rotZ (c s : ℚ) : Mat := !![c, -s, 0; s, c, 0; 0, 0, 1]

/-! ## Cases -/

/-- A wrench, in whichever frame the field it is stored in refers to. -/
def wrench (force torque : Vec) : Wrench ℚ := ⟨force, torque⟩

/-- A twist, in whichever frame the field it is stored in refers to. -/
def twist (v ω : Vec) : Twist ℚ := ⟨v, ω⟩

/-- One ground-truth case: the mounting transform from the sensor frame to the tip
frame (`p` and `R` as in `TorqueWrench`), plus a wrench at the tip and twists in both
frames, so that all four transform directions can be checked. -/
structure Case where
  name : String
  /-- The tip origin, in sensor coordinates. -/
  p : Vec
  /-- The rotation from tip coordinates to sensor coordinates. -/
  R : Mat
  /-- A wrench applied at the tip, in tip coordinates. -/
  tipWrench : Wrench ℚ
  /-- A twist of the sensor, in sensor coordinates. -/
  sensorTwist : Twist ℚ
  /-- A twist of the tip, in tip coordinates. -/
  tipTwist : Twist ℚ

/-- The cases. Rotations use only exactly representable angles; the offsets, wrenches and
twists mix integers, halves, thirds and quarters so that sign errors and dropped factors
show up rather than cancelling. -/
def cases : List Case := [
  { name := "identity_no_offset"
    p := ![0, 0, 0]
    R := rotZ 1 0
    tipWrench := wrench ![1, 0, -2] ![0, 1 / 2, 0]
    sensorTwist := twist ![1 / 4, 0, 0] ![0, 0, -1]
    tipTwist := twist ![0, 1 / 2, 0] ![1, 0, 0] },
  -- Pure translation with the force across the lever arm, so the sensor torque is
  -- exactly `p × F` and nothing else. (A force parallel to `p` would make that term
  -- vanish and the case would prove nothing.)
  { name := "pure_translation_lever_arm"
    p := ![0, 0, 10]
    R := rotZ 1 0
    tipWrench := wrench ![1, 0, 0] ![0, 0, 0]
    sensorTwist := twist ![0, 0, 0] ![0, 1, 0]
    tipTwist := twist ![0, 0, 0] ![0, 1, 0] },
  { name := "identity_general_offset"
    p := ![3 / 2, -5 / 4, 2]
    R := rotZ 1 0
    tipWrench := wrench ![2, -1, 1 / 2] ![1 / 4, 0, -3 / 4]
    sensorTwist := twist ![1, 1, 0] ![-1 / 2, 1 / 3, 2]
    tipTwist := twist ![-1 / 3, 2, 1 / 2] ![3 / 4, -1, 0] },
  { name := "quarter_turn_z"
    p := ![0, 0, 0]
    R := rotZ 0 1
    tipWrench := wrench ![1, 0, 0] ![0, 1, 0]
    sensorTwist := twist ![0, 1, 0] ![1, 0, 0]
    tipTwist := twist ![1, 0, 0] ![0, -1, 0] },
  { name := "half_turn_x"
    p := ![0, 0, -3 / 2]
    R := rotX (-1) 0
    tipWrench := wrench ![0, 2, -1] ![1 / 2, -1 / 2, 1 / 2]
    sensorTwist := twist ![-1, 0, 0] ![0, -1, 0]
    tipTwist := twist ![0, 1, -1 / 2] ![0, -1, 0] },
  { name := "quarter_turn_y"
    p := ![1, 0, 0]
    R := rotY 0 1
    tipWrench := wrench ![3, -1, 2] ![0, 0, 1 / 3]
    sensorTwist := twist ![0, 1 / 2, 1 / 2] ![-1, 0, 0]
    tipTwist := twist ![1 / 2, 0, -1 / 2] ![0, 0, -1] },
  { name := "rotation_345_z_no_offset"
    p := ![0, 0, 0]
    R := rotZ (4 / 5) (3 / 5)
    tipWrench := wrench ![1, 1, 0] ![0, 0, 1]
    sensorTwist := twist ![1 / 2, 1 / 2, 0] ![0, 0, 3]
    tipTwist := twist ![0, 1, 0] ![0, 0, 3] },
  { name := "rotation_345_z_with_offset"
    p := ![1, 2, -1 / 2]
    R := rotZ (4 / 5) (3 / 5)
    tipWrench := wrench ![1, 0, -2] ![0, 1 / 2, 0]
    sensorTwist := twist ![1 / 4, -1 / 4, 0] ![0, 0, -1]
    tipTwist := twist ![1, 0, -1 / 4] ![0, 0, -1] },
  { name := "rotation_345_z_reversed"
    p := ![-1 / 3, 2 / 3, 1]
    R := rotZ (4 / 5) (-3 / 5)
    tipWrench := wrench ![-1, 2, 3] ![2 / 3, -1, 1 / 3]
    sensorTwist := twist ![0, -1 / 2, 1 / 2] ![3 / 2, 0, 0]
    tipTwist := twist ![-1 / 2, 0, 1 / 2] ![3 / 2, 0, 0] },
  { name := "rotation_5_12_13_y"
    p := ![0, 1 / 4, 3]
    R := rotY (12 / 13) (5 / 13)
    tipWrench := wrench ![3, -2, 1] ![0, 0, -2]
    sensorTwist := twist ![0, 0, 1] ![1, -1, 0]
    tipTwist := twist ![1, 0, 0] ![1, -1, 0] },
  { name := "rotation_8_15_17_x"
    p := ![-2, 0, 1 / 3]
    R := rotX (15 / 17) (8 / 17)
    tipWrench := wrench ![1 / 2, 1 / 2, 1 / 2] ![1 / 2, -1 / 2, 1 / 2]
    sensorTwist := twist ![2, -1, 0] ![0, 0, -3 / 2]
    tipTwist := twist ![2, -1 / 4, 3 / 4] ![0, 0, -3 / 2] },
  { name := "compound_z_then_y"
    p := ![1 / 2, -1 / 2, 5 / 2]
    R := rotZ (4 / 5) (3 / 5) * rotY (12 / 13) (5 / 13)
    tipWrench := wrench ![-3, 1, 2] ![1, -1, 1]
    sensorTwist := twist ![1 / 3, 1 / 3, 1 / 3] ![-1, 2, -1 / 2]
    tipTwist := twist ![0, 1, -1] ![3 / 2, -1, 1] },
  { name := "compound_x_y_z"
    p := ![3, -1, 2]
    R := rotX (15 / 17) (8 / 17) * rotY (12 / 13) (5 / 13) * rotZ (4 / 5) (3 / 5)
    tipWrench := wrench ![5, -4, 3] ![-1, 1 / 2, 2]
    sensorTwist := twist ![-1 / 2, 2, 1] ![1 / 2, -1 / 2, 1 / 2]
    tipTwist := twist ![1, 1 / 2, 0] ![-2, 1, 1 / 2] },
  { name := "zero_wrench"
    p := ![1, 1, 1]
    R := rotZ (4 / 5) (3 / 5)
    tipWrench := wrench ![0, 0, 0] ![0, 0, 0]
    sensorTwist := twist ![1, 2, 3] ![3, 2, 1]
    tipTwist := twist ![0, 0, 0] ![0, 0, 0] },
  { name := "zero_twist"
    p := ![-1, 2, -2]
    R := rotY (12 / 13) (5 / 13)
    tipWrench := wrench ![1, -1, 2] ![1 / 2, 1 / 2, -1 / 2]
    sensorTwist := twist ![0, 0, 0] ![0, 0, 0]
    tipTwist := twist ![2, 1, 1] ![-1 / 2, 1 / 2, 1] }]

/-! ## Chains

Two frames in series: the sensor frame, a middle frame, and the tip. Converting in one
step with the folded pose `(p₁ + R₁ *ᵥ p₂, R₁ * R₂)` has to agree with converting twice,
which is what `tipToSensor_comp` and `sensorTwistToTip_comp` prove. -/

/-- A chain of two frame changes with data to push through both. -/
structure Chain where
  name : String
  /-- The middle frame's origin, in sensor coordinates. -/
  p₁ : Vec
  /-- The rotation from middle coordinates to sensor coordinates. -/
  R₁ : Mat
  /-- The tip frame's origin, in middle-frame coordinates. -/
  p₂ : Vec
  /-- The rotation from tip coordinates to middle-frame coordinates. -/
  R₂ : Mat
  /-- A wrench applied at the tip, in tip coordinates. -/
  tipWrench : Wrench ℚ
  /-- A twist of the sensor, in sensor coordinates. -/
  sensorTwist : Twist ℚ

/-- The sensor-to-tip pose of a chain, folded into one step. -/
def Chain.pose (c : Chain) : Vec × Mat := (c.p₁ + c.R₁ *ᵥ c.p₂, c.R₁ * c.R₂)

def chains : List Chain := [
  { name := "chain_translation_then_345"
    p₁ := ![0, 0, 3]
    R₁ := rotZ 1 0
    p₂ := ![1 / 2, 0, -1]
    R₂ := rotZ (4 / 5) (3 / 5)
    tipWrench := wrench ![2, -1, 1] ![0, 1, -1 / 2]
    sensorTwist := twist ![1, 0, -1 / 2] ![0, 1 / 2, 2] },
  { name := "chain_345_then_51213"
    p₁ := ![1, -1 / 2, 2]
    R₁ := rotZ (4 / 5) (3 / 5)
    p₂ := ![0, 3 / 4, -2]
    R₂ := rotY (12 / 13) (5 / 13)
    tipWrench := wrench ![-1, 3, 1 / 2] ![2, -1, 1 / 3]
    sensorTwist := twist ![-1 / 2, 2, 1] ![1 / 2, -1, 3] },
  -- A half turn in the middle of the chain, so a sign error in the composition shows up.
  { name := "chain_half_turn_then_quarter_turn"
    p₁ := ![-2, 1, 1 / 2]
    R₁ := rotX (-1) 0
    p₂ := ![0, 0, -3]
    R₂ := rotZ 0 1
    tipWrench := wrench ![0, 2, -1] ![1 / 2, 0, -3 / 2]
    sensorTwist := twist ![1 / 2, -1, 0] ![0, 2, -1 / 2] }]

/-! ## Serialization -/

/-- Render a rational exactly: `3` for integers, `-3/5` otherwise. `ℚ` is normalised
with a positive denominator, so this form is unambiguous, and Python's
`fractions.Fraction` parses both shapes. -/
def ratStr (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

def ratJson (q : ℚ) : Json := .str (ratStr q)

def vecJson (v : Vec) : Json := .arr #[ratJson (v 0), ratJson (v 1), ratJson (v 2)]

def matJson (R : Mat) : Json :=
  .arr #[.arr #[ratJson (R 0 0), ratJson (R 0 1), ratJson (R 0 2)],
    .arr #[ratJson (R 1 0), ratJson (R 1 1), ratJson (R 1 2)],
    .arr #[ratJson (R 2 0), ratJson (R 2 1), ratJson (R 2 2)]]

def wrenchJson (w : Wrench ℚ) : Json :=
  .mkObj [("force", vecJson w.force), ("torque", vecJson w.torque)]

def twistJson (t : Twist ℚ) : Json :=
  .mkObj [("v", vecJson t.v), ("omega", vecJson t.ω)]

/-! ## Checks -/

/-- `Wrench` and `Twist` do not carry `DecidableEq`, so the checks compare components. -/
def wrenchEq (a b : Wrench ℚ) : Bool :=
  decide (a.force = b.force) && decide (a.torque = b.torque)

def twistEq (a b : Twist ℚ) : Bool :=
  decide (a.v = b.v) && decide (a.ω = b.ω)

/-- The invariants a case has to satisfy, re-derived by evaluation. A non-empty result
means the case is not usable as ground truth. -/
def caseFailures (c : Case) : List String :=
  let sensorWrench := tipToSensor c.p c.R c.tipWrench
  let tipTwist := sensorTwistToTip c.p c.R c.sensorTwist
  let workSensor := virtualWork sensorWrench c.sensorTwist
  let workTip := virtualWork c.tipWrench tipTwist
  (if c.Rᵀ * c.R = 1 then [] else ["R is not a rotation"])
    ++ (if workSensor = workTip then []
        else [s!"virtual work differs: {ratStr workSensor} at the sensor, \
          {ratStr workTip} at the tip"])
    ++ (if wrenchEq (sensorToTip c.p c.R sensorWrench) c.tipWrench then []
        else ["sensorToTip did not recover the tip wrench"])
    ++ (if twistEq (tipTwistToSensor c.p c.R tipTwist) c.sensorTwist then []
        else ["tipTwistToSensor did not recover the sensor twist"])
    ++ (if twistEq (tipTwistToSensor c.p c.R (sensorTwistToTip c.p c.R c.tipTwist))
          c.tipTwist then []
        else ["the tip twist round trip through the sensor frame is not the identity"])

/-- The invariants a chain has to satisfy. -/
def chainFailures (c : Chain) : List String :=
  let (p, R) := c.pose
  let oneStep := tipToSensor p R c.tipWrench
  let twoStep := tipToSensor c.p₁ c.R₁ (tipToSensor c.p₂ c.R₂ c.tipWrench)
  let twistOne := sensorTwistToTip p R c.sensorTwist
  let twistTwo := sensorTwistToTip c.p₂ c.R₂ (sensorTwistToTip c.p₁ c.R₁ c.sensorTwist)
  (if c.R₁ᵀ * c.R₁ = 1 ∧ c.R₂ᵀ * c.R₂ = 1 then [] else ["a link is not a rotation"])
    ++ (if Rᵀ * R = 1 then [] else ["the folded pose is not a rotation"])
    ++ (if wrenchEq oneStep twoStep then [] else ["the wrench routes disagree"])
    ++ (if twistEq twistOne twistTwo then [] else ["the twist routes disagree"])

/-- The case as JSON: the inputs, and every quantity the Python implementation has to
reproduce. -/
def caseJson (c : Case) : Json :=
  let sensorWrench := tipToSensor c.p c.R c.tipWrench
  let tipTwist := sensorTwistToTip c.p c.R c.sensorTwist
  .mkObj [
    ("name", .str c.name),
    ("p", vecJson c.p),
    ("R", matJson c.R),
    ("tip_wrench", wrenchJson c.tipWrench),
    ("sensor_twist", twistJson c.sensorTwist),
    ("tip_twist", twistJson c.tipTwist),
    ("expected", .mkObj [
      ("sensor_wrench", wrenchJson sensorWrench),
      ("tip_twist_from_sensor", twistJson tipTwist),
      ("tip_velocity_in_sensor_frame", vecJson (sensorTwistToTipVelocity c.p c.sensorTwist)),
      ("sensor_to_tip_wrench", wrenchJson (sensorToTip c.p c.R sensorWrench)),
      ("sensor_twist_from_tip", twistJson (tipTwistToSensor c.p c.R c.tipTwist)),
      ("virtual_work_sensor_frame", ratJson (virtualWork sensorWrench c.sensorTwist)),
      ("virtual_work_tip_frame", ratJson (virtualWork c.tipWrench tipTwist))])]

def chainJson (c : Chain) : Json :=
  let (p, R) := c.pose
  .mkObj [
    ("name", .str c.name),
    ("p1", vecJson c.p₁),
    ("R1", matJson c.R₁),
    ("p2", vecJson c.p₂),
    ("R2", matJson c.R₂),
    ("tip_wrench", wrenchJson c.tipWrench),
    ("sensor_twist", twistJson c.sensorTwist),
    ("expected", .mkObj [
      ("composed_p", vecJson p),
      ("composed_R", matJson R),
      ("sensor_wrench_one_step", wrenchJson (tipToSensor p R c.tipWrench)),
      ("sensor_wrench_two_steps", wrenchJson (tipToSensor c.p₁ c.R₁ (tipToSensor c.p₂ c.R₂ c.tipWrench))),
      ("tip_twist_one_step", twistJson (sensorTwistToTip p R c.sensorTwist)),
      ("tip_twist_two_steps", twistJson (sensorTwistToTip c.p₂ c.R₂ (sensorTwistToTip c.p₁ c.R₁ c.sensorTwist)))])]

/-! ## Dynamics cases

The static cases above cover the frame algebra. These cover the measurement model: a body distal
to the sensor (mass, centre of mass, inertia), its motion and a gravitational acceleration in
sensor coordinates, and a contact wrench at the tip. What is stored is what the model *predicts*,
including both sides of the covariance identity, the parallel-axis form, the power identities and
the recovered contact wrench, so that a Python implementation can recompute every number from the
same inputs and be compared exactly.

The case list is chosen so that a wrong sign or a missing term cannot pass: gravity alone at rest
(the sensor reads minus the gravity wrench), an off-centre centre of mass under pure acceleration,
a purely centripetal motion, a gyroscopic torque from an anisotropic inertia, a non-diagonal
inertia, and a body assembled from two parts.
-/

/-- A symmetric inertia tensor from its six independent entries. -/
def symInertia (i₁₁ i₁₂ i₁₃ i₂₂ i₂₃ i₃₃ : ℚ) : Mat :=
  !![i₁₁, i₁₂, i₁₃; i₁₂, i₂₂, i₂₃; i₁₃, i₂₃, i₃₃]

theorem symInertia_symm (i₁₁ i₁₂ i₁₃ i₂₂ i₂₃ i₃₃ : ℚ) :
    (symInertia i₁₁ i₁₂ i₁₃ i₂₂ i₂₃ i₃₃)ᵀ = symInertia i₁₁ i₁₂ i₁₃ i₂₂ i₂₃ i₃₃ := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [symInertia, Matrix.transpose_apply]

/-- A body: mass, centre of mass relative to the frame origin, and inertia about the centre of
mass, given by its six independent entries so that symmetry is by construction. -/
def body (mass : ℚ) (com : Vec) (i₁₁ i₁₂ i₁₃ i₂₂ i₂₃ i₃₃ : ℚ) : MassProperties ℚ :=
  ⟨mass, com, symInertia i₁₁ i₁₂ i₁₃ i₂₂ i₂₃ i₃₃, symInertia_symm ..⟩

/-- An acceleration, as the model's `Accel`. -/
def accel (a alpha : Vec) : Accel ℚ := ⟨a, alpha⟩

/-- An `Accel` has no `DecidableEq`, so the checks compare components. -/
def accelEq (a b : Accel ℚ) : Bool := decide (a.a = b.a) && decide (a.alpha = b.alpha)

/-- One dynamics case: the body, its motion and gravity in sensor coordinates, and a contact
wrench at the tip in tip coordinates. `parts`, when given, names two bodies this one claims to be
the rigid combination of. -/
structure DynamicsCase where
  name : String
  /-- The tip origin, in sensor coordinates. -/
  p : Vec
  /-- The rotation from tip coordinates to sensor coordinates. -/
  R : Mat
  /-- The body distal to the sensor, in tip coordinates. -/
  mp : MassProperties ℚ
  /-- The gravitational acceleration, in sensor coordinates. -/
  g : Vec
  /-- The body's twist, in sensor coordinates. -/
  sensorTwist : Twist ℚ
  /-- The body's acceleration, in sensor coordinates. -/
  sensorAccel : Accel ℚ
  /-- The external wrench at the tip, in tip coordinates. -/
  tipWrench : Wrench ℚ
  /-- Two bodies whose combination this one is, when the case exercises composition. -/
  parts : Option (MassProperties ℚ × MassProperties ℚ) := none

/-- The dynamics cases. Masses, centres of mass and inertias are small rationals, and the
motions are chosen one effect at a time (gravity only, centripetal only, gyroscopic only,
off-centre acceleration) plus full-motion cases where everything is non-zero at once. -/
def dynamicsCases : List DynamicsCase := [
  -- No motion, no contact: the sensor reads exactly the negative of the gravity wrench, and
  -- compensation recovers nothing. This is the case a sign error in gravity fails.
  { name := "rest_gravity_only"
    p := ![0, 0, 3 / 2]
    R := rotZ 1 0
    mp := body 2 ![1 / 4, 0, -1 / 2] 1 0 0 (3 / 2) 0 (5 / 2)
    g := ![0, 0, -981 / 100]
    sensorTwist := twist ![0, 0, 0] ![0, 0, 0]
    sensorAccel := accel ![0, 0, 0] ![0, 0, 0]
    tipWrench := wrench ![0, 0, 0] ![0, 0, 0] },
  -- The same, rotated, with the gravity vector and the body off the frame axes: a dropped `R`
  -- on `g` or on the centre of mass shows up here.
  { name := "rest_gravity_rotated"
    p := ![-1 / 2, 1, 2]
    R := rotZ (4 / 5) (3 / 5) * rotY (12 / 13) (5 / 13)
    mp := body (3 / 2) ![1 / 3, -2, 1 / 2] (7 / 4) (1 / 2) (-1 / 3) (5 / 2) (2 / 3) (11 / 4)
    g := ![-1, 2, -9]
    sensorTwist := twist ![0, 0, 0] ![0, 0, 0]
    sensorAccel := accel ![0, 0, 0] ![0, 0, 0]
    tipWrench := wrench ![0, 0, 0] ![0, 0, 0] },
  -- Static contact through a rotated, offset mounting: gravity plus inertia compensation has to
  -- return the applied wrench exactly, which is the whole point of the model.
  { name := "rest_gravity_with_contact"
    p := ![1, -1 / 2, 3]
    R := rotX (15 / 17) (8 / 17)
    mp := body 2 ![-3 / 4, 1 / 2, 1] 2 (1 / 4) 0 (5 / 2) (-1 / 2) 3
    g := ![1 / 2, 0, -49 / 5]
    sensorTwist := twist ![0, 0, 0] ![0, 0, 0]
    sensorAccel := accel ![0, 0, 0] ![0, 0, 0]
    tipWrench := wrench ![3, -2, 1] ![1 / 2, 1, -1 / 3] },
  -- Pure spin with no linear or angular acceleration: the only force is the centripetal
  -- `m ω × (ω × c)`, which a model that drops the centripetal term reports as zero.
  { name := "centripetal_only"
    p := ![1 / 2, 1, -1]
    R := rotY (12 / 13) (5 / 13)
    mp := body 3 ![1, -1 / 2, 2] 1 0 0 2 0 4
    g := ![0, 0, 0]
    sensorTwist := twist ![0, 0, 0] ![1, -2, 1 / 2]
    sensorAccel := accel ![0, 0, 0] ![0, 0, 0]
    tipWrench := wrench ![0, 0, 0] ![0, 0, 0] },
  -- Spin about a non-principal axis with a non-isotropic inertia: the torque is the gyroscopic
  -- `ω × (I ω)`, which a model that forgets it reports as zero.
  { name := "gyroscopic_only"
    p := ![0, 0, 0]
    R := rotZ 1 0
    mp := body 1 ![0, 0, 0] 2 0 0 1 0 (1 / 2)
    g := ![0, 0, 0]
    sensorTwist := twist ![0, 0, 0] ![1, 1, 0]
    sensorAccel := accel ![0, 0, 0] ![0, 0, 0]
    tipWrench := wrench ![0, 0, 0] ![0, 0, 0] },
  -- Pure linear acceleration of an off-centre body: force `m a`, torque `c × (m a)`.
  { name := "off_center_accelerating"
    p := ![2, 0, -1 / 2]
    R := rotX (15 / 17) (8 / 17) * rotZ (4 / 5) (3 / 5)
    mp := body (5 / 2) ![1 / 2, 3 / 4, -1] 2 (1 / 3) 0 (7 / 2) 0 (3 / 4)
    g := ![0, 0, 0]
    sensorTwist := twist ![0, 0, 0] ![0, 0, 0]
    sensorAccel := accel ![3 / 2, -1, 2] ![0, 0, 0]
    tipWrench := wrench ![0, 0, 0] ![0, 0, 0] },
  -- Everything at once: a general rotation, an off-axis centre of mass, a non-diagonal inertia,
  -- a general twist and acceleration, and gravity.
  { name := "full_motion_rotated"
    p := ![-3 / 2, 2, 1]
    R := rotZ (4 / 5) (3 / 5) * rotY (12 / 13) (5 / 13) * rotX (15 / 17) (8 / 17)
    mp := body 2 ![1 / 3, 1 / 2, -3 / 4] (5 / 2) (1 / 3) (-1 / 2) 4 (2 / 3) (7 / 2)
    g := ![1, 1 / 2, -10]
    sensorTwist := twist ![1 / 2, -1, 2] ![-3 / 4, 1 / 3, 1]
    sensorAccel := accel ![2, 1 / 2, -1] ![1 / 3, -2, 1 / 2]
    tipWrench := wrench ![2, -3, 1] ![-1 / 2, 1 / 3, 3 / 2] },
  { name := "full_motion_identity"
    p := ![1, 1, 1]
    R := rotZ 1 0
    mp := body 1 ![-1, 2, 1 / 2] 1 (1 / 2) 0 2 (1 / 3) (3 / 2)
    g := ![0, 0, -5]
    sensorTwist := twist ![1, 2, 3] ![1, 2, 3]
    sensorAccel := accel ![3, 2, 1] ![-1, -2, -3]
    tipWrench := wrench ![1, 1, 1] ![1, 1, 1] },
  -- A point mass: no inertia couple at all, so the torque is only `c × F`.
  { name := "zero_inertia"
    p := ![1 / 2, -1, 2]
    R := rotY (12 / 13) (5 / 13)
    mp := body 2 ![3 / 4, 1 / 2, -1 / 4] 0 0 0 0 0 0
    g := ![0, 0, -4]
    sensorTwist := twist ![1, 0, -1] ![0, 1, 0]
    sensorAccel := accel ![1, 1, 1] ![0, 0, 1 / 2]
    tipWrench := wrench ![1, -1, 2] ![0, 1, 0] },
  -- No motion and no gravity: the measurement is the plain static transform.
  { name := "zero_motion"
    p := ![-2, 1, 1 / 2]
    R := rotZ (4 / 5) (-3 / 5)
    mp := body 3 ![1, 1, 1] 1 0 0 1 0 1
    g := ![0, 0, 0]
    sensorTwist := twist ![0, 0, 0] ![0, 0, 0]
    sensorAccel := accel ![0, 0, 0] ![0, 0, 0]
    tipWrench := wrench ![-1, 2, 3] ![1 / 2, -1, 0] },
  -- Two bodies and their rigid combination: the composite's mass, first moment and inertia about
  -- the origin are the sums of the parts', and so are its wrenches.
  -- Two unit cubes of mass 2 at `(1,0,0)` and `(0,1,0)`: the combination sits at `(1/2,1/2,0)`
  -- with mass 4 and inertia `[[3,1,0],[1,3,0],[0,0,4]]` about its own centre, so all three
  -- additive quantities are exact rationals rather than approximations.
  { name := "composition_tool_payload"
    p := ![1, 0, -1]
    R := rotZ (4 / 5) (3 / 5)
    mp := body 4 ![1 / 2, 1 / 2, 0] 3 1 0 3 0 4
    g := ![0, 1, -5]
    sensorTwist := twist ![1 / 2, 1, -1 / 2] ![2, -1, 1 / 3]
    sensorAccel := accel ![-1, 1 / 2, 2] ![1, 1 / 2, -1]
    tipWrench := wrench ![1, 2, -1] ![0, 1 / 2, 1]
    parts := some (body 2 ![1, 0, 0] 1 0 0 1 0 1, body 2 ![0, 1, 0] 1 0 0 1 0 1) }]

/-- The invariants a dynamics case has to satisfy, re-derived by evaluation: the two sides of the
covariance theorems, the parallel-axis form, both power identities, and exact recovery of the
contact wrench. -/
def dynamicsFailures (c : DynamicsCase) : List String :=
  let mpS := tipMassToSensor c.p c.R c.mp
  let tipTwist := sensorTwistToTip c.p c.R c.sensorTwist
  let tipAccel := sensorAccelToTip c.p c.R c.sensorTwist c.sensorAccel
  let tipInertial := inertialWrench c.mp tipTwist tipAccel
  let sensorInertial := inertialWrench mpS c.sensorTwist c.sensorAccel
  let tipGravity := gravityWrench c.mp (c.Rᵀ *ᵥ c.g)
  let sensorGravity := gravityWrench mpS c.g
  let measured := measuredWrench c.p c.R c.mp c.sensorTwist c.sensorAccel c.g c.tipWrench
  let recovered := recoveredContactWrench c.p c.R c.mp c.sensorTwist c.sensorAccel c.g measured
  let powerInertial := virtualWork (inertialWrench c.mp tipTwist tipAccel) tipTwist
  let powerGravity := virtualWork (gravityWrench c.mp (c.Rᵀ *ᵥ c.g)) tipTwist
  (if c.Rᵀ * c.R = 1 ∧ c.R.det = 1 then [] else ["R is not a rotation"])
    ++ (if accelEq (sensorAccelToTip c.p c.R (tipTwistToSensor c.p c.R tipTwist)
          (tipAccelToSensor c.p c.R tipTwist tipAccel)) tipAccel then []
        else ["the acceleration transform does not round trip"])
    ++ (if wrenchEq (tipToSensor c.p c.R tipInertial) sensorInertial then []
        else ["the inertial wrench does not transport between the frames"])
    ++ (if wrenchEq (tipToSensor c.p c.R tipGravity) sensorGravity then []
        else ["the gravity wrench does not transport between the frames"])
    ++ (if wrenchEq tipInertial
          (spatialInertialWrench c.mp.mass (firstMoment c.mp) (originInertia c.mp) tipTwist
            tipAccel) then []
        else ["the origin form of the inertial wrench disagrees with the centre-of-mass form"])
    ++ (if powerInertial = c.mp.mass *
          dot (comAccel c.mp tipTwist tipAccel) (tipTwist.v + cross tipTwist.ω c.mp.com)
          + dot tipAccel.alpha (c.mp.inertia *ᵥ tipTwist.ω) then []
        else ["the inertial power identity fails"])
    ++ (if powerGravity = c.mp.mass *
          dot (c.Rᵀ *ᵥ c.g) (tipTwist.v + cross tipTwist.ω c.mp.com) then []
        else ["the gravity power identity fails"])
    ++ (if wrenchEq recovered c.tipWrench then []
        else ["compensation did not recover the contact wrench"])
    ++ (match c.parts with
        | none => []
        | some (mp₁, mp₂) =>
          (if c.mp.mass = mp₁.mass + mp₂.mass then []
            else ["the composite mass is not the sum of the parts"])
            ++ (if firstMoment c.mp = firstMoment mp₁ + firstMoment mp₂ then []
                else ["the composite first moment is not the sum of the parts"])
            ++ (if originInertia c.mp = originInertia mp₁ + originInertia mp₂ then []
                else ["the composite inertia about the origin is not the sum of the parts"])
            ++ (if wrenchEq tipInertial (inertialWrench mp₁ tipTwist tipAccel +
                  inertialWrench mp₂ tipTwist tipAccel) then []
                else ["the inertial wrench is not additive in the parts"])
            ++ (if wrenchEq (gravityWrench c.mp (c.Rᵀ *ᵥ c.g))
                  (gravityWrench mp₁ (c.Rᵀ *ᵥ c.g) + gravityWrench mp₂ (c.Rᵀ *ᵥ c.g)) then []
                else ["the gravity wrench is not additive in the parts"]))

/-- The case as JSON: the inputs, and every quantity the Python implementation has to reproduce. -/
def massJson (mp : MassProperties ℚ) : Json :=
  .mkObj [("mass", ratJson mp.mass), ("com", vecJson mp.com), ("inertia", matJson mp.inertia)]

def accelJson (x : Accel ℚ) : Json := .mkObj [("a", vecJson x.a), ("alpha", vecJson x.alpha)]

def dynamicsCaseJson (c : DynamicsCase) : Json :=
  let mpS := tipMassToSensor c.p c.R c.mp
  let tipTwist := sensorTwistToTip c.p c.R c.sensorTwist
  let tipAccel := sensorAccelToTip c.p c.R c.sensorTwist c.sensorAccel
  let tipInertial := inertialWrench c.mp tipTwist tipAccel
  let powerInertial := virtualWork tipInertial tipTwist
  let powerGravity := virtualWork (gravityWrench c.mp (c.Rᵀ *ᵥ c.g)) tipTwist
  .mkObj [
    ("name", .str c.name),
    ("p", vecJson c.p),
    ("R", matJson c.R),
    ("mass_properties", massJson c.mp),
    ("gravity", vecJson c.g),
    ("sensor_twist", twistJson c.sensorTwist),
    ("sensor_accel", accelJson c.sensorAccel),
    ("tip_wrench", wrenchJson c.tipWrench),
    ("parts", match c.parts with
      | none => .null
      | some (mp₁, mp₂) => .arr #[massJson mp₁, massJson mp₂]),
    ("expected", .mkObj [
      ("mass_properties_in_sensor_frame", massJson mpS),
      ("tip_twist", twistJson tipTwist),
      ("tip_accel", accelJson tipAccel),
      ("com_accel", vecJson (comAccel c.mp tipTwist tipAccel)),
      ("first_moment", vecJson (firstMoment c.mp)),
      ("origin_inertia", matJson (originInertia c.mp)),
      ("inertial_wrench", wrenchJson (inertialWrench mpS c.sensorTwist c.sensorAccel)),
      ("inertial_wrench_from_tip", wrenchJson (tipToSensor c.p c.R tipInertial)),
      ("gravity_wrench", wrenchJson (gravityWrench mpS c.g)),
      ("gravity_wrench_from_tip", wrenchJson (tipToSensor c.p c.R (gravityWrench c.mp (c.Rᵀ *ᵥ c.g)))),
      ("power_inertial_work", ratJson powerInertial),
      ("power_inertial_formula", ratJson (c.mp.mass *
        dot (comAccel c.mp tipTwist tipAccel) (tipTwist.v + cross tipTwist.ω c.mp.com)
        + dot tipAccel.alpha (c.mp.inertia *ᵥ tipTwist.ω))),
      ("power_gravity_work", ratJson powerGravity),
      ("power_gravity_formula", ratJson (c.mp.mass *
        dot (c.Rᵀ *ᵥ c.g) (tipTwist.v + cross tipTwist.ω c.mp.com))),
      ("measured_wrench", wrenchJson (measuredWrench c.p c.R c.mp c.sensorTwist c.sensorAccel c.g c.tipWrench)),
      ("recovered_contact_wrench", wrenchJson (recoveredContactWrench c.p c.R c.mp c.sensorTwist
        c.sensorAccel c.g (measuredWrench c.p c.R c.mp c.sensorTwist c.sensorAccel c.g c.tipWrench)))])]

def document : Json := .mkObj [
  ("schema_version", (3 : Json)),
  ("source", .str "lean/TorqueWrench.lean and lean/Dynamics.lean, evaluated over the rationals \
    (exact)"),
  ("conventions", .str "R rotates tip coordinates into sensor coordinates, p is the tip \
    origin in sensor coordinates, rows are row-major so `R i j` is Python `R[i][j]`, and \
    every numeral is an exact integer or \"num/den\" string. In dynamics cases the mass \
    properties are given in tip coordinates, the twist, acceleration and gravity in sensor \
    coordinates, the tip wrench is the external wrench at the tip in tip coordinates, and the \
    gravity vector is the gravitational acceleration (pointing down), so a sensor holding a \
    body at rest reads minus its gravity wrench."),
  ("cases", .arr (cases.map caseJson).toArray),
  ("chains", .arr (chains.map chainJson).toArray),
  ("dynamics_cases", .arr (dynamicsCases.map dynamicsCaseJson).toArray)]

end ForceTorqueTestData

open ForceTorqueTestData

/-- Entry point: check every case, then write the JSON. Takes the output path as its
only argument, defaulting to `../test_data/force_torque_frames.json` (relative to
`lean/`, which is where `lake exe` is run from). Exits non-zero without writing anything
if a case fails its checks. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "../test_data/force_torque_frames.json"
  let failures := (cases.filterMap fun c =>
      match caseFailures c with
      | [] => none
      | fs => some (c.name, fs))
    ++ (chains.filterMap fun c =>
      match chainFailures c with
      | [] => none
      | fs => some (c.name, fs))
    ++ (dynamicsCases.filterMap fun c =>
      match dynamicsFailures c with
      | [] => none
      | fs => some (c.name, fs))
  unless failures.isEmpty do
    IO.eprintln "refusing to write test data: a case failed its checks"
    for (name, fs) in failures do
      for f in fs do
        IO.eprintln s!"  {name}: {f}"
    return 1
  if let some dir := (System.FilePath.mk path).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path (Json.pretty document ++ "\n")
  IO.println s!"wrote {cases.length} cases, {chains.length} chains and \
    {dynamicsCases.length} dynamics cases to {path}"
  return 0
