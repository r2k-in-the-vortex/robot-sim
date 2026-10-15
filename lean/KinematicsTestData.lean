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
public import Kinematics

open Lean (Json)
open Matrix
open scoped Matrix

@[expose] public section

/-!
# Exact ground-truth data for the forward chain

`Kinematics.lean` is the specification of the forward kinematics, as `TorqueWrench.lean` is
the specification of the force/torque algebra. This file evaluates it and writes the results
out as JSON for the Rust and Python implementations to be checked against.

Every number here is exact. The forward chain reads a joint angle only through its cosine
and sine - that is `dh_congr`, and `fk_congr` at the level of the whole pose - so supplying
those two numbers as data loses nothing, and every `alpha` in the fixed twist pattern is a
quarter turn, whose cosine and sine are `0` and `1` exactly. A joint angle given as a
Pythagorean pair such as `(4/5, 3/5)`, `(5/13, 12/13)` or `(15/17, 8/17)` therefore makes the
whole chain a polynomial with rational values, and a consumer can compare poses with `==`
rather than against a tolerance: a failing comparison is a real mistake, not drift.

`Kinematics.lean` states the chain over `ℝ`, where a pose cannot be evaluated (a general
joint angle's cosine is irrational, and `Real.cos` does not compute). The definitions below
are that file's definitions again at `ℚ` - the same six-entry `joint` table with the same
`90, 0, 90, 90, -90, 0` twists, the same product order and bracketing, the same `carrierPose`
tower including the base frame, the same `wristCenter` - with `dh` taking the cosine/sine
pair instead of the angle. This is a restatement and not an instantiation, as
`ForceTorqueTestData.lean` manages: `TorqueWrench` is polymorphic over a commutative ring
and can be instantiated at `ℚ`, while the chain is stated at `ℝ` alone. So the mirror below
is held to the specification by reading and by the invariants every case re-derives, not by
the type checker. `Kinematics` is imported anyway - the generator then re-elaborates
whenever the specification changes, rather than silently drifting from a stale copy.
The `(R, p)` view with `toMatrix4`, the `mul` it composes with,
and the lemmas the cases are checked against (`carrierPose_zero`, `carrierPose_succ`,
`carrierPose_six`, `carrierPose_four_p`, `fk_R`, `dh_toMatrix4`, `Pose.toMatrix4_mul`,
`rotX_orth`, `rotZ_orth`, `mul_orth`, `armRotation_orth`) are restated over `ℚ` in the
same shapes.

That restatement is deliberately weaker than `ForceTorqueTestData.lean`'s. There, the
specification itself is polymorphic over a commutative ring and instantiates at `ℚ`, so the
type checker holds the data to it. Here the chain is stated at `ℝ` alone, so the mirror is
held to the specification by reading and by the invariants each case re-derives - checked
outright rather than inherited. The `det = 1` half of "is a rotation" is the extreme case:
it is proved in `InverseKinematics.lean` (`fk_R_orth` alongside `fk_R_det`) rather than in
`Kinematics.lean`, so it too is re-derived here by Sarrus, as `Mat3::det` does on the Rust
side.

A case also names a geometry. `linkOne` and `linkTwo` are Lean's names for the DH table's
`a2` and `d4`, and both appear in the document under their DH names.

Regenerate the data with, from `lean/`:

    lake exe kinematics_test_data ../test_data/kinematics_frames.json

Every case is re-checked by evaluation before anything is written, and the generator
refuses to write a file if a check fails.
-/

namespace KinematicsTestData

/-- A vector in `R^3` with exact rational components. -/
abbrev Vec := Fin 3 → ℚ

/-- A 3x3 matrix with exact rational entries. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℚ

/-! ## Angles as cosine/sine pairs -/

/-- The cosine and sine of one joint angle. By `dh_congr` the pair is a complete description
of what the chain reads from the angle, and unlike the angle it is exactly representable in
`ℚ`. The pair is not required to be normalised: the chain never re-derives one entry from
the other. -/
structure CosSin where
  cos : ℚ
  sin : ℚ

/-- `(1, 0)`: the identity angle, a total joint angle of zero. -/
def identity : CosSin := ⟨1, 0⟩

/-- `(0, 1)`: the quarter turn, `Kinematics.quarter`. -/
def quarterTurn : CosSin := ⟨0, 1⟩

/-- `(-1, 0)`: a half turn. -/
def halfTurn : CosSin := ⟨-1, 0⟩

/-- `(0, -1)`: a quarter turn backwards. -/
def threeQuarterTurn : CosSin := ⟨0, -1⟩

/-- The angle `self + other`, by the addition formulas: `Real.cos_add` and `Real.sin_add`,
which is what lets `θ2 + θ3` in `armRotation` be taken on the pairs. Purely polynomial. -/
def CosSin.then (x y : CosSin) : CosSin :=
  ⟨x.cos * y.cos - x.sin * y.sin, x.sin * y.cos + x.cos * y.sin⟩

/-- The angle `-self`. -/
def CosSin.negated (x : CosSin) : CosSin := ⟨x.cos, -x.sin⟩

/-- Whether the pair lies on the unit circle, i.e. names an actual angle rather than an
arbitrary pair of rationals. Every case's pairs satisfy this, so the data describes
configurations a real arm could be in. -/
def CosSin.isNormalized (x : CosSin) : Bool := decide (x.cos * x.cos + x.sin * x.sin = 1)

/-! ## Rotations, poses and the DH transform -/

/-- Rotation about the x axis, given its cosine and sine. -/
def rotX (x : CosSin) : Mat := !![1, 0, 0; 0, x.cos, -x.sin; 0, x.sin, x.cos]

/-- Rotation about the y axis, given its cosine and sine. -/
def rotY (x : CosSin) : Mat := !![x.cos, 0, x.sin; 0, 1, 0; -x.sin, 0, x.cos]

/-- Rotation about the z axis, given its cosine and sine. -/
def rotZ (x : CosSin) : Mat := !![x.cos, -x.sin, 0; x.sin, x.cos, 0; 0, 0, 1]

/-- A rigid pose over `ℚ`. Lean's `Kinematics.Pose` with rational entries. -/
structure Pose where
  /-- The rotation carrying the frame's coordinates to the base frame. -/
  R : Mat
  /-- The frame's origin, in base coordinates. -/
  p : Vec

namespace Pose

/-- Composition, `Kinematics.Pose.mul`. -/
def mul (X Y : Pose) : Pose := ⟨X.R * Y.R, X.R *ᵥ Y.p + X.p⟩

instance : Mul Pose := ⟨mul⟩

/-- The frame coinciding with the base frame. -/
def id : Pose := ⟨1, 0⟩

instance : One Pose := ⟨id⟩

/-- The 4x4 homogeneous matrix of a pose, row-major, in the layout `mathematics.md` and
`kinematics.py` use. `Kinematics.Pose.toMatrix4`. -/
def toMatrix4 (X : Pose) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![X.R 0 0, X.R 0 1, X.R 0 2, X.p 0;
     X.R 1 0, X.R 1 1, X.R 1 2, X.p 1;
     X.R 2 0, X.R 2 1, X.R 2 2, X.p 2;
     0, 0, 0, 1]

end Pose

/-- `Pose` carries a function field, whose equality `decide` cannot be handed, so the checks
compare the two components instead. -/
def poseEq (X Y : Pose) : Bool := decide (X.R = Y.R) && decide (X.p = Y.p)

/-- The determinant, by the rule of Sarrus. `Kinematics` proves the chain's rotation
orthogonal (`armRotation_orth`) but carries no determinant theorem - `fk_R_det` lives in
`InverseKinematics.lean`, which is a library above this one, so a case here cannot cite it.
Re-deriving it by Sarrus keeps this generator self-contained; `Mat3::det` is the Rust
counterpart. -/
def det3 (M : Mat) : ℚ :=
  M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1)
    - M 0 1 * (M 1 0 * M 2 2 - M 1 2 * M 2 0)
    + M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0)

/-- Whether a matrix is a rotation: orthogonal with determinant one. The orthogonality half is
`rotX_orth`, `rotY_orth`, `rotZ_orth` and `mul_orth` - hence `armRotation_orth` - read as one
predicate; the determinant half is checked outright. -/
def matIsRotation (M : Mat) : Bool := decide (Mᵀ * M = 1) && decide (det3 M = 1)

/-- The free dimensions of the supported arm. Lean's `Kinematics.Geometry`, without the
positivity proofs: nothing below divides by a link length, so evaluation does not need
them. `linkOne` and `linkTwo` are the DH table's `a2` and `d4`. -/
structure Geometry where
  a1 : ℚ
  d1 : ℚ
  linkOne : ℚ
  linkTwo : ℚ
  toolOffset : ℚ

/-- A geometry with the name a case refers to it by. -/
structure NamedGeometry where
  name : String
  geometry : Geometry

/-- The DH parameters of one joint beyond its angle: the translation `d` along the previous
z axis, the link offset `a` along the joint's x axis, and the fixed twist `alpha`. -/
structure JointParams where
  d : ℚ
  a : ℚ
  alpha : CosSin

/-- One standard-DH transform, `Rz θ · Tz d · Tx a · Rx α`. Lean's `dh θ d a α`, with the
parameters grouped so a case's table can be written out once.

`toMatrix4` of this is the matrix `mathematics.md` writes - `dh_toMatrix4` - and
`dhMatrix4` below is that matrix transcribed from the document, so the checks compare two
independent routes to it. -/
def dh (θ : CosSin) (p : JointParams) : Pose :=
  ⟨rotZ θ * rotX p.alpha, ![p.a * θ.cos, p.a * θ.sin, p.d]⟩

/-- The DH table of the supported arm: `Kinematics.joint`'s six entries, with the fixed
`alpha` pattern `90, 0, 90, 90, -90, 0` degrees as the quarter turns `(0, 1)` and `(0, -1)`. -/
def jointParams (g : Geometry) : Fin 6 → JointParams :=
  ![⟨g.d1, g.a1, quarterTurn⟩,
    ⟨0, g.linkOne, identity⟩,
    ⟨0, 0, quarterTurn⟩,
    ⟨g.linkTwo, 0, quarterTurn⟩,
    ⟨0, 0, threeQuarterTurn⟩,
    ⟨g.toolOffset, 0, identity⟩]

/-- The six DH transforms at the given joint angles. Lean's `joint`. -/
def joint (g : Geometry) (θ : Fin 6 → CosSin) : Fin 6 → Pose :=
  fun i => dh (θ i) (jointParams g i)

/-- Frames 0 to 3: the shoulder, the upper arm and the `alpha3 = 90` twist. Lean's
`armPose`, with the same `(A1 · A2) · A3` bracketing. -/
def armPose (g : Geometry) (θ : Fin 6 → CosSin) : Pose :=
  joint g θ 0 * joint g θ 1 * joint g θ 2

/-- Frames 3 to 6: the spherical wrist. Lean's `wristPose`. -/
def wristPose (g : Geometry) (θ : Fin 6 → CosSin) : Pose :=
  joint g θ 3 * joint g θ 4 * joint g θ 5

/-- The full forward kinematics, `A1 · A2 · ⋯ · A6`. Lean's `fk`. -/
def fk (g : Geometry) (θ : Fin 6 → CosSin) : Pose := armPose g θ * wristPose g θ

/-- The cumulative frames `⁰T_0, …, ⁰T_6` of the DH chain, `⁰T_0` the base frame. Lean's
`carrierPose`, written out rather than defined by recursion. -/
def carrierPose (g : Geometry) (θ : Fin 6 → CosSin) : Fin 7 → Pose :=
  ![1,
    joint g θ 0,
    joint g θ 0 * joint g θ 1,
    armPose g θ,
    armPose g θ * joint g θ 3,
    armPose g θ * joint g θ 3 * joint g θ 4,
    armPose g θ * joint g θ 3 * joint g θ 4 * joint g θ 5]

/-- The rotation from the base frame to frame 3. Lean's `armRotation`: joints 2 and 3 turn
about the same axis, so only their sum appears - `CosSin.then`, i.e. `Real.cos_add` and
`Real.sin_add`. -/
def armRotation (θ1 θ2 θ3 : CosSin) : Mat :=
  rotZ θ1 * rotX quarterTurn * rotZ (θ2.then θ3) * rotX quarterTurn

/-- The rotation from frame 3 to frame 6, a ZYZ decomposition. Lean's `wristRotation`, whose
middle angle is `-θ5` because the `alpha4 = 90`, `alpha5 = -90` twists conjugate the z
rotations into a ball joint (`rotX_conj`). -/
def wristRotation (θ4 θ5 θ6 : CosSin) : Mat := rotZ θ4 * rotY θ5.negated * rotZ θ6

/-- A scalar multiple of a vector: `wristCenter` writes this product, and keeping it a named
function leaves `ℚ` no `SMul` instance to need. -/
def scaleVec (c : ℚ) (v : Vec) : Vec := fun i => c * v i

/-- The wrist centre: the end-effector origin pulled back along frame 6's z axis by the tool
offset. Lean's `wristCenter`, and the frame-4 origin of the tower (`carrierPose_four_p`). -/
def wristCenter (g : Geometry) (T : Pose) : Vec :=
  T.p - scaleVec g.toolOffset (T.R *ᵥ ![0, 0, 1])

/-- The written-out DH matrix of `mathematics.md` and of `dh_toMatrix4`, transcribed from
the document rather than built from the rotation product `dh` computes. The checks compare
the two routes. -/
def dhMatrix4 (θ : CosSin) (p : JointParams) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![θ.cos, -θ.sin * p.alpha.cos, θ.sin * p.alpha.sin, p.a * θ.cos;
     θ.sin, θ.cos * p.alpha.cos, -θ.cos * p.alpha.sin, p.a * θ.sin;
     0, p.alpha.sin, p.alpha.cos, p.d;
     0, 0, 0, 1]

/-! ## Conjunctions over the fixed chain lengths

Written out rather than folded over a list: the arm has exactly six joints and exactly seven
frames, and saying so literally keeps the checks below reading like the vector they check. -/

def allJoints (f : Fin 6 → Bool) : Bool := f 0 && f 1 && f 2 && f 3 && f 4 && f 5

def allFrames (f : Fin 7 → Bool) : Bool := f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6

/-- The six pairs of a configuration, in joint order. -/
def pairs (θ : Fin 6 → CosSin) : List CosSin :=
  [θ 0, θ 1, θ 2, θ 3, θ 4, θ 5]

/-- The seven frames of the tower as a list, so the JSON writer can map over them:
`allFrames` is a conjunction, not a list. -/
def frames (g : Geometry) (θ : Fin 6 → CosSin) : List Pose :=
  let tower := carrierPose g θ
  [tower 0, tower 1, tower 2, tower 3, tower 4, tower 5, tower 6]

/-! ## Geometries -/

/-- The geometry `robot_parameters.json` ships: `a1 = 10`, `d1 = 40`, `a2 = 40`, `d4 = 40`,
`d6 = 10`. -/
def shippedGeometry : Geometry := ⟨10, 40, 40, 40, 10⟩

/-- A second arm, so the generator is not accidentally hard-wired to one set of link
lengths: shorter links, a smaller tool, and `a1 = 0`, which puts the frame-1 origin on the
base rotation axis. -/
def shortArmGeometry : Geometry := ⟨0, 25, 30, 12, 4⟩

def shipped : NamedGeometry := ⟨"shipped", shippedGeometry⟩

def shortArm : NamedGeometry := ⟨"short_arm", shortArmGeometry⟩

def geometries : List NamedGeometry := [shipped, shortArm]

/-! ## Cases -/

/-- One ground-truth case: an arm and six joint angles, as cosine/sine pairs. -/
structure Case where
  name : String
  /-- The arm the case runs on. -/
  arm : NamedGeometry
  /-- The joint angles, in joint order. -/
  theta : Fin 6 → CosSin
  /-- Whether the case is a witness that the wrist centre can sit exactly on the frame-1
  origin. With equal link lengths and the second link folded back onto the first, the
  planar offsets `q` and `h` of `planarQ`/`planarH` are both zero, and `wristCenter_fk`
  puts the wrist centre exactly where the frame-1 origin is. -/
  wristCenterAtFrameOne : Bool := false

/-- The cases. The pairs are either the exactly special values `(1, 0)`, `(0, 1)`, `(-1, 0)`
and `(0, -1)`, or Pythagorean pairs, whose cosine and sine are rational by construction.
Both arms appear, and the single-joint cases move one joint at a time so a wrong sign or a
mis-indexed entry cannot hide behind the others. -/
def cases : List Case := [
  -- Every joint at total angle zero. Six turns of the DH table with nothing rotated, so
  -- this is the case that pins down the table's signs and offsets.
  { name := "identity_all_joints"
    arm := shipped
    theta := ![identity, identity, identity, identity, identity, identity] },
  -- The arm's zero pose: joint 2 carries a 90 degree static offset in
  -- `robot_parameters.json`, so the configuration the simulator opens at is not the
  -- all-identity one. The frame origins are the ones `doc/main_window_image.png` shows.
  { name := "documented_zero_pose"
    arm := shipped
    theta := ![identity, quarterTurn, identity, identity, identity, identity] },
  { name := "pythagorean_joint_one"
    arm := shipped
    theta := ![⟨4 / 5, 3 / 5⟩, identity, identity, identity, identity, identity] },
  { name := "pythagorean_joint_two"
    arm := shipped
    theta := ![identity, ⟨5 / 13, 12 / 13⟩, identity, identity, identity, identity] },
  { name := "pythagorean_joint_four"
    arm := shipped
    theta := ![identity, identity, identity, ⟨8 / 17, 15 / 17⟩, identity, identity] },
  { name := "pythagorean_joint_six"
    arm := shipped
    theta := ![identity, identity, identity, identity, identity, ⟨15 / 17, 8 / 17⟩] },
  -- Half and backward-quarter turns about the wrist's three axes, so the sign of each
  -- rotation shows up on its own.
  { name := "half_turns_on_the_wrist"
    arm := shipped
    theta := ![identity, identity, identity, halfTurn, threeQuarterTurn, halfTurn] },
  -- Every joint rotated at once, with a different Pythagorean pair on each: no entry of
  -- the pose is left equal to a clean 0, 1 or -1 that a dropped term could still produce.
  { name := "all_joints_pythagorean"
    arm := shipped
    theta := ![⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨8 / 17, 15 / 17⟩,
      ⟨3 / 5, 4 / 5⟩, ⟨12 / 13, 5 / 13⟩, ⟨15 / 17, 8 / 17⟩] },
  -- The same arm with the pairs in the other quadrants, so a sign that cancels in the case
  -- above does not cancel here.
  { name := "all_joints_pythagorean_negative"
    arm := shipped
    theta := ![⟨4 / 5, -3 / 5⟩, ⟨-5 / 13, 12 / 13⟩, ⟨8 / 17, -15 / 17⟩,
      ⟨-3 / 5, -4 / 5⟩, ⟨12 / 13, -5 / 13⟩, ⟨-15 / 17, 8 / 17⟩] },
  -- The wrist centre on the frame-1 origin: the shipped arm's links are equal, and a
  -- three-quarter turn on joint 3 folds the second link back onto the first.
  { name := "wrist_center_at_frame_one_origin"
    arm := shipped
    theta := ![⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, threeQuarterTurn, identity, identity, identity]
    wristCenterAtFrameOne := true },
  { name := "short_arm_identity"
    arm := shortArm
    theta := ![identity, identity, identity, identity, identity, identity] },
  { name := "short_arm_all_joints_pythagorean"
    arm := shortArm
    theta := ![⟨3 / 5, 4 / 5⟩, ⟨12 / 13, 5 / 13⟩, quarterTurn,
      ⟨15 / 17, 8 / 17⟩, halfTurn, ⟨4 / 5, -3 / 5⟩] }]

/-! ## Serialization -/

/-- Render a rational exactly: `3` for integers, `-3/5` otherwise. `ℚ` is normalised with a
positive denominator, so this form is unambiguous. -/
def ratStr (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

def ratJson (q : ℚ) : Json := .str (ratStr q)

def vecJson (v : Vec) : Json := .arr #[ratJson (v 0), ratJson (v 1), ratJson (v 2)]

def matJson (M : Mat) : Json :=
  .arr #[.arr #[ratJson (M 0 0), ratJson (M 0 1), ratJson (M 0 2)],
    .arr #[ratJson (M 1 0), ratJson (M 1 1), ratJson (M 1 2)],
    .arr #[ratJson (M 2 0), ratJson (M 2 1), ratJson (M 2 2)]]

def row4Json (M : Matrix (Fin 4) (Fin 4) ℚ) (i : Fin 4) : Json :=
  .arr #[ratJson (M i 0), ratJson (M i 1), ratJson (M i 2), ratJson (M i 3)]

def matrix4Json (M : Matrix (Fin 4) (Fin 4) ℚ) : Json :=
  .arr #[row4Json M 0, row4Json M 1, row4Json M 2, row4Json M 3]

def pairJson (x : CosSin) : Json := .mkObj [("cos", ratJson x.cos), ("sin", ratJson x.sin)]

def poseJson (X : Pose) : Json := .mkObj [("R", matJson X.R), ("p", vecJson X.p)]

def geometryJson (ng : NamedGeometry) : Json :=
  .mkObj [
    ("name", .str ng.name),
    ("a1", ratJson ng.geometry.a1),
    ("d1", ratJson ng.geometry.d1),
    ("a2", ratJson ng.geometry.linkOne),
    ("d4", ratJson ng.geometry.linkTwo),
    ("d6", ratJson ng.geometry.toolOffset)]

/-! ## Checks -/

/-- The invariants a case has to satisfy, re-derived by evaluation: the pairs name actual
angles, every rotation the case produces is a rotation, and the chain lemmas the consumers
rely on hold of the values about to be written. A non-empty result means the case is not
usable as ground truth. -/
def caseFailures (c : Case) : List String :=
  let g := c.arm.geometry
  let θ := c.theta
  let tower := carrierPose g θ
  let pose := fk g θ
  let center := wristCenter g pose
  (if allJoints fun i => (θ i).isNormalized then []
      else ["a joint's cosine/sine pair is not on the unit circle"])
    ++ (if allFrames (fun i => matIsRotation (tower i).R) && matIsRotation pose.R
          && matIsRotation (armRotation (θ 0) (θ 1) (θ 2))
          && matIsRotation (wristRotation (θ 3) (θ 4) (θ 5)) then []
        else ["a rotation is not a rotation"])
    ++ (if poseEq (tower 0) 1 then [] else ["the tower does not start at the base frame"])
    ++ (if allJoints (fun i => poseEq (tower i.succ) (tower i.castSucc * joint g θ i)) then []
        else ["the tower does not extend by one joint at a time"])
    ++ (if poseEq (tower 6) pose then [] else ["the sixth frame is not the forward kinematics"])
    ++ (if decide ((tower 4).p = center) then []
        else ["the fourth frame is not the wrist centre"])
    ++ (if decide (pose.R = armRotation (θ 0) (θ 1) (θ 2) * wristRotation (θ 3) (θ 4) (θ 5))
        then [] else ["the rotation does not factor through frame 3"])
    ++ (if allJoints (fun i =>
          decide ((joint g θ i).toMatrix4 = dhMatrix4 (θ i) (jointParams g i))) then []
        else ["a DH transform's homogeneous matrix is not the written-out matrix"])
    ++ (if allJoints (fun i => decide ((tower i.succ).toMatrix4
          = (tower i.castSucc).toMatrix4 * (joint g θ i).toMatrix4)) then []
        else ["the homogeneous matrices of the tower do not multiply"])
    ++ (if c.wristCenterAtFrameOne then
          (if decide (center = (tower 1).p) then []
            else ["the wrist centre is not on the frame-1 origin"])
        else [])

/-- The document-level invariant: a geometry that no case uses would be a link length set
nothing checks, and the second arm exists precisely to be checked. -/
def documentFailures : List String :=
  (geometries.filter fun ng => !cases.any fun c => c.arm.name == ng.name).map fun ng =>
    s!"geometry '{ng.name}' is not used by any case"

/-- The case as JSON: the configuration, and every quantity a consumer has to reproduce. -/
def caseJson (c : Case) : Json :=
  let g := c.arm.geometry
  let θ := c.theta
  let pose := fk g θ
  .mkObj [
    ("name", .str c.name),
    ("geometry", .str c.arm.name),
    ("wrist_center_at_frame_one", .bool c.wristCenterAtFrameOne),
    ("theta_cos_sin", .arr ((pairs θ).map pairJson).toArray),
    ("expected", .mkObj [
      ("carrier_pose", .arr ((frames g θ).map poseJson).toArray),
      ("carrier_matrix4", .arr ((frames g θ).map fun X => matrix4Json X.toMatrix4).toArray),
      ("fk", poseJson pose),
      ("wrist_center", vecJson (wristCenter g pose)),
      ("arm_rotation", matJson (armRotation (θ 0) (θ 1) (θ 2))),
      ("wrist_rotation", matJson (wristRotation (θ 3) (θ 4) (θ 5)))])]

def document : Json := .mkObj [
  ("schema_version", (1 : Json)),
  ("source", .str "lean/Kinematics.lean, evaluated over the rationals (exact)"),
  ("conventions", .str "A joint angle is given only by its cosine and sine, because the \
    chain reads an angle no other way (`dh_congr`, `fk_congr`); each `theta_cos_sin` entry \
    is a pair of exact numerals. `carrier_pose` is the tower `0T_0` to `0T_6` of \
    `Kinematics.carrierPose`, base frame first, each frame a rotation `R` and an origin `p` \
    in base coordinates, and `carrier_matrix4` is the same seven frames as 4x4 homogeneous \
    matrices, row-major, so rows are rows. `fk` is `Kinematics.fk`, the last entry of the \
    tower. `wrist_center` is `Kinematics.wristCenter` of `fk`: the frame-4 origin, which \
    `wrist_center_at_frame_one` additionally pins to the frame-1 origin in the cases that \
    set it. `arm_rotation` and `wrist_rotation` are the two factors of `fk_R`. Geometry is \
    named by the DH letters: `a2` is `Kinematics.Geometry.linkOne` and `d4` is `linkTwo`. \
    Every numeral is an exact integer or \"num/den\" string, never a JSON number."),
  ("geometries", .arr (geometries.map geometryJson).toArray),
  ("cases", .arr (cases.map caseJson).toArray)]

end KinematicsTestData

open KinematicsTestData

/-- Entry point: check every case, then write the JSON. Takes the output path as its only
argument, defaulting to `../test_data/kinematics_frames.json` (relative to `lean/`, which is
where `lake exe` is run from). Exits non-zero without writing anything if a case fails its
checks. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "../test_data/kinematics_frames.json"
  let failures := (cases.filterMap fun c =>
      match caseFailures c with
      | [] => none
      | fs => some (c.name, fs))
    ++ (if documentFailures.isEmpty then [] else [("<document>", documentFailures)])
  unless failures.isEmpty do
    IO.eprintln "refusing to write test data: a case failed its checks"
    for (name, fs) in failures do
      for f in fs do
        IO.eprintln s!"  {name}: {f}"
    return 1
  if let some dir := (System.FilePath.mk path).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path (Json.pretty document ++ "\n")
  IO.println s!"wrote {cases.length} cases over {geometries.length} geometries to {path}"
  return 0
