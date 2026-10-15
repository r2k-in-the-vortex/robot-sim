module
-- These are `public import`s because the declarations below are exported
-- (`@[expose] public section`): everything their types and bodies mention has to
-- be part of this module's public interface, or importers cannot use them.
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

open Matrix
open scoped Matrix

noncomputable section

-- The entry-by-entry chain computations below expand deeply nested sums; the default
-- recursion budget is not enough for the six-factor products.
set_option maxRecDepth 10000

@[expose] public section

/-!
# Forward kinematics of the six-axis arm

This file is the Lean specification of `mathematics.md`'s forward kinematics and of
`kinematics.py`'s `dh_transform_standard` / `forward_kinematics`, as `TorqueWrench.lean` is
the specification of the force/torque algebra. `InverseKinematics.lean` carries the
closed-form solver and the theorems about it.

A pose is kept as a rotation and a translation rather than a 4x4 homogeneous matrix —
`Pose.toMatrix4` proves the two views agree, so the spec still literally matches the matrix
in `mathematics.md`, but the algebra stays in 3x3 blocks where `ring` is effective.

The arm's structure is the one `kinematics.py`'s `_validate_supported_geometry` accepts:
`alpha` of `90, 0, 90, 90, -90, 0` degrees with `a3 = a4 = a5 = a6 = 0` and
`d2 = d3 = d5 = 0`, leaving `a1`, `d1`, `a2` (the first link), `d4` (the second link, which
`alpha3` turns into a link perpendicular to the joint-4 axis) and `d6` free.

Angles here are **total DH angles**: the joint's static theta offset is already folded in,
exactly as `theta_i` appears in `mathematics.md`. `kinematics.py` keeps the offset separate
and reports `wrap(total - offset)`; that split is a change of variable and does not affect
anything proved here. The solver's returned angles are also normalised into `(-pi, pi]` by
its `_wrap_angle`; every statement below is modulo a full turn, so the normalisation is
invisible to it.
-/

namespace Kinematics

/-! ## Poses -/

/-- A rigid pose: the rotation carrying a frame's coordinates to the base frame, and its
origin expressed in the base frame. -/
structure Pose where
  R : Matrix (Fin 3) (Fin 3) ℝ
  p : Fin 3 → ℝ

namespace Pose

/-- Composition: `X * Y` is `X` after `Y`, so `(X * Y).p` places `Y`'s origin by `X`. -/
def mul (X Y : Pose) : Pose := ⟨X.R * Y.R, X.R *ᵥ Y.p + X.p⟩

instance : Mul Pose := ⟨mul⟩

/-- The frame coinciding with the base frame. -/
def id : Pose := ⟨1, 0⟩

instance : One Pose := ⟨id⟩

-- The projections are definitional, which is what lets `simp` see through the `Mul` and
-- `One` instances: unfolding an instance is not something `simp only` does on its own.
@[simp] theorem mul_R (X Y : Pose) : (X * Y).R = X.R * Y.R := rfl
@[simp] theorem mul_p (X Y : Pose) : (X * Y).p = X.R *ᵥ Y.p + X.p := rfl
@[simp] theorem one_R : (1 : Pose).R = 1 := rfl
@[simp] theorem one_p : (1 : Pose).p = 0 := rfl

/-- The 4x4 homogeneous matrix of a pose, in the row-major layout `mathematics.md` uses. -/
def toMatrix4 (X : Pose) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![X.R 0 0, X.R 0 1, X.R 0 2, X.p 0;
     X.R 1 0, X.R 1 1, X.R 1 2, X.p 1;
     X.R 2 0, X.R 2 1, X.R 2 2, X.p 2;
     0, 0, 0, 1]

/-- The homogeneous matrix of a composition is the product of the matrices, which is the
whole point of carrying the translation alongside the rotation. -/
theorem toMatrix4_mul (X Y : Pose) :
    (X * Y).toMatrix4 = X.toMatrix4 * Y.toMatrix4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix4, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_three]

@[ext] theorem ext {X Y : Pose} (hR : X.R = Y.R) (hp : X.p = Y.p) : X = Y := by
  cases X; cases Y; simp_all

/-- A pose is determined by its homogeneous matrix: the top-left 3x3 block of `X.toMatrix4` is
`X.R` and its last column is `X.p`, so together with `toMatrix4_mul` this says that the `(R, p)`
view and `mathematics.md`'s 4x4 view carry the same data in both directions. -/
theorem toMatrix4_eq_iff {X Y : Pose} : X.toMatrix4 = Y.toMatrix4 ↔ X = Y := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have entry : ∀ i j : Fin 4, X.toMatrix4 i j = Y.toMatrix4 i j :=
    fun i j => congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) h
  -- The matrix literal computes at literal indices, so the block and the column are read back
  -- out entry by entry rather than through a lemma about arbitrary indices.
  have block : ∀ (M : Pose) (i j : Fin 3), M.toMatrix4 i.castSucc j.castSucc = M.R i j := by
    intro M i j
    fin_cases i <;> fin_cases j <;> rfl
  have col : ∀ (M : Pose) (i : Fin 3), M.toMatrix4 i.castSucc 3 = M.p i := by
    intro M i
    fin_cases i <;> rfl
  refine Pose.ext ?_ ?_
  · ext i j
    rw [← block X i j, ← block Y i j]
    exact entry i.castSucc j.castSucc
  · funext i
    rw [← col X i, ← col Y i]
    exact entry i.castSucc 3

theorem mul_assoc (X Y Z : Pose) : X * Y * Z = X * (Y * Z) := by
  ext <;>
    simp only [mul_R, mul_p, Pi.add_apply, Matrix.mul_assoc, mulVec_mulVec,
      Matrix.mulVec_add, add_assoc]

theorem one_mul (X : Pose) : 1 * X = X := by
  ext <;> simp only [mul_R, mul_p, one_R, one_p, Pi.add_apply, Pi.zero_apply,
    Matrix.one_mul, Matrix.one_mulVec]; abel

theorem mul_one (X : Pose) : X * 1 = X := by
  ext <;> simp only [mul_R, mul_p, one_R, one_p, Pi.add_apply, Pi.zero_apply,
    Matrix.mul_one, Matrix.mulVec_zero]; abel

end Pose

/-! ## The three elementary rotations -/

/-- Rotation about the x axis by `α`. -/
def rotX (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos α, -Real.sin α; 0, Real.sin α, Real.cos α]

/-- Rotation about the y axis by `θ`. -/
def rotY (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, 0, Real.sin θ; 0, 1, 0; -Real.sin θ, 0, Real.cos θ]

/-- Rotation about the z axis by `θ`. -/
def rotZ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

-- The quarter turn is kept as an opaque name: `simp` would otherwise rewrite `pi / 2` into
-- `pi * 2⁻¹` underneath a `rotX` and the values below would stop matching. The four values
-- are everything the proofs about the arm's fixed twists actually need.
/-- A quarter turn: the twist shared by `alpha1`, `alpha3` and `alpha4`. -/
def quarter : ℝ := Real.pi / 2

@[simp] theorem cos_quarter : Real.cos quarter = 0 := by simp [quarter]
@[simp] theorem sin_quarter : Real.sin quarter = 1 := by simp [quarter]
@[simp] theorem cos_neg_quarter : Real.cos (-quarter) = 0 := by simp [quarter]
@[simp] theorem sin_neg_quarter : Real.sin (-quarter) = -1 := by simp [quarter]

@[simp] theorem rotX_zero : rotX 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotX]

@[simp] theorem rotY_zero : rotY 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotY]

@[simp] theorem rotZ_zero : rotZ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ]

/-- Rotations about a fixed axis add. -/
theorem rotZ_add (θ φ : ℝ) : rotZ θ * rotZ φ = rotZ (θ + φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;>
    ring

theorem rotX_orth (α : ℝ) : (rotX α)ᵀ * rotX α = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotX, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp

theorem rotY_orth (θ : ℝ) : (rotY θ)ᵀ * rotY θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp

theorem rotZ_orth (θ : ℝ) : (rotZ θ)ᵀ * rotZ θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp

/-- The components of a literal three-vector, so that `simp only` can read them without
having to reduce `Fin` indices itself. -/
@[simp] theorem vec3_zero (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 0 = a := rfl
@[simp] theorem vec3_one (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 1 = b := rfl
@[simp] theorem vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

/-- The identity `alpha4 = 90` and `alpha5 = -90` degrees encode: a z rotation conjugated by
the quarter turn about x is a rotation about `y` with the opposite sign. This is what makes
the spherical wrist a ZYZ ball joint. -/
theorem rotX_conj (φ : ℝ) :
    rotX quarter * rotZ φ * rotX (-quarter) = rotY (-φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotX, rotY, rotZ, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_neg,
      Real.sin_neg]

/-! ## The DH transform -/

/-- The free dimensions of the supported arm. The `alpha` pattern and the zero entries of
the DH table are fixed; these are the values `_validate_supported_geometry` leaves open. -/
structure Geometry where
  /-- Base offset `a1`: the frame-1 origin sits this far off the base rotation axis. -/
  a1 : ℝ
  /-- Base height `d1`. -/
  d1 : ℝ
  /-- First link length, `a2`. Positive: the planar solve divides by it. -/
  linkOne : ℝ
  /-- Second link length, `d4`. Positive. -/
  linkTwo : ℝ
  /-- Tool offset `d6` along frame 6's z axis. -/
  toolOffset : ℝ
  linkOne_pos : 0 < linkOne
  linkTwo_pos : 0 < linkTwo

/-- The translation part of a DH transform: `a` along the frame's x axis after the `θ`
turn, and `d` along the previous z axis. Naming it keeps its components available as
scalars, so later proofs never have to read a literal vector's entries. -/
def dhP (θ d a : ℝ) : Fin 3 → ℝ := ![a * Real.cos θ, a * Real.sin θ, d]

@[simp] theorem dhP_zero (θ d a : ℝ) : dhP θ d a 0 = a * Real.cos θ := rfl
@[simp] theorem dhP_one (θ d a : ℝ) : dhP θ d a 1 = a * Real.sin θ := rfl
@[simp] theorem dhP_two (θ d a : ℝ) : dhP θ d a 2 = d := rfl

/-- With `a = 0` the DH translation runs purely along the previous z axis. -/
theorem dhP_a_zero (θ d : ℝ) : dhP θ d 0 = ![0, 0, d] := by
  funext i
  fin_cases i <;> simp [dhP]

/-- One standard-DH transform, `Rz θ · Tz d · Tx a · Rx α`.

`Pose.toMatrix4` of this is the matrix written out in `mathematics.md`, entry for entry -
see `dh_toMatrix4`. -/
def dh (θ d a α : ℝ) : Pose := ⟨rotZ θ * rotX α, dhP θ d a⟩

/-- `dh` written out as the homogeneous matrix of `mathematics.md` and of
`kinematics.py`'s `dh_transform_standard`. -/
theorem dh_toMatrix4 (θ d a α : ℝ) :
    (dh θ d a α).toMatrix4 =
      !![Real.cos θ, -Real.sin θ * Real.cos α, Real.sin θ * Real.sin α, a * Real.cos θ;
         Real.sin θ, Real.cos θ * Real.cos α, -Real.cos θ * Real.sin α, a * Real.sin θ;
         0, Real.sin α, Real.cos α, d;
         0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dh, dhP, Pose.toMatrix4, rotZ, rotX]

variable (g : Geometry) (θ : Fin 6 → ℝ)

/-- Only the angle's cosine and sine are ever read, which is what lets the inverse solver
be stated modulo a full turn. -/
theorem dh_congr {θ θ' d a α : ℝ} (hc : Real.cos θ = Real.cos θ')
    (hs : Real.sin θ = Real.sin θ') : dh θ d a α = dh θ' d a α := by
  refine Pose.ext ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [dh, rotZ, rotX, hc, hs]
  · funext i
    fin_cases i <;> simp [dh, dhP, hc, hs]

/-! ## The chain -/

/-- The six DH transforms at the given total joint angles. The twists are the arm's fixed
`90, 0, 90, 90, -90, 0` degrees. -/
def joint : Fin 6 → Pose :=
  ![dh (θ 0) g.d1 g.a1 quarter,
    dh (θ 1) 0 g.linkOne 0,
    dh (θ 2) 0 0 quarter,
    dh (θ 3) g.linkTwo 0 quarter,
    dh (θ 4) 0 0 (-quarter),
    dh (θ 5) g.toolOffset 0 0]

/-- Frames 0 to 3: the shoulder, the upper arm and the `alpha3 = 90` twist that turns the
`d4` offset into a planar second link. -/
def armPose : Pose := joint g θ 0 * joint g θ 1 * joint g θ 2

/-- Frames 3 to 6: the spherical wrist, whose three axes meet at the frame-4 origin. -/
def wristPose : Pose := joint g θ 3 * joint g θ 4 * joint g θ 5

/-- The full forward kinematics, `A1 · A2 · … · A6`. This is what `forward_kinematics`
returns in its last entry. -/
def fk : Pose := armPose g θ * wristPose g θ

/-- The rotation from the base frame to frame 3. Joints 2 and 3 rotate about the same axis,
so only their sum appears. -/
def armRotation (θ1 θ2 θ3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rotZ θ1 * rotX quarter * rotZ (θ2 + θ3) * rotX quarter

/-- The rotation from frame 3 to frame 6: a ZYZ decomposition, because joints 4, 5 and 6 are
a spherical wrist. -/
def wristRotation (θ4 θ5 θ6 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rotZ θ4 * rotY (-θ5) * rotZ θ6

-- The chain lemmas are computed entry by entry rather than by reassociating the matrix
-- product: after `ring` every entry is a trigonometric polynomial, and the proof then does
-- not depend on how the product happens to be bracketed.
theorem armPose_R : (armPose g θ).R = armRotation (θ 0) (θ 1) (θ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [armPose, armRotation, joint, dh, Pose.mul_R, rotZ, rotX, Matrix.mul_apply,
      Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;>
    ring

theorem wristPose_R : (wristPose g θ).R = wristRotation (θ 3) (θ 4) (θ 5) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wristPose, wristRotation, joint, dh, Pose.mul_R, rotZ, rotX, rotY,
      Matrix.mul_apply, Fin.sum_univ_three, Real.cos_neg, Real.sin_neg]

/-- `R_0^6` factors through frame 3, which is what lets the wrist be solved from the `R_3^6`
the solver builds out of the target pose. -/
theorem fk_R : (fk g θ).R =
    armRotation (θ 0) (θ 1) (θ 2) * wristRotation (θ 3) (θ 4) (θ 5) := by
  simp only [fk, Pose.mul_R, armPose_R g θ, wristPose_R g θ]

/-- A product of two rotations is a rotation. Stated for two factors so that a long chain
folds one step at a time, which keeps the reassociation out of the caller. -/
theorem mul_orth {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (A * B)ᵀ * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc (Bᵀ) (Aᵀ) (A * B), ← Matrix.mul_assoc (Aᵀ) A B,
    hA, Matrix.one_mul, hB]

theorem armRotation_orth (θ1 θ2 θ3 : ℝ) :
    (armRotation θ1 θ2 θ3)ᵀ * armRotation θ1 θ2 θ3 = 1 := by
  simp only [armRotation]
  rw [mul_orth (mul_orth (mul_orth (rotZ_orth θ1) (rotX_orth quarter))
    (rotZ_orth (θ2 + θ3))) (rotX_orth quarter)]

/-- Frame 3's z axis in base coordinates: the direction of the `d4` link. -/
def armAxis (θ1 θ2 θ3 : ℝ) : Fin 3 → ℝ :=
  ![Real.sin (θ2 + θ3) * Real.cos θ1, Real.sin (θ2 + θ3) * Real.sin θ1,
    -Real.cos (θ2 + θ3)]

@[simp] theorem armAxis_zero (θ1 θ2 θ3 : ℝ) :
    armAxis θ1 θ2 θ3 0 = Real.sin (θ2 + θ3) * Real.cos θ1 := rfl
@[simp] theorem armAxis_one (θ1 θ2 θ3 : ℝ) :
    armAxis θ1 θ2 θ3 1 = Real.sin (θ2 + θ3) * Real.sin θ1 := rfl
@[simp] theorem armAxis_two (θ1 θ2 θ3 : ℝ) :
    armAxis θ1 θ2 θ3 2 = -Real.cos (θ2 + θ3) := rfl

/-- The third column of `armRotation` is `armAxis`. -/
theorem armRotation_mulVec_axis (θ1 θ2 θ3 : ℝ) :
    armRotation θ1 θ2 θ3 *ᵥ ![0, 0, 1] = armAxis θ1 θ2 θ3 := by
  ext i
  fin_cases i <;>
    simp [armRotation, armAxis, rotZ, rotX, mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    ring

/-! ## Where the wrist centre is

`p4` is the shared origin of frames 4 and 5 - the point all three wrist axes pass through.
`InverseKinematics.lean` recovers it from the target pose as `p6 - d6 · (third column of
R_0^6)`: `alpha6 = 0` and `a6 = 0` make frame 6's z axis frame 5's z axis, so the `d6` tool
offset is exactly the vector from the frame-4 origin to the end-effector origin.
-/

/-- The wrist centre read off a pose: the end-effector origin pulled back along frame 6's
z axis. `a6 = 0`, so only the `d6` term appears.

`T.R *ᵥ ![0, 0, 1]` is frame 6's z axis, i.e. the third column of `T.R` - the same thing
`kinematics.py` reads as `target_pose[axis][2]`. -/
def wristCenter (T : Pose) : Fin 3 → ℝ :=
  T.p - g.toolOffset • (T.R *ᵥ ![0, 0, 1])

/-! ## The planar reduction

Frames 2 to 4 form a planar two-link chain once `alpha3 = 90` has turned the `d4` offset into
a link perpendicular to the joint-4 axis. Writing `ψ = θ3 - π/2` for the second link's
direction relative to the first, the frame-4 origin relative to the frame-1 origin is
`(q, h)` in the plane that joint 1 has swung to:

    q = L2 cos θ2 + L4 cos (θ2 + ψ),   h = L2 sin θ2 + L4 sin (θ2 + ψ).

The solver reads `q` and `h` back out of the wrist centre, and the two useful rearrangements
are that `(q, h)` is `(u, v)` turned by `θ2` with `u = L2 + L4 cos ψ`, `v = L4 sin ψ`, and
that `q² + h² = u² + v²`.
-/

/-- The second link's direction relative to the first: the third joint's angle less the
quarter turn. In `mathematics.md`'s 1-based numbering that joint is `theta3`, so in this
file's 0-based `θ` it is `θ 2` - the joint `kinematics.py` reports as `total_theta3 =
psi + pi/2`. -/
def psi : ℝ := θ 2 - quarter

/-- The second link's direction in terms of the joint angles themselves: the matrix product
produces `theta2 + theta3`, and `psi = theta3 - pi/2` differs from it by the quarter turn. -/
theorem cos_psi (x : ℝ) : Real.cos (x + (θ 2 - quarter)) = Real.sin (x + θ 2) := by
  rw [show x + (θ 2 - quarter) = (x + θ 2) - quarter by ring, sub_eq_add_neg, Real.cos_add,
    Real.cos_neg, Real.sin_neg, cos_quarter, sin_quarter]
  ring

theorem sin_psi (x : ℝ) : Real.sin (x + (θ 2 - quarter)) = -Real.cos (x + θ 2) := by
  rw [show x + (θ 2 - quarter) = (x + θ 2) - quarter by ring, sub_eq_add_neg, Real.sin_add,
    Real.cos_neg, Real.sin_neg, cos_quarter, sin_quarter]
  ring

/-- Signed planar offset of the wrist centre along the arm plane's radial direction. -/
def planarQ : ℝ := g.linkOne * Real.cos (θ 1) + g.linkTwo * Real.cos (θ 1 + psi θ)

/-- Signed planar offset of the wrist centre along the vertical. -/
def planarH : ℝ := g.linkOne * Real.sin (θ 1) + g.linkTwo * Real.sin (θ 1 + psi θ)

/-- `(u, v)` is the planar target expressed relative to the second link rather than the
first: `(q, h)` is this turned by `θ2`. -/
def planarU : ℝ := g.linkOne + g.linkTwo * Real.cos (psi θ)

def planarV : ℝ := g.linkTwo * Real.sin (psi θ)

/-- The z axis is fixed by a z rotation. -/
theorem rotZ_mulVec_axis (θ : ℝ) : rotZ θ *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [rotZ, mulVec, dotProduct, Fin.sum_univ_three]

/-- A `d` translation along the z axis is a multiple of the axis, so a matrix only has to be
applied to the axis itself.

Not a `simp` lemma: at `c = 1` its left-hand side matches its own right-hand side, and `simp`
would loop. Rewrite with it. -/
theorem mulVec_axis_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) :
    M *ᵥ ![0, 0, c] = c • (M *ᵥ ![0, 0, 1]) := by
  rw [show (![0, 0, c] : Fin 3 → ℝ) = c • ![0, 0, 1] from by
    ext i
    fin_cases i <;> simp, Matrix.mulVec_smul]

/-- Frame 5's z axis in frame-4 coordinates: the direction the `d6` tool offset points. -/
def toolAxis (θ4 : ℝ) : Fin 3 → ℝ := ![-(Real.sin θ4), Real.cos θ4, 0]

@[simp] theorem toolAxis_zero (θ4 : ℝ) : toolAxis θ4 0 = -Real.sin θ4 := rfl
@[simp] theorem toolAxis_one (θ4 : ℝ) : toolAxis θ4 1 = Real.cos θ4 := rfl
@[simp] theorem toolAxis_two (θ4 : ℝ) : toolAxis θ4 2 = 0 := rfl

-- One lemma per joint, so a later proof rewrites a single component rather than unfolding the
-- six-element vector of poses.
theorem joint_zero_p : (joint g θ 0).p = dhP (θ 0) g.d1 g.a1 := by simp [joint, dh]
theorem joint_one_p : (joint g θ 1).p = dhP (θ 1) 0 g.linkOne := by simp [joint, dh]
theorem joint_two_p : (joint g θ 2).p = 0 := by
  funext i
  fin_cases i <;> simp [joint, dh, dhP]
theorem joint_three_p : (joint g θ 3).p = dhP (θ 3) g.linkTwo 0 := by simp [joint, dh]
theorem joint_four_p : (joint g θ 4).p = 0 := by
  funext i
  fin_cases i <;> simp [joint, dh, dhP]
theorem joint_five_p : (joint g θ 5).p = dhP (θ 5) g.toolOffset 0 := by simp [joint, dh]
theorem joint_zero_R : (joint g θ 0).R = rotZ (θ 0) * rotX quarter := by simp [joint, dh]
theorem joint_one_R : (joint g θ 1).R = rotZ (θ 1) := by simp [joint, dh]
theorem joint_two_R : (joint g θ 2).R = rotZ (θ 2) * rotX quarter := by simp [joint, dh]
theorem joint_three_R : (joint g θ 3).R = rotZ (θ 3) * rotX quarter := by simp [joint, dh]
theorem joint_four_R : (joint g θ 4).R = rotZ (θ 4) * rotX (-quarter) := by simp [joint, dh]
theorem joint_five_R : (joint g θ 5).R = rotZ (θ 5) := by simp [joint, dh]

-- The same one-step-at-a-time route for the chain: each lemma carries one factor of the
-- `Pose` product through `Pose.mul_p`/`Pose.mul_R` and lands on a named vector, so no later
-- proof has to index a literal.
/-- Frame 5's z axis in frame-4 coordinates: what `alpha5 = -90` turns `toolAxis` into. -/
theorem joint_four_mulVec_axis :
    (joint g θ 4).R *ᵥ ![0, 0, 1] = toolAxis (θ 4) := by
  ext i
  fin_cases i <;>
    simp [joint_four_R, toolAxis, rotZ, rotX, mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- Frame 6's z axis is frame 5's z axis - joint 6 turns about it - carried into frame 3. -/
theorem wristPose_mulVec_axis :
    (wristPose g θ).R *ᵥ ![0, 0, 1] = (joint g θ 3).R *ᵥ toolAxis (θ 4) := by
  simp only [wristPose, Pose.mul_R]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, joint_five_R, rotZ_mulVec_axis,
    joint_four_mulVec_axis]

/-- The wrist's translation: `d6` along the tool axis, plus `d4` along frame 3's z axis. -/
theorem wristPose_p :
    (wristPose g θ).p =
      g.toolOffset • ((joint g θ 3).R *ᵥ toolAxis (θ 4)) + ![0, 0, g.linkTwo] := by
  simp only [wristPose, Pose.mul_p, Pose.mul_R, joint_three_p, joint_four_p, joint_five_p,
    dhP_a_zero, Matrix.mulVec_zero, zero_add]
  rw [← Matrix.mulVec_mulVec, mulVec_axis_smul, joint_four_mulVec_axis, Matrix.mulVec_smul]

/-- The first link's offset in base coordinates: frame 1's plane, swung by the base joint. -/
theorem joint_zero_mulVec_joint_one_p :
    (joint g θ 0).R *ᵥ (joint g θ 1).p =
      ![g.linkOne * Real.cos (θ 1) * Real.cos (θ 0),
        g.linkOne * Real.cos (θ 1) * Real.sin (θ 0),
        g.linkOne * Real.sin (θ 1)] := by
  ext i
  fin_cases i <;>
    simp [joint_zero_R, joint_one_p, dhP, rotZ, rotX, mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    ring

/-- `armPose`'s translation: joint 2 contributes no offset of its own. -/
theorem armPose_p :
    (armPose g θ).p = (joint g θ 0).R *ᵥ (joint g θ 1).p + (joint g θ 0).p := by
  simp only [armPose, Pose.mul_p, joint_two_p, Matrix.mulVec_zero, zero_add]

/-! ## The wrist-centre identity

`wristCenter g (fk g θ)` - the end-effector origin pulled back `d6` along frame 6's z axis -
is the frame-4 origin, whose base coordinates are `(a1 + q) cos θ1`, `(a1 + q) sin θ1`,
`d1 + h`, with `q` and `h` the planar reduction's `planarQ` and `planarH`.
`InverseKinematics.lean` needs exactly this to feed the solver.
-/

/-- The wrist centre is the frame-4 origin: frame 6's z axis is frame 5's z axis, so the `d6`
tool offset cancels against itself, leaving frame 3's origin plus `d4` along frame 3's z
axis. -/
theorem wristCenter_fk_frameFour :
    wristCenter g (fk g θ) = (armPose g θ).R *ᵥ ![0, 0, g.linkTwo] + (armPose g θ).p := by
  simp only [wristCenter, fk, Pose.mul_R, Pose.mul_p]
  rw [← Matrix.mulVec_mulVec, wristPose_mulVec_axis, wristPose_p, Matrix.mulVec_add,
    Matrix.mulVec_smul]
  abel

/-- The wrist centre in base coordinates: the planar offsets `q` and `h` of the planar
reduction, placed in the plane joint 1 has swung to. -/
theorem wristCenter_fk : wristCenter g (fk g θ) =
    ![(g.a1 + planarQ g θ) * Real.cos (θ 0),
      (g.a1 + planarQ g θ) * Real.sin (θ 0),
      g.d1 + planarH g θ] := by
  rw [wristCenter_fk_frameFour, armPose_R, mulVec_axis_smul, armRotation_mulVec_axis,
    armPose_p]
  -- Full `simp`, not `simp only`: the component lemmas are stated with literal `Fin` indices,
  -- and `simp only` cannot match those against the `Fin.mk` indices `fin_cases` leaves behind.
  funext i
  fin_cases i <;>
    simp [joint_zero_mulVec_joint_one_p, joint_zero_p, dhP, armAxis, planarQ, planarH, psi,
      cos_psi, sin_psi] <;>
    ring

theorem planarQ_eq : planarQ g θ =
    planarU g θ * Real.cos (θ 1) - planarV g θ * Real.sin (θ 1) := by
  simp only [planarQ, planarU, planarV, psi, Real.cos_add]
  ring

theorem planarH_eq : planarH g θ =
    planarU g θ * Real.sin (θ 1) + planarV g θ * Real.cos (θ 1) := by
  simp only [planarH, planarU, planarV, psi, Real.sin_add]
  ring

/-- The planar distance from the frame-1 origin to the wrist centre is the length of
`(u, v)`; it is what the elbow's law of cosines is stated in terms of. -/
theorem planarQ_sq_add_planarH_sq :
    planarQ g θ ^ 2 + planarH g θ ^ 2 = planarU g θ ^ 2 + planarV g θ ^ 2 := by
  rw [planarQ_eq, planarH_eq]
  nlinarith [Real.sin_sq_add_cos_sq (θ 1)]

/-! ## The cumulative frames

`mathematics.md` writes `⁰T_i = A_1 ⋯ A_i` for frame `i` expressed in the base frame, and
`kinematics.py`'s `forward_kinematics` returns exactly that tower - the simulator draws the origin
`⁰p_i` of each entry and reads the end-effector pose off the last one. `carrierPose` is that tower
as a single vector, including the base frame `⁰T_0 = 1`.
-/

/-- The cumulative frames `⁰T_i` of the DH chain, `i = 0, …, 6`: `⁰T_0` is the base frame and
`⁰T_i = A_1 * ⋯ * A_i` is frame `i` in base coordinates, so `(carrierPose g θ i).p` is the `⁰p_i`
`mathematics.md` records for `i = 1, …, 6`. Written out rather than defined by recursion, so that
`carrierPose_succ` is a computation on the literal vector instead of an induction carrying `Fin`
arithmetic. -/
def carrierPose (g : Geometry) (θ : Fin 6 → ℝ) : Fin 7 → Pose :=
  ![1,
    joint g θ 0,
    joint g θ 0 * joint g θ 1,
    armPose g θ,
    armPose g θ * joint g θ 3,
    armPose g θ * joint g θ 3 * joint g θ 4,
    armPose g θ * joint g θ 3 * joint g θ 4 * joint g θ 5]

/-- The base of the tower: `⁰T_0` is the frame coinciding with the base frame. -/
theorem carrierPose_zero (g : Geometry) (θ : Fin 6 → ℝ) : carrierPose g θ 0 = 1 := rfl

/-- One more joint transform extends the chain by one frame: `⁰T_{i+1} = ⁰T_i * A_{i+1}`. This is
the recurrence `mathematics.md` defines the products by, recorded for the literal vector so that
every frame in it is reachable from the base frame one joint at a time.

The `i = 0` case is `1 * A_1 = A_1`, which is why `Pose.one_mul` is in the rewrite set. -/
theorem carrierPose_succ (g : Geometry) (θ : Fin 6 → ℝ) (i : Fin 6) :
    carrierPose g θ i.succ = carrierPose g θ i.castSucc * joint g θ i := by
  fin_cases i <;>
    -- Full `simp`, not `simp only`: the vector entries sit behind literal `Fin.mk` indices, which
    -- the `cons_val` simproc and the `cons_val_*` lemmas reduce but a fixed rewrite set does not.
    simp [carrierPose, armPose, Pose.one_mul]

/-- The sixth cumulative frame is the forward kinematics: `⁰T_6 = A_1 * ⋯ * A_6`, the pose
`forward_kinematics` reports in its last entry and `fk` abbreviates. -/
theorem carrierPose_six (g : Geometry) (θ : Fin 6 → ℝ) : carrierPose g θ 6 = fk g θ := by
  -- Full `simp` for the literal vector index, and `Pose.mul_assoc` alone for the rest: both sides
  -- reassociate to the same right-nested product, `fk`'s `wristPose` pair included.
  simp [carrierPose, fk, wristPose, armPose, Pose.mul_assoc]

/-- The frame-4 origin of the chain is the wrist centre of the solver: `⁰T_4` extends `⁰T_3` by
the joint-4 transform, whose only translation is `d4` along frame 3's z axis, and that is exactly
the offset `wristCenter g (fk g θ)` removes from the end-effector origin. This is the identity
`InverseKinematics.lean` feeds the solver, read off the frame tower the simulator draws. -/
theorem carrierPose_four_p (g : Geometry) (θ : Fin 6 → ℝ) :
    (carrierPose g θ 4).p = wristCenter g (fk g θ) := by
  -- One `Pose.mul_p` and the frame-3 translation turn the left-hand side into exactly the
  -- right-hand side of `wristCenter_fk_frameFour`; full `simp` again for the literal vector index.
  simp [carrierPose, Pose.mul_p, joint_three_p, dhP_a_zero, wristCenter_fk_frameFour]

/-! ## The wrist's ZYZ entries

For `M = Rz a · Ry β · Rz c` the entries below are the ones the solver reads. With `β = -θ5`
they carry the sine and cosine of `θ5` and the directions of joints 4 and 6, which is
section 7 of `mathematics.md`.
-/

theorem rotZ_mul_rotY_mul_rotZ_entries (a β c : ℝ) :
    (rotZ a * rotY β * rotZ c) 0 2 = Real.sin β * Real.cos a ∧
    (rotZ a * rotY β * rotZ c) 1 2 = Real.sin β * Real.sin a ∧
    (rotZ a * rotY β * rotZ c) 2 2 = Real.cos β ∧
    (rotZ a * rotY β * rotZ c) 2 0 = -Real.sin β * Real.cos c ∧
    (rotZ a * rotY β * rotZ c) 2 1 = Real.sin β * Real.sin c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [rotZ, rotY, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

/-! ## Angle congruence

`fk` reads each joint angle only through its cosine and sine, so a candidate that agrees with
the true angles modulo a full turn produces the same pose. This is the bridge from the
solver's angle bookkeeping to the pose check at the end of `inverse_kinematics`.
-/

/-- A real angle and its image in `Real.Angle`. `Real.Angle` is `ℝ ⧸ 2πℤ`, so an equality
there is exactly "the same joint angle up to a full turn" - the sense in which a solution
recovers the joint angles. -/
theorem cos_of_angle_eq {a b : ℝ} (h : (a : Real.Angle) = (b : Real.Angle)) :
    Real.cos a = Real.cos b := by
  rw [← Real.Angle.cos_coe a, h, Real.Angle.cos_coe b]

theorem sin_of_angle_eq {a b : ℝ} (h : (a : Real.Angle) = (b : Real.Angle)) :
    Real.sin a = Real.sin b := by
  rw [← Real.Angle.sin_coe a, h, Real.Angle.sin_coe b]

/-- `π` is not a full turn, which is what rules out the spurious `a = -b` case below. -/
theorem angle_pi_ne_zero : (Real.pi : Real.Angle) ≠ 0 := by
  intro h
  have h2 : Real.pi = 0 := by
    have h' := congrArg Real.Angle.toReal h
    simp [Real.Angle.toReal_pi] at h'
  exact Real.pi_ne_zero h2

/-- Converses: a common cosine and sine force the angles to agree modulo a full turn. The
spurious `a = -b` case that a common cosine alone permits is killed by the sine. -/
theorem angle_eq_of_cos_eq_of_sin_eq {a b : ℝ}
    (hc : Real.cos a = Real.cos b) (hs : Real.sin a = Real.sin b) :
    (a : Real.Angle) = (b : Real.Angle) := by
  have hc' : Real.Angle.cos (a : Real.Angle) = Real.Angle.cos (b : Real.Angle) := by
    rw [Real.Angle.cos_coe, Real.Angle.cos_coe, hc]
  have hs' : Real.Angle.sin (a : Real.Angle) = Real.Angle.sin (b : Real.Angle) := by
    rw [Real.Angle.sin_coe, Real.Angle.sin_coe, hs]
  rcases (Real.Angle.cos_eq_iff_eq_or_eq_neg).mp hc' with h | h
  · exact h
  · rcases (Real.Angle.sin_eq_iff_eq_or_add_eq_pi).mp hs' with h' | h'
    · exact h'
    · rw [h] at h'
      exact absurd (by simpa using h'.symm : (Real.pi : Real.Angle) = 0) angle_pi_ne_zero

theorem fk_congr {θ' : Fin 6 → ℝ}
    (h : ∀ i, (θ' i : Real.Angle) = (θ i : Real.Angle)) : fk g θ' = fk g θ := by
  have hcos : ∀ i, Real.cos (θ' i) = Real.cos (θ i) := fun i => cos_of_angle_eq (h i)
  have hsin : ∀ i, Real.sin (θ' i) = Real.sin (θ i) := fun i => sin_of_angle_eq (h i)
  have hjoint : ∀ i, joint g θ' i = joint g θ i := by
    intro i
    fin_cases i <;>
      simp only [joint, Matrix.vecCons] <;>
      exact dh_congr (hcos _) (hsin _)
  simp only [fk, armPose, wristPose, hjoint]

/-- `rotZ` reads its angle only modulo a full turn: its entries are the angle's cosine and sine,
which `cos_of_angle_eq` and `sin_of_angle_eq` already know are functions of the angle in
`Real.Angle`. This is `dh_congr`'s statement at the level of the single rotation factor. -/
theorem rotZ_congr {a b : ℝ} (h : (a : Real.Angle) = (b : Real.Angle)) : rotZ a = rotZ b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, cos_of_angle_eq h, sin_of_angle_eq h]

/-- `armRotation` reads its three angles only modulo a full turn: each `rotZ` factor sees its
angle through `rotZ_congr`, and joints 2 and 3 enter only through their sum, which agrees modulo a
full turn by `Real.Angle.coe_add`. Together with `fk_congr` this is what lets a downstream
completeness proof read the solver's `R_3^6` off the commanded angles: the solver's angles are the
true ones up to a full turn, and the rotation they produce is the target rotation. -/
theorem armRotation_congr {θ1 θ2 θ3 θ1' θ2' θ3' : ℝ}
    (h1 : (θ1' : Real.Angle) = (θ1 : Real.Angle))
    (h2 : (θ2' : Real.Angle) = (θ2 : Real.Angle))
    (h3 : (θ3' : Real.Angle) = (θ3 : Real.Angle)) :
    armRotation θ1' θ2' θ3' = armRotation θ1 θ2 θ3 := by
  -- The sum only has to be congruent as a whole; `coe_add` splits it into the two hypotheses.
  have h23 : ((θ2' + θ3' : ℝ) : Real.Angle) = ((θ2 + θ3 : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_add, h2, h3]
  simp only [armRotation, rotZ_congr h1, rotZ_congr h23]

end Kinematics
