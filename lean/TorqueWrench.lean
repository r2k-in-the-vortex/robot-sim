module
-- These are `public import`s because the declarations below are exported
-- (`@[expose] public section`): everything their types and bodies mention has to
-- be part of this module's public interface, or importers cannot use them.
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

open Matrix
open scoped Matrix

@[expose] public section

/-!
# Wrench and twist frame transformations

Force/torque control has to carry a wrench (force + moment) and a twist
(linear + angular velocity) between the sensor frame and the tool-tip frame.
The transformation that matters is the one that preserves virtual power, so
this file defines both transforms and proves that the power agrees in either
frame.

Throughout, `p` is the tip origin expressed in sensor coordinates and `R` maps
tip coordinates to sensor coordinates.

Everything is stated over an arbitrary commutative ring `α`. The identity being
proved is algebraic, so it holds at `ℚ` as well as at the intended physical
instantiation `ℝ` (see `virtualWork_invariant_real`). `ℚ` is what makes the
definitions *evaluable*: `ℝ` is a quotient of Cauchy sequences with no
computation rule, while `ℚ` arithmetic computes, so `ForceTorqueTestData` can
run these transforms to produce exact ground-truth numbers.

Each transform is defined in both directions and the two are proved to be mutual
inverses. `Rotation` then bundles the properties a frame change has to have for
the *algebra* to work — orthogonality, which the inverses need, and determinant
one, without which a reflection would flip a cross product — and with it a chain
of frames is proved to fold into a single transform.
-/

variable {α : Type*} [CommRing α]

-- Define a Wrench structure holding a force and a torque (moment) vector.
-- We use `Fin 3 → α` to represent vectors in R^3.
structure Wrench (α : Type*) where
  force : Fin 3 → α
  torque : Fin 3 → α

-- Define the cross product of two 3D vectors using the standard definition.
def cross (u v : Fin 3 → α) : Fin 3 → α :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

-- Define the dot product (inner product) of two 3D vectors.
def dot (u v : Fin 3 → α) : α :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

-- The components of the cross product, one lemma per index.
--
-- These are what let `simp` see through `cross` in the proofs below: unfolding
-- `cross` itself only yields `![...]`, and `![a, b, c] k` does not reduce by
-- rewriting, so the components have to be named for the literal indices.
@[simp] theorem cross_apply_zero (u v : Fin 3 → α) : cross u v 0 = u 1 * v 2 - u 2 * v 1 := rfl
@[simp] theorem cross_apply_one (u v : Fin 3 → α) : cross u v 1 = u 2 * v 0 - u 0 * v 2 := rfl
@[simp] theorem cross_apply_two (u v : Fin 3 → α) : cross u v 2 = u 0 * v 1 - u 1 * v 0 := rfl

-- A Twist represents the velocity of a rigid body at a point.
-- v is the linear velocity of the reference point, ω is the angular velocity.
structure Twist (α : Type*) where
  v : Fin 3 → α
  ω : Fin 3 → α

-- Compute the virtual power (work rate) of a wrench on a twist.
-- This is the key quantity that must be invariant under transformation.
def virtualWork (w : Wrench α) (t : Twist α) : α :=
  dot w.force t.v + dot w.torque t.ω

-- The transformation from a tip wrench to a sensor wrench.
-- p is the vector from the sensor origin to the tip origin.
-- R is the rotation matrix from tip coordinates to sensor coordinates.
def tipToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (tipWrench : Wrench α) : Wrench α :=
  let F_s := R.mulVec tipWrench.force
  let τ_s := R.mulVec tipWrench.torque + cross p F_s
  ⟨F_s, τ_s⟩

-- The transformation from a sensor wrench back to a tip wrench, the direction
-- force/torque control actually needs: the sensor measures at its own origin,
-- while the contact happens at the tip.
--
-- Rᵀ undoes the rotation and the `- cross p F` removes the moment the lever arm
-- `p` contributed, which is exactly the term `tipToSensor` added.
def sensorToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (sensorWrench : Wrench α) : Wrench α :=
  ⟨Rᵀ.mulVec sensorWrench.force,
    Rᵀ.mulVec (sensorWrench.torque - cross p sensorWrench.force)⟩

-- Define the velocity of the tip given the twist of the sensor.
-- This is the velocity of the tip's material point, still in sensor coordinates.
def sensorTwistToTipVelocity (p : Fin 3 → α) (t : Twist α) : Fin 3 → α :=
  t.v + cross t.ω p

-- The tip twist expressed in tip coordinates, from a sensor twist.
-- Shifting the reference point is not enough on its own: the components are
-- still measured along the sensor's axes, so both parts rotate back by Rᵀ.
def sensorTwistToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (t : Twist α) : Twist α :=
  ⟨Rᵀ.mulVec (sensorTwistToTipVelocity p t), Rᵀ.mulVec t.ω⟩

-- Theorem: The virtual work computed at the sensor is equal to the virtual work
-- computed at the tip, for any valid transformation and any twist.
-- This formally proves the static equivalence of the two wrenches.
--
-- The `Rᵀ` on the twist is what makes this hold. Stating it with the unrotated
-- `sensorTwistToTipVelocity` alone makes the two sides differ in general,
-- because the sensor-frame wrench would then act on a twist whose angular part
-- is still resolved in sensor axes.
theorem virtualWork_invariant (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (tipWrench : Wrench α) (t : Twist α) :
    virtualWork (tipToSensor p R tipWrench) t =
    virtualWork tipWrench (sensorTwistToTip p R t) := by
  -- Unfold the definitions until only the entries of `p`, `R` and the wrench and
  -- twist vectors remain, then close the resulting polynomial identity. `cross`
  -- is deliberately left folded in favour of its component lemmas, and `simp only`
  -- keeps the default simp set out of the expansion.
  simp only [virtualWork, tipToSensor, sensorTwistToTip, sensorTwistToTipVelocity, dot,
    dotProduct, Matrix.mulVec, Matrix.transpose_apply, Fin.sum_univ_three, Pi.add_apply,
    cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

-- The physical instantiation of `virtualWork_invariant`: over `ℝ`, in the
-- frames a real force/torque sensor and tool tip live in.
theorem virtualWork_invariant_real (p : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (tipWrench : Wrench ℝ) (t : Twist ℝ) :
    virtualWork (tipToSensor p R tipWrench) t =
    virtualWork tipWrench (sensorTwistToTip p R t) :=
  virtualWork_invariant p R tipWrench t

-- The two transforms are mutual inverses, so converting a tip wrench to the
-- sensor frame and back is lossless. The `p × F` terms cancel; orthogonality of
-- `R` (`Rᵀ * R = 1`, i.e. `R` is a rotation) is the only hypothesis needed.
-- Each direction consumes the orthogonality it uses.
theorem sensorToTip_tipToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (w : Wrench α) :
    sensorToTip p R (tipToSensor p R w) = w := by
  cases w with
  | mk F τ =>
    simp only [tipToSensor, sensorToTip, Wrench.mk.injEq]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    · simp only [add_sub_cancel_right, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

theorem tipToSensor_sensorToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : R * Rᵀ = 1) (w : Wrench α) :
    tipToSensor p R (sensorToTip p R w) = w := by
  cases w with
  | mk F τ =>
    simp only [tipToSensor, sensorToTip, Wrench.mk.injEq]
    refine ⟨?_, ?_⟩
    · simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    · simp only [sub_add_cancel, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

-- The inverse of `sensorTwistToTip`: a twist at the tip, expressed at the sensor origin
-- in sensor coordinates. The angular part rotates forward, and the lever arm is
-- subtracted, mirroring the `+ cross t.ω p` that `sensorTwistToTipVelocity` adds.
def tipTwistToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α) (t : Twist α) : Twist α :=
  ⟨R.mulVec t.v - cross (R.mulVec t.ω) p, R.mulVec t.ω⟩

theorem sensorTwistToTip_tipTwistToSensor (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : Rᵀ * R = 1) (t : Twist α) :
    sensorTwistToTip p R (tipTwistToSensor p R t) = t := by
  cases t with
  | mk v ω =>
    simp only [sensorTwistToTip, tipTwistToSensor, sensorTwistToTipVelocity, Twist.mk.injEq]
    refine ⟨?_, ?_⟩
    · simp only [sub_add_cancel, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    · simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

theorem tipTwistToSensor_sensorTwistToTip (p : Fin 3 → α) (R : Matrix (Fin 3) (Fin 3) α)
    (hR : R * Rᵀ = 1) (t : Twist α) :
    tipTwistToSensor p R (sensorTwistToTip p R t) = t := by
  cases t with
  | mk v ω =>
    simp only [sensorTwistToTip, tipTwistToSensor, sensorTwistToTipVelocity, Twist.mk.injEq]
    refine ⟨?_, ?_⟩
    · simp only [add_sub_cancel_right, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    · simp only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

/-! ## The cross product as a vector operation

The frame algebra below needs two facts about `cross` that the component lemmas above do
not give: that it is what Mathlib calls `⨯₃`, so that its bilinearity is available, and
that a rotation commutes with it.
-/

/-- This file's `cross` is Mathlib's cross product, spelled out. -/
theorem cross_eq_crossProduct (u v : Fin 3 → α) : cross u v = u ⨯₃ v := rfl

theorem add_cross (u v w : Fin 3 → α) : cross (u + v) w = cross u w + cross v w := by
  simp only [cross_eq_crossProduct, map_add, LinearMap.add_apply]

theorem cross_add (u v w : Fin 3 → α) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross_eq_crossProduct, map_add]

/-- Mathlib states the triple product as `u ⬝ᵥ (v ⨯₃ w)`; this is the same identity with
the cross product on the left, which is the form the proof below needs. -/
theorem cross_dotProduct_eq_det (u v w : Fin 3 → α) :
    (u ⨯₃ v) ⬝ᵥ w = Matrix.det ![u, v, w] := by
  rw [dotProduct_comm, triple_product_permutation, triple_product_eq_det]

/-- With the dot product on the left, the transpose moves across: this is the identity
that lets a rotated vector be tested against a fixed direction. -/
theorem mulVec_dotProduct (A : Matrix (Fin 3) (Fin 3) α) (v w : Fin 3 → α) :
    (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
  calc (A *ᵥ v) ⬝ᵥ w = w ⬝ᵥ (A *ᵥ v) := dotProduct_comm _ _
    _ = (w ᵥ* A) ⬝ᵥ v := Matrix.dotProduct_mulVec w A v
    _ = (Aᵀ *ᵥ w) ⬝ᵥ v := by rw [Matrix.mulVec_transpose]
    _ = v ⬝ᵥ (Aᵀ *ᵥ w) := dotProduct_comm _ _

/-- The `k`-th basis vector of `α³`, written out rather than taken from `Pi.single` so
that this file depends on nothing beyond the imports at the top. -/
def basisVec (k : Fin 3) : Fin 3 → α := fun j => if j = k then 1 else 0

/-- Dotting with the `k`-th basis vector reads off the `k`-th component. -/
theorem dotProduct_basisVec (x : Fin 3 → α) (k : Fin 3) : x ⬝ᵥ basisVec k = x k := by
  fin_cases k <;> simp [dotProduct, basisVec]

-- Orthogonality plus determinant one also makes `R` a left inverse of its transpose,
-- which is what lets `R *ᵥ Rᵀ *ᵥ x` collapse. The adjugate supplies the missing piece:
-- `R * adjugate R = det R • 1 = 1`, and multiplying that on the left by `Rᵀ` turns it into
-- `adjugate R = Rᵀ`, which is exactly `R * Rᵀ = 1`.
theorem mul_transpose_eq_one (R : Matrix (Fin 3) (Fin 3) α) (hR : Rᵀ * R = 1)
    (hd : R.det = 1) : R * Rᵀ = 1 := by
  have hmul : R * Matrix.adjugate R = 1 := by rw [Matrix.mul_adjugate, hd, one_smul]
  have hadj : Matrix.adjugate R = Rᵀ := by
    calc Matrix.adjugate R = 1 * Matrix.adjugate R := (one_mul _).symm
      _ = (Rᵀ * R) * Matrix.adjugate R := by rw [hR]
      _ = Rᵀ * (R * Matrix.adjugate R) := Matrix.mul_assoc _ _ _
      _ = Rᵀ * 1 := by rw [hmul]
      _ = Rᵀ := mul_one _
  rw [← hadj]
  exact hmul

/-- Rotating all three rows of a `![x, y, z]` block leaves its determinant alone, because
the rotated block is `![x, y, z] * Rᵀ` and `det R = 1`. -/
theorem det_rotate (R : Matrix (Fin 3) (Fin 3) α) (hd : R.det = 1) (x y z : Fin 3 → α) :
    Matrix.det ![R *ᵥ x, R *ᵥ y, R *ᵥ z] = Matrix.det ![x, y, z] := by
  -- `Matrix.of` keeps both factors syntactically matrices: `Matrix` is a `def`, so
  -- instance resolution will not unfold it far enough to multiply a bare `![...]`.
  have hmat : (![R *ᵥ x, R *ᵥ y, R *ᵥ z] : Matrix (Fin 3) (Fin 3) α) =
      Matrix.of ![x, y, z] * Rᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] <;>
      ring
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, hd, mul_one]
  rfl

/-- A rotation commutes with the cross product.
--
-- This is where the determinant earns its place: orthogonality alone would also admit
-- reflections, and those *anti*-commute with the cross product instead. -/
theorem mulVec_cross (R : Matrix (Fin 3) (Fin 3) α) (hR : Rᵀ * R = 1) (hd : R.det = 1)
    (u v : Fin 3 → α) : R *ᵥ cross u v = cross (R *ᵥ u) (R *ᵥ v) := by
  have hRR : R * Rᵀ = 1 := mul_transpose_eq_one R hR hd
  rw [cross_eq_crossProduct, cross_eq_crossProduct]
  funext k
  -- Both components are the same determinant: `R` can be pulled out of one side of the
  -- triple product and put back on the other.
  calc (R *ᵥ (u ⨯₃ v)) k
      = (R *ᵥ (u ⨯₃ v)) ⬝ᵥ basisVec k := (dotProduct_basisVec _ k).symm
    _ = (u ⨯₃ v) ⬝ᵥ (Rᵀ *ᵥ basisVec k) := mulVec_dotProduct R _ _
    _ = Matrix.det ![u, v, Rᵀ *ᵥ basisVec k] := cross_dotProduct_eq_det _ _ _
    _ = Matrix.det ![R *ᵥ u, R *ᵥ v, R *ᵥ (Rᵀ *ᵥ basisVec k)] :=
          (det_rotate R hd u v _).symm
    _ = Matrix.det ![R *ᵥ u, R *ᵥ v, basisVec k] := by
          rw [Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec]
    _ = ((R *ᵥ u) ⨯₃ (R *ᵥ v)) ⬝ᵥ basisVec k := (cross_dotProduct_eq_det _ _ _).symm
    _ = ((R *ᵥ u) ⨯₃ (R *ᵥ v)) k := dotProduct_basisVec _ k

/-! ## Rotations

Orthogonality alone is enough for the round trips above, but not for composing frames: a
reflection such as `diag(1, 1, -1)` satisfies `Rᵀ * R = 1` and flips the sign of a cross
product, and composing through it would report the wrong torque. Bundling the determinant
into the structure keeps that hypothesis off every caller.
-/

/-- A rotation: an orthogonal matrix with determinant one, the rigid change of frame the
transforms above are meant for. -/
structure Rotation (α : Type*) [CommRing α] where
  mat : Matrix (Fin 3) (Fin 3) α
  orth : matᵀ * mat = 1
  det_eq_one : mat.det = 1

namespace Rotation

instance : Coe (Rotation α) (Matrix (Fin 3) (Fin 3) α) := ⟨Rotation.mat⟩

/-- The identity rotation. -/
def id : Rotation α where
  mat := 1
  orth := by rw [Matrix.transpose_one, Matrix.one_mul]
  det_eq_one := Matrix.det_one

/-- Composition: `ρ * σ` is `ρ` after `σ`, the rotation that carries a vector through
both. -/
def mul (ρ σ : Rotation α) : Rotation α where
  mat := ρ.mat * σ.mat
  orth := by
    calc (ρ.mat * σ.mat)ᵀ * (ρ.mat * σ.mat)
        = (σ.matᵀ * ρ.matᵀ) * (ρ.mat * σ.mat) := by rw [Matrix.transpose_mul]
      _ = σ.matᵀ * (ρ.matᵀ * (ρ.mat * σ.mat)) := Matrix.mul_assoc _ _ _
      _ = σ.matᵀ * ((ρ.matᵀ * ρ.mat) * σ.mat) := by
            rw [← Matrix.mul_assoc ρ.matᵀ ρ.mat σ.mat]
      _ = σ.matᵀ * (1 * σ.mat) := by rw [ρ.orth]
      _ = σ.matᵀ * σ.mat := by rw [Matrix.one_mul]
      _ = 1 := σ.orth
  det_eq_one := by rw [Matrix.det_mul, ρ.det_eq_one, σ.det_eq_one, one_mul]

/-- The inverse rotation, which for a rotation is the transpose. -/
def inv (ρ : Rotation α) : Rotation α where
  mat := ρ.matᵀ
  orth := by rw [Matrix.transpose_transpose, mul_transpose_eq_one _ ρ.orth ρ.det_eq_one]
  det_eq_one := by rw [Matrix.det_transpose, ρ.det_eq_one]

instance : One (Rotation α) := ⟨id⟩
instance : Mul (Rotation α) := ⟨mul⟩
instance : Inv (Rotation α) := ⟨inv⟩

/-- A rotation commutes with the cross product, with nothing left to discharge. -/
theorem mulVec_cross (ρ : Rotation α) (u v : Fin 3 → α) :
    ρ.mat *ᵥ cross u v = cross (ρ.mat *ᵥ u) (ρ.mat *ᵥ v) :=
  _root_.mulVec_cross ρ.mat ρ.orth ρ.det_eq_one u v

/-- The transpose of a rotation pushes through a cross product by rotating the other
factor: `mulVec_cross` read backwards, through the inverse rotation. -/
theorem transpose_mulVec_cross (ρ : Rotation α) (u q : Fin 3 → α) :
    cross (ρ.matᵀ *ᵥ u) q = ρ.matᵀ *ᵥ cross u (ρ.mat *ᵥ q) := by
  calc cross (ρ.matᵀ *ᵥ u) q
      = cross (ρ.matᵀ *ᵥ u) (ρ.matᵀ *ᵥ (ρ.mat *ᵥ q)) := by
          rw [Matrix.mulVec_mulVec, ρ.orth, Matrix.one_mulVec]
    _ = ρ.matᵀ *ᵥ cross u (ρ.mat *ᵥ q) := (mulVec_cross ρ⁻¹ u (ρ.mat *ᵥ q)).symm

/-- Converting a tip wrench up to the sensor frame and back is lossless. -/
theorem sensorToTip_tipToSensor (ρ : Rotation α) (p : Fin 3 → α) (w : Wrench α) :
    sensorToTip p ρ.mat (tipToSensor p ρ.mat w) = w :=
  _root_.sensorToTip_tipToSensor p ρ.mat ρ.orth w

/-- Converting a sensor wrench down to the tip and back is lossless. -/
theorem tipToSensor_sensorToTip (ρ : Rotation α) (p : Fin 3 → α) (w : Wrench α) :
    tipToSensor p ρ.mat (sensorToTip p ρ.mat w) = w :=
  _root_.tipToSensor_sensorToTip p ρ.mat (mul_transpose_eq_one ρ.mat ρ.orth ρ.det_eq_one) w

/-- Converting a sensor twist down to the tip and back is lossless. -/
theorem sensorTwistToTip_tipTwistToSensor (ρ : Rotation α) (p : Fin 3 → α) (t : Twist α) :
    sensorTwistToTip p ρ.mat (tipTwistToSensor p ρ.mat t) = t :=
  _root_.sensorTwistToTip_tipTwistToSensor p ρ.mat ρ.orth t

/-- Converting a tip twist up to the sensor frame and back is lossless. -/
theorem tipTwistToSensor_sensorTwistToTip (ρ : Rotation α) (p : Fin 3 → α) (t : Twist α) :
    tipTwistToSensor p ρ.mat (sensorTwistToTip p ρ.mat t) = t :=
  _root_.tipTwistToSensor_sensorTwistToTip p ρ.mat
    (mul_transpose_eq_one ρ.mat ρ.orth ρ.det_eq_one) t

end Rotation

/-! ## Composing frames

A chain of frames collapses into a single transform: the pose of the far frame is the
usual rigid composition `p + ρ *ᵥ q` with `ρ * σ`, and the extra lever-arm terms merge
because a rotation commutes with `cross`.
-/

/-- Wrenches compose: routing a wrench through an intermediate frame gives the same
result as converting it in one step. -/
theorem tipToSensor_comp (ρ σ : Rotation α) (p q : Fin 3 → α) (w : Wrench α) :
    tipToSensor p ρ.mat (tipToSensor q σ.mat w) =
    tipToSensor (p + ρ.mat *ᵥ q) (ρ.mat * σ.mat) w := by
  obtain ⟨F, τ⟩ := w
  simp only [tipToSensor, Wrench.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_mulVec]
  · have hσ : ρ.mat *ᵥ cross q (σ.mat *ᵥ F) = cross (ρ.mat *ᵥ q) ((ρ.mat * σ.mat) *ᵥ F) := by
      rw [Rotation.mulVec_cross, Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_add]
    -- `hσ` first, while `cross` is still folded, then the linearity of `⨯₃`.
    simp only [hσ, Matrix.mulVec_mulVec]
    simp only [cross_eq_crossProduct, map_add, LinearMap.add_apply]
    abel

/-- Twists compose exactly like wrenches, with the same composed pose. -/
theorem sensorTwistToTip_comp (ρ σ : Rotation α) (p q : Fin 3 → α) (t : Twist α) :
    sensorTwistToTip q σ.mat (sensorTwistToTip p ρ.mat t) =
    sensorTwistToTip (p + ρ.mat *ᵥ q) (ρ.mat * σ.mat) t := by
  obtain ⟨v, ω⟩ := t
  simp only [sensorTwistToTip, sensorTwistToTipVelocity, Twist.mk.injEq]
  refine ⟨?_, ?_⟩
  · -- Push `ρᵀ` back through the lever arm so the two offsets can be added inside one
    -- cross product, then collapse the two rotations into one.
    calc σ.matᵀ *ᵥ (ρ.matᵀ *ᵥ (v + cross ω p) + cross (ρ.matᵀ *ᵥ ω) q)
        = σ.matᵀ *ᵥ (ρ.matᵀ *ᵥ (v + cross ω p) + ρ.matᵀ *ᵥ cross ω (ρ.mat *ᵥ q)) := by
          rw [Rotation.transpose_mulVec_cross]
      _ = σ.matᵀ *ᵥ (ρ.matᵀ *ᵥ ((v + cross ω p) + cross ω (ρ.mat *ᵥ q))) := by
          rw [← Matrix.mulVec_add]
      _ = σ.matᵀ *ᵥ (ρ.matᵀ *ᵥ (v + cross ω (p + ρ.mat *ᵥ q))) := by
          rw [add_assoc, ← cross_add]
      _ = (ρ.mat * σ.mat)ᵀ *ᵥ (v + cross ω (p + ρ.mat *ᵥ q)) := by
          rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  · rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
