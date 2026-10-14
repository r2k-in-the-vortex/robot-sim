module
-- These are `public import`s because the declarations below are exported
-- (`@[expose] public section`): everything their types and bodies mention has to
-- be part of this module's public interface, or importers cannot use them.
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.DotProduct
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
