module
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Matrix
open scoped Matrix

/-!
# Wrench and twist frame transformations

Force/torque control has to carry a wrench (force + moment) and a twist
(linear + angular velocity) between the sensor frame and the tool-tip frame.
The transformation that matters is the one that preserves virtual power, so
this file defines both transforms and proves that the power agrees in either
frame.

Throughout, `p` is the tip origin expressed in sensor coordinates and `R` maps
tip coordinates to sensor coordinates.
-/

-- Define a Wrench structure holding a force and a torque (moment) vector.
-- We use `Fin 3 → ℝ` to represent vectors in R^3.
structure Wrench where
  force : Fin 3 → ℝ
  torque : Fin 3 → ℝ

-- Define the cross product of two 3D vectors using the standard definition.
noncomputable def cross (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

-- Define the dot product (inner product) of two 3D vectors.
noncomputable def dot (u v : Fin 3 → ℝ) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

-- A Twist represents the velocity of a rigid body at a point.
-- v is the linear velocity of the reference point, ω is the angular velocity.
structure Twist where
  v : Fin 3 → ℝ
  ω : Fin 3 → ℝ

-- Compute the virtual power (work rate) of a wrench on a twist.
-- This is the key quantity that must be invariant under transformation.
noncomputable def virtualWork (w : Wrench) (t : Twist) : ℝ :=
  dot w.force t.v + dot w.torque t.ω

-- The transformation from a tip wrench to a sensor wrench.
-- p is the vector from the sensor origin to the tip origin.
-- R is the rotation matrix from tip coordinates to sensor coordinates.
noncomputable def tipToSensor (p : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (tipWrench : Wrench) : Wrench :=
  let F_s := R.mulVec tipWrench.force
  let τ_s := R.mulVec tipWrench.torque + cross p F_s
  ⟨F_s, τ_s⟩

-- Define the velocity of the tip given the twist of the sensor.
-- This is the velocity of the tip's material point, still in sensor coordinates.
noncomputable def sensorTwistToTipVelocity (p : Fin 3 → ℝ) (t : Twist) : Fin 3 → ℝ :=
  t.v + cross t.ω p

-- The tip twist expressed in tip coordinates, from a sensor twist.
-- Shifting the reference point is not enough on its own: the components are
-- still measured along the sensor's axes, so both parts rotate back by Rᵀ.
noncomputable def sensorTwistToTip (p : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (t : Twist) : Twist :=
  ⟨Rᵀ.mulVec (sensorTwistToTipVelocity p t), Rᵀ.mulVec t.ω⟩

-- Theorem: The virtual work computed at the sensor is equal to the virtual work
-- computed at the tip, for any valid transformation and any twist.
-- This formally proves the static equivalence of the two wrenches.
--
-- The `Rᵀ` on the twist is what makes this hold. Stating it with the unrotated
-- `sensorTwistToTipVelocity` alone makes the two sides differ in general,
-- because the sensor-frame wrench would then act on a twist whose angular part
-- is still resolved in sensor axes.
theorem virtualWork_invariant (p : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (tipWrench : Wrench) (t : Twist) :
    virtualWork (tipToSensor p R tipWrench) t =
    virtualWork tipWrench (sensorTwistToTip p R t) := by
  simp [virtualWork, tipToSensor, sensorTwistToTip, sensorTwistToTipVelocity, dot, cross,
    Matrix.mulVec, Matrix.transpose_apply, Fin.sum_univ_three]
  ring
