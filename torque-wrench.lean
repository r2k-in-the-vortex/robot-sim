import Mathlib

open Matrix
open scoped Matrix

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
noncomputable def sensorTwistToTipVelocity (p : Fin 3 → ℝ) (t : Twist) : Fin 3 → ℝ :=
  t.v + cross t.ω p

-- Theorem: The virtual work computed at the sensor is equal to the virtual work
-- computed at the tip, for any valid transformation and any twist.
-- This formally proves the static equivalence of the two wrenches.
theorem virtualWork_invariant (p : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (tipWrench : Wrench) (t : Twist) :
    virtualWork (tipToSensor p R tipWrench) t =
    virtualWork tipWrench ⟨sensorTwistToTipVelocity p t, t.ω⟩ := by
  -- Unfold all definitions to work with the raw algebra.
  simp [virtualWork, tipToSensor, sensorTwistToTipVelocity, dot, cross, R.mulVec]

  -- We need a helper lemma: the scalar triple product identity.
  -- v · (ω × p) = ω · (p × v)
  have tripleProduct (v ω p : Fin 3 → ℝ) :
    dot v (cross ω p) = dot ω (cross p v) := by
    simp [dot, cross]
    ring

  -- Use the triple product lemma to rearrange the terms.
  rw [tripleProduct]

  -- The remaining goal is a linear algebraic identity that `ring` can solve.
  ring
