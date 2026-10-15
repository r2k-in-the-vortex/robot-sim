module

-- `Kinematics` is `public` because these are more theorems about its objects: every statement
-- below mentions `rotZ`, `rotY` or `wristRotation`, and the proofs use `rotZ_add`.
-- `NonsingularInverse` is `public` because `mul_transpose_eq_one_of_transpose_mul` is exported
-- (`@[expose] public section`) and its proof names `Matrix.isUnit_det_of_left_inverse`,
-- `Matrix.inv_eq_left_inv` and `Matrix.mul_nonsing_inv`, which live there - and because the
-- cofactor relations below go through `Matrix.adjugate`, which comes from its public
-- `Matrix.Adjugate` and `Matrix.MvPolynomial` imports together with `Matrix.det`.
-- `Atan2` is `public` because the reconstruction statements mention `atan2` and `hypot`.
public import Kinematics
public import Atan2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
open scoped Matrix
open RealAtan2

noncomputable section

@[expose] public section

/-!
# The ZYZ/wrist facts the closed-form inverse kinematics consumes

This file carries the wrist's `ZYZ` algebra that `InverseKinematics.lean`'s reconstruction step
needs and that `Kinematics.lean` does not already provide: the four facts below, and the
reconstruction theorems built out of them.

* `rotZ_pi_mul_rotY_mul_rotZ_pi` - a half-turn about z conjugated with a y-rotation;
* `wristRotation_mirror` - the two wrist branches are literally the same rotation, which is what
  removes the sign case split from the reconstruction;
* `rotZ_mul_rotY_mul_rotZ_entries_all` - the four entries of a ZYZ product left out by
  `Kinematics.rotZ_mul_rotY_mul_rotZ_entries`;
* `mul_transpose_eq_one_of_transpose_mul` - the direction of orthogonality that
  `Kinematics.mul_orth` cannot produce.

`wristRotation_reconstruct` then puts them together: the three angles the solver's wrist step
reads off a rotation rebuild it, in either `atan2` branch
(`wristRotation_reconstruct_mirror`) and at the wrist singularity
(`wristRotation_reconstruct_flat`). The middle angle is passed to `wristRotation` *negated*,
because that definition already carries the negation of `θ5`: the ZYZ middle angle `γ` of `Q` is
recovered as `θ5 = -γ`, `hypot` is never negative, and the two branches the solver returns are
exactly `(a, -β, c)` and `(a + π, β, c + π)`. -/

namespace Kinematics

/-- A half-turn about z conjugates a y-rotation into the y-rotation of the opposite angle:
`rotZ π * rotY β * rotZ π = rotY (-β)`.

`rotZ π` is `diag (-1, -1, 1)`, so conjugating by it flips the sign of `rotY β`'s first two rows
and columns; the only entries of `rotY β` that sit off the diagonal are the two `sin β` ones, so
the result is `rotY (-β)`. Structurally it is the sign flip that `θ4 ↦ θ4 + π` and
`θ6 ↦ θ6 + π` impose on the middle angle.

This is the identity that makes the two wrist branches reconstruct the *same* matrix — it is what
`wristRotation_mirror` below reduces to — so the reconstruction never has to split on which
branch the solved angles came from. -/
theorem rotZ_pi_mul_rotY_mul_rotZ_pi (β : ℝ) :
    rotZ Real.pi * rotY β * rotZ Real.pi = rotY (-β) := by
  -- No `ring` after the expansion: `rotZ π` is `diag (-1, -1, 1)`, so once `simp` has
  -- evaluated `cos π`, `sin π` and `sin (-β)`, both sides of every entry are the same product
  -- of `±1`, `sin β` and `cos β`, and `simp`'s arithmetic normalisation already sees that.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, rotY, Matrix.mul_apply, Fin.sum_univ_three]

/-- The mirrored wrist is the same wrist: `wristRotation (a + π) (-β) (c + π)` is
`wristRotation a β c`.

A spherical wrist's `ZYZ` decomposition has two angle solutions for one rotation, related by
turning joints 4 and 6 by `π` and joint 5 the other way. The solver's `atan2` may return either,
so the reconstruction has to accept both; this lemma says the pose it then computes is the same
one, and it is the reason the middle angle is stated *negated* — `wristRotation` already carries
the negation of `θ5`, so `-β` cancels against it and the two half-turns cancel against the
`rotZ π` in `rotZ_pi_mul_rotY_mul_rotZ_pi`. -/
theorem wristRotation_mirror (a β c : ℝ) :
    wristRotation (a + Real.pi) (-β) (c + Real.pi) = wristRotation a β c := by
  -- Unfold the ZYZ product; `wristRotation` negates the middle angle, so the mirror's `-β`
  -- cancels against that negation and leaves the plain `rotY β`.
  simp only [wristRotation, neg_neg]
  -- Split each shifted z rotation into the original turn and a half-turn. The right half-turn is
  -- taken out on its *left* (`c + π = π + c`, so `rotZ (c + π) = rotZ π * rotZ c`), which puts
  -- the two half-turns next to each other without having to commute `rotZ c` past the middle
  -- factor at all.
  rw [← rotZ_add a Real.pi, show c + Real.pi = Real.pi + c by ring, ← rotZ_add Real.pi c]
  -- Reassociate, purely by `Matrix.mul_assoc`, so that the two half-turns bracket the middle
  -- factor: `rotZ a * (rotZ π * rotY β * rotZ π) * rotZ c`. Then the conjugation above collapses
  -- the bracket to `rotY (-β)`, which is the right-hand side.
  rw [Matrix.mul_assoc (rotZ a) (rotZ Real.pi) (rotY β),
    ← Matrix.mul_assoc (rotZ a * (rotZ Real.pi * rotY β)) (rotZ Real.pi) (rotZ c),
    Matrix.mul_assoc (rotZ a) (rotZ Real.pi * rotY β) (rotZ Real.pi),
    rotZ_pi_mul_rotY_mul_rotZ_pi β]

/-- The four entries of a ZYZ product that `rotZ_mul_rotY_mul_rotZ_entries` leaves out: the
top-left 2x2 block, as a conjunction in the same style as that theorem.

`M = rotZ a * rotY β * rotZ c` is the wrist rotation with the labels `a = θ4`, `β = -θ5`,
`c = θ6`. The five entries already on record pin down the third row and third column of `M` and
are what the solver *reads* the angles from; these four pin down the remaining top-left block,
and with `sin β` and `cos β` known each of them is the entry the same ZYZ product evaluates to,
so together the nine give the full entrywise equality the reconstruction turns back into a matrix
equation. -/
theorem rotZ_mul_rotY_mul_rotZ_entries_all (a β c : ℝ) :
    (rotZ a * rotY β * rotZ c) 0 0 = Real.cos a * Real.cos β * Real.cos c - Real.sin a * Real.sin c ∧
    (rotZ a * rotY β * rotZ c) 0 1 = -Real.cos a * Real.cos β * Real.sin c - Real.sin a * Real.cos c ∧
    (rotZ a * rotY β * rotZ c) 1 0 = Real.sin a * Real.cos β * Real.cos c + Real.cos a * Real.sin c ∧
    (rotZ a * rotY β * rotZ c) 1 1 = -Real.sin a * Real.cos β * Real.sin c + Real.cos a * Real.cos c := by
  -- Same expansion as `rotZ_mul_rotY_mul_rotZ_entries`: both matrix products become sums of
  -- three terms, and every entry is then a trigonometric polynomial in `a`, `β` and `c`.
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [rotZ, rotY, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

/-- Orthogonality the other way round: `Aᵀ * A = 1` implies `A * Aᵀ = 1` for a 3x3 real matrix.

`Kinematics.mul_orth` only ever builds the `Aᵀ * A = 1` direction, which cancels a factor
standing on the *left* of a product (`A * Y = X` becomes `Y = Aᵀ * X`). The reconstruction also
needs the direction below, which cancels a factor standing on the *right* (`Y * A = X` becomes
`Y = X * Aᵀ`); the two together say `Aᵀ` is a two-sided inverse of `A`. -/
theorem mul_transpose_eq_one_of_transpose_mul {A : Matrix (Fin 3) (Fin 3) ℝ} (h : Aᵀ * A = 1) :
    A * Aᵀ = 1 := by
  -- `Aᵀ` is a left inverse of `A`, so `A.det` is a unit; there is no need to detour through
  -- `det ≠ 0` and `isUnit_iff_ne_zero`, `Matrix.isUnit_det_of_left_inverse` hands over the
  -- `IsUnit` directly.
  have hunit : IsUnit A.det := Matrix.isUnit_det_of_left_inverse h
  -- `A⁻¹` is the nonsingular inverse, which is `Aᵀ` because a left inverse of a nonsingular
  -- matrix is the inverse ...
  rw [← Matrix.inv_eq_left_inv h]
  -- ... and it is a right inverse, which is exactly the goal.
  exact Matrix.mul_nonsing_inv A hunit

/-! ## The reconstruction

The solver's wrist step builds three angles out of a rotation `Q` and hands them to
`wristRotation`; these three theorems are the guarantee that the pose it computes is `Q` itself.
`Q` enters as an orthonormal matrix of determinant one - what the wrist's share of a target
rotation is, once the arm's rotation has been divided out - and `hne : (Q 0 2, Q 1 2) ≠ (0, 0)`
says the third column is not vertical: the hypothesis the two regular branches take and the flat
branch assumes the negation of.
-/

/-- The direct reconstruction: a rotation whose third column is not vertical is rebuilt by the
three angles the solver reads off it.

`hypot (Q 0 2) (Q 1 2)` is the length of the third column's `xy` part, so `β` is the middle ZYZ
angle as `atan2` of the third column sees it, and the two outer angles are the directions of
joints 4 and 6. The proof is entry by entry: the five entries
`Kinematics.rotZ_mul_rotY_mul_rotZ_entries` provides come from `sin_atan2`/`cos_atan2` together
with the third column and third row being unit vectors, and the four remaining ones are pinned
down by the cofactor relations that `Q.det = 1` gives - which is the one place `hdet` is used. -/
theorem wristRotation_reconstruct {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Qᵀ * Q = 1) (hdet : Q.det = 1) (hne : (Q 0 2, Q 1 2) ≠ (0, 0)) :
    wristRotation (atan2 (Q 1 2) (Q 0 2))
      (-(atan2 (hypot (Q 0 2) (Q 1 2)) (Q 2 2)))
      (atan2 (Q 2 1) (-(Q 2 0))) = Q := by
  -- `wristRotation` already negates its middle angle, so the solver's `β` cancels against that
  -- negation and the goal is the plain ZYZ product `rotZ a * rotY β * rotZ c = Q`.
  simp only [wristRotation, neg_neg]
  -- Short names: the five entries the solver reads, the third column's `xy` length, and the
  -- three angles.
  set p : ℝ := Q 0 2 with hp
  set q : ℝ := Q 1 2 with hq
  set r : ℝ := Q 2 2 with hr
  set u : ℝ := Q 2 0 with hu
  set v : ℝ := Q 2 1 with hv
  set s : ℝ := hypot p q with hs
  set a : ℝ := atan2 q p with ha
  set b : ℝ := atan2 s r with hb
  set c : ℝ := atan2 v (-u) with hc
  -- ## Norms
  -- The third column is a unit vector, so `s ^ 2 = 1 - r ^ 2`; the third row is one too, which
  -- is what makes `(u, v)` a legal `atan2` argument below.
  have hcol3 : p ^ 2 + q ^ 2 + r ^ 2 = 1 := by
    have h : (Qᵀ * Q) 2 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 2 := by rw [hQ]
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, pow_two,
      ← hp, ← hq, ← hr] using h
  have hrow3 : u ^ 2 + v ^ 2 + r ^ 2 = 1 := by
    have h : (Q * Qᵀ) 2 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 2 := by
      rw [mul_transpose_eq_one_of_transpose_mul hQ]
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, pow_two,
      ← hu, ← hv, ← hr] using h
  have hs_sq : s ^ 2 = p ^ 2 + q ^ 2 := by rw [hs]; exact hypot_sq p q
  have hs2 : s ^ 2 = 1 - r ^ 2 := by nlinarith [hs_sq, hcol3]
  have huv : u ^ 2 + v ^ 2 = s ^ 2 := by nlinarith [hrow3, hcol3, hs_sq]
  -- `hne` is exactly `s ≠ 0`, and `s ≠ 0` also makes `(u, v)` nonvanishing.
  have hpq_ne : (p, q) ≠ (0, 0) := by simpa only [← hp, ← hq] using hne
  have hs_ne : s ≠ 0 := by
    intro h0
    have hz : p ^ 2 + q ^ 2 = 0 := by rw [← hs_sq, h0]; ring
    exact hpq_ne (Prod.ext (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg q, hz]))
      (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg p, hz])))
  have huv_ne : (u, v) ≠ (0, 0) := by
    intro h0
    have hu0 : u = 0 := congrArg Prod.fst h0
    have hv0 : v = 0 := congrArg Prod.snd h0
    refine hs_ne (sq_eq_zero_iff.mp ?_)
    rw [← huv, hu0, hv0]
    ring
  have hneguv_ne : (-u, v) ≠ (0, 0) := by
    intro h0
    have hu0 : -u = 0 := congrArg Prod.fst h0
    have hv0 : v = 0 := congrArg Prod.snd h0
    exact huv_ne (Prod.ext (neg_eq_zero.mp hu0) hv0)
  -- ## The three angles
  -- `sin_atan2` is total and `cos_atan2` needs a direction; the forms below are `s`-multiplied,
  -- so no division survives into the entry computations.
  have hrs : hypot r s = 1 := by
    rw [hypot, show r ^ 2 + s ^ 2 = 1 by nlinarith [hs_sq, hcol3], Real.sqrt_one]
  have hrs_ne : (r, s) ≠ (0, 0) := fun h0 => hs_ne (by simpa using congrArg Prod.snd h0)
  have hsb : Real.sin b = s := by rw [hb, sin_atan2, hrs, div_one]
  have hcb : Real.cos b = r := by rw [hb, cos_atan2 hrs_ne, hrs, div_one]
  have hsa : s * Real.cos a = p := by
    rw [ha, cos_atan2 hpq_ne, ← hs, mul_div_assoc', mul_div_cancel_left₀ p hs_ne]
  have hssa : s * Real.sin a = q := by
    rw [ha, sin_atan2, ← hs, mul_div_assoc', mul_div_cancel_left₀ q hs_ne]
  have huv_eq : hypot u v = s := by
    rw [hs, hypot, hypot, show u ^ 2 + v ^ 2 = p ^ 2 + q ^ 2 by nlinarith [huv, hs_sq]]
  -- `hypot` only sees the square of its first argument, so the sign `-u` drops out.
  have hneguv : hypot (-u) v = s := by
    rw [← huv_eq, hypot, hypot, show (-u) ^ 2 + v ^ 2 = u ^ 2 + v ^ 2 by ring]
  have hsc : s * Real.cos c = -u := by
    rw [hc, cos_atan2 hneguv_ne, hneguv, mul_div_assoc', mul_div_cancel_left₀ (-u) hs_ne]
  have hss : s * Real.sin c = v := by
    rw [hc, sin_atan2, hneguv, mul_div_assoc', mul_div_cancel_left₀ v hs_ne]
  -- ## The cofactor relations
  -- `Q.det = 1` makes `Qᵀ` the inverse and hence the adjugate of `Q`, whose entries are the 2x2
  -- cofactors. The four top-left ones are linear in the unknowns `Q 0 0`, `Q 0 1`, `Q 1 0`,
  -- `Q 1 1` and are what determines them from the entries the solver already has.
  have hadj : Q.adjugate = Qᵀ := by
    have hinv : Q⁻¹ = Qᵀ := Matrix.inv_eq_left_inv hQ
    rw [← hinv, Matrix.inv_def, hdet]
    simp
  have hc00 : Q 0 0 = Q 1 1 * Q 2 2 - Q 1 2 * Q 2 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) hadj
    simpa [Matrix.adjugate_fin_three, Matrix.transpose_apply] using h.symm
  have hc01 : Q 0 1 = -(Q 1 0 * Q 2 2) + Q 1 2 * Q 2 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 0) hadj
    simpa [Matrix.adjugate_fin_three, Matrix.transpose_apply] using h.symm
  have hc10 : Q 1 0 = -(Q 0 1 * Q 2 2) + Q 0 2 * Q 2 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) hadj
    simpa [Matrix.adjugate_fin_three, Matrix.transpose_apply] using h.symm
  have hc11 : Q 1 1 = Q 0 0 * Q 2 2 - Q 0 2 * Q 2 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) hadj
    simpa [Matrix.adjugate_fin_three, Matrix.transpose_apply] using h.symm
  -- In the short names, and combined into the cleared form `entry * s ^ 2 = ...`: substituting
  -- one relation into the other leaves a linear equation in the monomials, which `linarith`
  -- then closes.
  have hc00' : Q 0 0 = Q 1 1 * r - q * v := by simpa only [← hr, ← hq, ← hv] using hc00
  have hc01' : Q 0 1 = -(Q 1 0 * r) + q * u := by simpa only [← hr, ← hu, ← hq] using hc01
  have hc10' : Q 1 0 = -(Q 0 1 * r) + p * v := by simpa only [← hr, ← hp, ← hv] using hc10
  have hc11' : Q 1 1 = Q 0 0 * r - p * u := by simpa only [← hr, ← hp, ← hu] using hc11
  have hQ00 : Q 0 0 * s ^ 2 = -(p * u * r + q * v) := by
    rw [hs2]
    have h := hc00'
    rw [hc11'] at h
    linarith [h]
  have hQ01 : Q 0 1 * s ^ 2 = q * u - p * v * r := by
    rw [hs2]
    have h := hc01'
    rw [hc10'] at h
    linarith [h]
  have hQ10 : Q 1 0 * s ^ 2 = p * v - q * u * r := by
    rw [hs2]
    have h := hc10'
    rw [hc01'] at h
    linarith [h]
  have hQ11 : Q 1 1 * s ^ 2 = -(p * u + q * v * r) := by
    rw [hs2]
    have h := hc11'
    rw [hc00'] at h
    linarith [h]
  -- ## The product's four corner entries, multiplied up by `s ^ 2`
  -- Multiplying by `s ^ 2` lets the cleared angle facts factor the products: each of
  -- `s * cos a`, `s * sin a`, `s * cos c`, `s * sin c` appears exactly once per term.
  obtain ⟨e00, e01, e10, e11⟩ := rotZ_mul_rotY_mul_rotZ_entries_all a b c
  have hP00 : (Real.cos a * Real.cos b * Real.cos c - Real.sin a * Real.sin c) * s ^ 2
      = -(p * u * r + q * v) := by
    calc (Real.cos a * Real.cos b * Real.cos c - Real.sin a * Real.sin c) * s ^ 2
        = (s * Real.cos a) * Real.cos b * (s * Real.cos c)
            - (s * Real.sin a) * (s * Real.sin c) := by ring
      _ = p * r * (-u) - q * v := by rw [hsa, hcb, hsc, hssa, hss]
      _ = -(p * u * r + q * v) := by ring
  have hP01 : (-Real.cos a * Real.cos b * Real.sin c - Real.sin a * Real.cos c) * s ^ 2
      = q * u - p * v * r := by
    calc (-Real.cos a * Real.cos b * Real.sin c - Real.sin a * Real.cos c) * s ^ 2
        = -((s * Real.cos a) * Real.cos b * (s * Real.sin c))
            - (s * Real.sin a) * (s * Real.cos c) := by ring
      _ = -(p * r * v) - q * (-u) := by rw [hsa, hcb, hss, hssa, hsc]
      _ = q * u - p * v * r := by ring
  have hP10 : (Real.sin a * Real.cos b * Real.cos c + Real.cos a * Real.sin c) * s ^ 2
      = p * v - q * u * r := by
    calc (Real.sin a * Real.cos b * Real.cos c + Real.cos a * Real.sin c) * s ^ 2
        = (s * Real.sin a) * Real.cos b * (s * Real.cos c)
            + (s * Real.cos a) * (s * Real.sin c) := by ring
      _ = q * r * (-u) + p * v := by rw [hssa, hcb, hsc, hsa, hss]
      _ = p * v - q * u * r := by ring
  have hP11 : (-Real.sin a * Real.cos b * Real.sin c + Real.cos a * Real.cos c) * s ^ 2
      = -(p * u + q * v * r) := by
    calc (-Real.sin a * Real.cos b * Real.sin c + Real.cos a * Real.cos c) * s ^ 2
        = -((s * Real.sin a) * Real.cos b * (s * Real.sin c))
            + (s * Real.cos a) * (s * Real.cos c) := by ring
      _ = -(q * r * v) + p * (-u) := by rw [hssa, hcb, hss, hsa, hsc]
      _ = -(p * u + q * v * r) := by ring
  -- ## The nine entries
  obtain ⟨e02, e12, e22, e20, e21⟩ := rotZ_mul_rotY_mul_rotZ_entries a b c
  have hs2_ne : s ^ 2 ≠ 0 := pow_ne_zero 2 hs_ne
  have h00 : (rotZ a * rotY b * rotZ c) 0 0 = Q 0 0 := by
    rw [e00]
    exact mul_right_cancel₀ hs2_ne (hP00.trans hQ00.symm)
  have h01 : (rotZ a * rotY b * rotZ c) 0 1 = Q 0 1 := by
    rw [e01]
    exact mul_right_cancel₀ hs2_ne (hP01.trans hQ01.symm)
  have h10 : (rotZ a * rotY b * rotZ c) 1 0 = Q 1 0 := by
    rw [e10]
    exact mul_right_cancel₀ hs2_ne (hP10.trans hQ10.symm)
  have h11 : (rotZ a * rotY b * rotZ c) 1 1 = Q 1 1 := by
    rw [e11]
    exact mul_right_cancel₀ hs2_ne (hP11.trans hQ11.symm)
  have h02 : (rotZ a * rotY b * rotZ c) 0 2 = Q 0 2 := by
    rw [e02, ← hp, hsb]
    exact hsa
  have h12 : (rotZ a * rotY b * rotZ c) 1 2 = Q 1 2 := by
    rw [e12, ← hq, hsb]
    exact hssa
  have h22 : (rotZ a * rotY b * rotZ c) 2 2 = Q 2 2 := by
    rw [e22, ← hr]
    exact hcb
  have h20 : (rotZ a * rotY b * rotZ c) 2 0 = Q 2 0 := by
    rw [e20, ← hu, hsb]
    linarith [hsc]
  have h21 : (rotZ a * rotY b * rotZ c) 2 1 = Q 2 1 := by
    rw [e21, ← hv, hsb]
    exact hss
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The mirrored branch of the reconstruction: joints 4 and 6 turned by `π`, the middle angle
the other way round, rebuilding the same `Q`.

`atan2`'s other branch for the two outer joints returns `(a + π, β, c + π)` where the direct
branch returned `(a, -β, c)`; either rebuilds the same `Q`, which is what lets the solver return
both. Nothing new is needed - `wristRotation_mirror` says the mirrored triple *is* the direct
one's rotation, so the direct reconstruction closes it. -/
theorem wristRotation_reconstruct_mirror {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Qᵀ * Q = 1) (hdet : Q.det = 1) (hne : (Q 0 2, Q 1 2) ≠ (0, 0)) :
    wristRotation (atan2 (Q 1 2) (Q 0 2) + Real.pi)
      (atan2 (hypot (Q 0 2) (Q 1 2)) (Q 2 2))
      (atan2 (Q 2 1) (-(Q 2 0)) + Real.pi) = Q := by
  -- `wristRotation_mirror` at the *negated* middle angle: its left-hand side then carries
  -- `-(-β)`, which `neg_neg` folds back to the `β` this statement asks for.
  have hmirror := wristRotation_mirror (atan2 (Q 1 2) (Q 0 2))
    (-(atan2 (hypot (Q 0 2) (Q 1 2)) (Q 2 2))) (atan2 (Q 2 1) (-(Q 2 0)))
  simp only [neg_neg] at hmirror
  rw [hmirror]
  exact wristRotation_reconstruct hQ hdet hne

/-- The wrist-singularity branch: with the third column vertical (`Q 0 2 = Q 1 2 = 0`) joints 4
and 6 share an axis and only `θ4 + θ6` is observable, so the solver holds joint 4 at zero and
reads joint 6 off the flattened matrix `rotY θ5 * Q` with `θ5 = atan2 0 (Q 2 2)`, which is `0`
or `π` here. This is `kinematics.py`'s `flattened = Ry(theta5) * relative_rotation` step, with
`θ5` the positive `atan2` - `rotY` does not see the sign at the singularity, both sines being
zero. -/
theorem wristRotation_reconstruct_flat {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Qᵀ * Q = 1) (hdet : Q.det = 1) (h02 : Q 0 2 = 0) (h12 : Q 1 2 = 0) :
    wristRotation 0 (atan2 0 (Q 2 2))
      (atan2 ((rotY (atan2 0 (Q 2 2)) * Q) 1 0) ((rotY (atan2 0 (Q 2 2)) * Q) 0 0)) = Q := by
  set r : ℝ := Q 2 2 with hr
  set b : ℝ := atan2 0 r with hb
  set c : ℝ := atan2 ((rotY b * Q) 1 0) ((rotY b * Q) 0 0) with hc
  -- ## The third column is `(0, 0, r)` with `r ^ 2 = 1`
  have hcol3 : Q 0 2 ^ 2 + Q 1 2 ^ 2 + Q 2 2 ^ 2 = 1 := by
    have h : (Qᵀ * Q) 2 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 2 := by rw [hQ]
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, pow_two] using h
  have hr2 : r ^ 2 = 1 := by
    have h := hcol3
    rw [h02, h12, ← hr] at h
    simpa using h
  -- The third row is a unit vector too, so `r ^ 2 = 1` kills its first two entries.
  have hrow3 : Q 2 0 ^ 2 + Q 2 1 ^ 2 + Q 2 2 ^ 2 = 1 := by
    have h : (Q * Qᵀ) 2 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 2 := by
      rw [mul_transpose_eq_one_of_transpose_mul hQ]
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, pow_two] using h
  have hu : Q 2 0 = 0 := by
    have h := hrow3
    rw [← hr] at h
    exact sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (Q 2 1), h, hr2])
  have hv : Q 2 1 = 0 := by
    have h := hrow3
    rw [← hr] at h
    exact sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (Q 2 0), h, hr2])
  -- ## The two angles
  have hsb : Real.sin b = 0 := by rw [hb, sin_atan2, zero_div]
  have hr_ne : r ≠ 0 := by
    intro h0
    rw [h0] at hr2
    have h10 : (1 : ℝ) = 0 := by simpa using hr2.symm
    exact one_ne_zero h10
  have hrs : hypot r 0 = 1 := by
    rw [hypot, show r ^ 2 + 0 ^ 2 = 1 by nlinarith [hr2], Real.sqrt_one]
  have hcb : Real.cos b = r := by
    rw [hb, cos_atan2 (fun h0 => hr_ne (congrArg Prod.fst h0)), hrs, div_one]
  -- ## The flattened matrix
  -- Both sines vanish, so `rotY b` is the diagonal matrix `diag (r, 1, r)`.
  have hrotY : rotY b = !![r, 0, 0; 0, 1, 0; 0, 0, r] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotY, hsb, hcb]
  have hflat10 : (rotY b * Q) 1 0 = Q 1 0 := by
    rw [hrotY]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hflat00 : (rotY b * Q) 0 0 = r * Q 0 0 := by
    rw [hrotY]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  -- ## The top-left block of `Q`
  -- With `(Q 0 2, Q 1 2, Q 2 2) = (0, 0, r)` the two remaining columns of `Q` are orthonormal
  -- and the determinant `hdet` fixes the handedness: the block is a rotation when `r = 1` and a
  -- reflection when `r = -1`. Both cases are the two rows below.
  have hC1 : Q 0 0 ^ 2 + Q 1 0 ^ 2 = 1 := by
    have h : (Qᵀ * Q) 0 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 := by rw [hQ]
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, pow_two, hu] using h
  have hC2 : Q 0 1 ^ 2 + Q 1 1 ^ 2 = 1 := by
    have h : (Qᵀ * Q) 1 1 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 1 := by rw [hQ]
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, pow_two, hv] using h
  have hdet' : Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0 = r := by
    have h := hdet
    rw [Matrix.det_fin_three] at h
    rw [h02, h12, ← hr, hu, hv] at h
    ring_nf at h
    -- `h` is now `r * (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) = 1`; multiplying it by `r` and using
    -- `r * r = 1` leaves the product itself, which is the statement.
    have h1 : r * (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) = 1 := by linarith [h]
    have h2 : r * (r * (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0)) = r := by rw [h1, mul_one]
    rw [← mul_assoc, ← pow_two, hr2, one_mul] at h2
    exact h2
  -- The sum of the two squares below is `0` by the four relations above, so each of them
  -- vanishes; that is `Q 0 1 = -r * Q 1 0` and `Q 1 1 = r * Q 0 0`.
  have hsum : (Q 0 1 + r * Q 1 0) ^ 2 + (Q 1 1 - r * Q 0 0) ^ 2 = 0 := by
    calc (Q 0 1 + r * Q 1 0) ^ 2 + (Q 1 1 - r * Q 0 0) ^ 2
        = (Q 0 1 ^ 2 + Q 1 1 ^ 2) + r ^ 2 * (Q 0 0 ^ 2 + Q 1 0 ^ 2)
            - 2 * r * (Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0) := by ring
      _ = 1 + 1 * 1 - 2 * r * r := by rw [hC2, hC1, hdet', hr2]
      _ = 0 := by nlinarith [hr2]
  have hB : Q 0 1 = -r * Q 1 0 := by
    have hx : (Q 0 1 + r * Q 1 0) ^ 2 = 0 := by
      linarith [hsum, sq_nonneg (Q 1 1 - r * Q 0 0), sq_nonneg (Q 0 1 + r * Q 1 0)]
    linarith [sq_eq_zero_iff.mp hx]
  have hD : Q 1 1 = r * Q 0 0 := by
    have hx : (Q 1 1 - r * Q 0 0) ^ 2 = 0 := by
      linarith [hsum, sq_nonneg (Q 0 1 + r * Q 1 0), sq_nonneg (Q 1 1 - r * Q 0 0)]
    linarith [sq_eq_zero_iff.mp hx]
  -- ## The last joint
  -- The pair the solver reads is `(Q 1 0, r * Q 0 0)`, a unit vector, so its `atan2` is total
  -- up to that unit length.
  have hhyps : hypot (r * Q 0 0) (Q 1 0) = 1 := by
    -- `(r * Q 0 0) ^ 2 + Q 1 0 ^ 2` is `Q 0 0 ^ 2 + Q 1 0 ^ 2`, which column 1 makes `1`.
    have hsq : (r * Q 0 0) ^ 2 + Q 1 0 ^ 2 = 1 := by
      rw [mul_pow, hr2, one_mul, hC1]
    rw [hypot, hsq, Real.sqrt_one]
  have hc_sin : Real.sin c = Q 1 0 := by
    rw [hc, hflat10, hflat00, sin_atan2, hhyps, div_one]
  have hc_cos : Real.cos c = r * Q 0 0 := by
    have hne' : (r * Q 0 0, Q 1 0) ≠ (0, 0) := by
      intro h0
      have h1 : (r * Q 0 0) ^ 2 + Q 1 0 ^ 2 = 1 := by
        rw [← hypot_sq (r * Q 0 0) (Q 1 0), hhyps]
        ring
      have h0a : r * Q 0 0 = 0 := congrArg Prod.fst h0
      have h0b : Q 1 0 = 0 := congrArg Prod.snd h0
      rw [h0a, h0b] at h1
      have h10 : (1 : ℝ) = 0 := by simpa using h1.symm
      exact one_ne_zero h10
    rw [hc, hflat10, hflat00, cos_atan2 hne', hhyps, div_one]
  -- ## The nine entries
  have hwrist : wristRotation 0 b c = rotY (-b) * rotZ c := by simp [wristRotation]
  have hrotYneg : rotY (-b) = !![r, 0, 0; 0, 1, 0; 0, 0, r] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotY, Real.cos_neg, Real.sin_neg, hsb, hcb]
  rw [hwrist, hrotYneg]
  -- The product is the diagonal matrix times `rotZ c`, so it is `rotZ`-shaped with the first
  -- two rows scaled by `r`.
  have hprod : !![r, 0, 0; 0, 1, 0; 0, 0, r] * rotZ c
      = !![r * Real.cos c, -(r * Real.sin c), 0; Real.sin c, Real.cos c, 0; 0, 0, r] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, rotZ]
  -- `r * r = 1` undoes the scaling of the first row.
  have hrr : r * (r * Q 0 0) = Q 0 0 := by rw [← mul_assoc, ← pow_two, hr2, one_mul]
  rw [hprod]
  -- Each entry is one of the block relations above, or `r * r = 1`.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hc_sin, hc_cos, hB, hD, hrr, ← hr, hu, hv, h02, h12]

end Kinematics
