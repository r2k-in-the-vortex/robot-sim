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
needs and that `Kinematics.lean` does not already provide: the four facts below, the
reconstruction theorems built out of them, and the read-off theorems that are the same argument
read the other way.

* `rotZ_pi_mul_rotY_mul_rotZ_pi` - a half-turn about z conjugated with a y-rotation;
* `wristRotation_mirror` - the two wrist branches are literally the same rotation, which is what
  removes the sign case split from the reconstruction;
* `rotZ_mul_rotY_mul_rotZ_entries_all` - the four entries of a ZYZ product left out by
  `Kinematics.rotZ_mul_rotY_mul_rotZ_entries`;
* `mul_transpose_eq_one_of_transpose_mul` - the direction of orthogonality that
  `Kinematics.mul_orth` cannot produce;
* `wristRotation_hypot_third_column` and the three `wristRotation_read_*` theorems - the three
  angles the solver reads off a *commanded* wrist are the commanded ones, which is the direction a
  completeness statement needs and the reconstruction cannot supply: it starts from a rotation,
  not from an angle triple;
* `wristRotation_singular_flat`, `wristRotation_zero_middle` and `wristRotation_pi_middle` - the
  wrist singularity, where only `θ4 + θ6` (or `θ4 - θ6`) is observable at all.

`wristRotation_reconstruct` then puts them together: the three angles the solver's wrist step
reads off a rotation rebuild it, in either `atan2` branch
(`wristRotation_reconstruct_mirror`) and at the wrist singularity
(`wristRotation_reconstruct_flat`). The middle angle is passed to `wristRotation` *negated*,
because that definition already carries the negation of `θ5`: the ZYZ middle angle `γ` of `Q` is
recovered as `θ5 = -γ`, `hypot` is never negative, and the two branches the solver returns are
exactly `(a, -β, c)` and `(a + π, β, c + π)`.

The read-off theorems below run the same three angles through the product instead of the product
through the angles: `wristRotation_read_theta4_coe_angle` and its two siblings say that the solver
reads `a`, `β` and `c` back out of `wristRotation a β c`, the two outer ones up to the one
half-turn offset - exactly the offset `wristRotation_reconstruct_mirror` mirrors - and the last
three theorems record what the product still says once `sin β = 0` and the three angles have
stopped being separately observable. -/

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

/-! ## The reads invert the product

The reconstruction turns a rotation into angles; a completeness proof needs the other direction,
that the angles the solver *reads* off a commanded wrist are the commanded ones. The theorems
below are that direction: `wristRotation_hypot_third_column` and the three `wristRotation_read_*`
are the solver's own `atan2` calls applied to a `wristRotation`, each returning the angle that went
in, and the last three say what is left of the product once `sin β = 0` and the three angles have
stopped being separately observable at all.

`wristRotation a β c` is `rotZ a * rotY (-β) * rotZ c`, so reading
`Kinematics.rotZ_mul_rotY_mul_rotZ_entries` at `(a, -β, c)` supplies the five numbers the solver's
reads are built from: `Q 0 2 = -sin β · cos a`, `Q 1 2 = -sin β · sin a`, `Q 2 2 = cos β`,
`Q 2 0 = sin β · cos c` and `Q 2 1 = -sin β · sin c`. No other entry of the product enters a read,
so every theorem below is a statement about those five numbers.

The two outer reads carry the *same* offset, `if 0 < Real.sin β then Real.pi else 0`, because the
two pairs they read are `(-sin β · cos x, -sin β · sin x)` with the same factor `-sin β` in front
of the same unit-circle pair `(cos x, sin x)`; only the sign of that factor can move the angle, and
it moves both by the same half turn - which is what lets the solver's single `mirror` flag serve
joints 4 and 6 at once. The hypothesis `Real.sin β ≠ 0` on those three reads is the non-vanishing
the scale needs for the pair to have a direction at all, the same condition under which
`wristRotation_reconstruct` applies; the singular case it excludes is what the last three theorems
describe, where the product no longer determines the three angles separately and only `θ4 ± θ6`
survives.
-/

/-- The length of the third column's `xy` part of a ZYZ product is `|Real.sin β|`: the two entries
`-sin β · cos a` and `-sin β · sin a` are a common factor `-sin β` times the point of the unit
circle at angle `a`, and a length cannot remember the sign of that factor - only its absolute
value. This is the number the solver's middle read, `atan2 (hypot Q₀₂ Q₁₂) Q₂₂`, is taken of, and
it is why `RealAtan2.hypot_mul_cos_sin` is stated with an absolute value: with it the third
column's length collapses to `|sin β|` in one step, with no case split on the sign of the middle
angle's sine. -/
theorem wristRotation_hypot_third_column (a β c : ℝ) :
    hypot ((wristRotation a β c) 0 2) ((wristRotation a β c) 1 2) = |Real.sin β| := by
  obtain ⟨h02, h12, -, -, -⟩ := rotZ_mul_rotY_mul_rotZ_entries a (-β) c
  -- Unfold to the product the entry lemma is stated for, read the two entries off it, and let
  -- `hypot_mul_cos_sin` take the common factor out - the `-β` the entry lemma is called at is
  -- what turns the factor into the plain `-sin β` the last step needs `abs_neg` for.
  simp only [wristRotation]
  rw [h02, h12, Real.sin_neg, hypot_mul_cos_sin, abs_neg]

/-- The solver's joint-4 read-off inverts `wristRotation`: the angle of the third column's `(x, y)`
part is the commanded `a`, plus a half turn exactly when `sin β` is negative.

The pair read is `(Q 1 2, Q 0 2) = -sin β · (sin a, cos a)`, the direction of joint 4 scaled by
`-sin β`; a positive scale moves no angle, a negative one costs exactly a half turn, and the `if`
in the statement is that half turn. That is also why the hypothesis is `Real.sin β ≠ 0` rather
than a sign: the factor has to be *nonzero* for the pair to have a direction at all - at
`sin β = 0` the third column is vertical and the solver takes its flat branch instead - and the two
signs of `sin β` are the two `atan2` branches, which the statement keeps apart through the `if`
rather than through a case split of its own. -/
theorem wristRotation_read_theta4_coe_angle (a β c : ℝ) (h : Real.sin β ≠ 0) :
    (atan2 ((wristRotation a β c) 1 2) ((wristRotation a β c) 0 2) : Real.Angle) =
      (a : Real.Angle) + (if 0 < Real.sin β then Real.pi else 0) := by
  obtain ⟨h02, h12, -, -, -⟩ := rotZ_mul_rotY_mul_rotZ_entries a (-β) c
  simp only [wristRotation]
  -- Both entries carry `sin (-β)`, and `-sin β` is the scale the two multiplication lemmas are
  -- stated for.
  rw [h12, h02, Real.sin_neg]
  -- The pair the two lemmas are given is `(cos a, sin a)`, a point of the unit circle, so it
  -- cannot be the origin and `atan2_neg_mul_coe_angle`'s non-vanishing hypothesis is free; it
  -- has to be proved rather than assumed because `h` is a hypothesis about `sin β`, not about `a`.
  have hne : (Real.cos a, Real.sin a) ≠ (0, 0) := by
    intro h0
    have hc : Real.cos a = 0 := congrArg Prod.fst h0
    have hs : Real.sin a = 0 := congrArg Prod.snd h0
    have h1 : (0 : ℝ) = 1 := by simpa [hc, hs] using Real.sin_sq_add_cos_sq a
    exact one_ne_zero h1.symm
  -- `h` leaves exactly two cases, and they are the two branches: the sign of `-sin β` is the
  -- opposite of the sign of `sin β`, so a negative `sin β` is the *positive* scale.
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- `sin β < 0`: the scale is positive and the read is the angle itself, with no offset.
    rw [atan2_pos_mul_coe_angle (neg_pos.mpr hneg), atan2_cos_sin_coe_angle a,
      ite_eq_right (not_lt.mpr hneg.le), Real.Angle.coe_zero, add_zero]
  · -- `sin β > 0`: the scale is negative, which is exactly the half turn the offset names.
    rw [atan2_neg_mul_coe_angle (neg_lt_zero.mpr hpos) hne, atan2_cos_sin_coe_angle a,
      ite_eq_left hpos]

/-- The solver's joint-6 read-off inverts `wristRotation`: the angle of the third row's `(y, -x)`
part is the commanded `c`, plus the *same* half turn the joint-4 read carries.

`atan2 (Q 2 1) (-(Q 2 0))` is taken of `(-sin β · sin c, -sin β · cos c)`, the same `-sin β` scale
of `(sin c, cos c)` that joint 4's read sees of `(sin a, cos a)` - only the unit-circle direction
differs, so the sign of the scale, and hence the offset, is the same term as in
`wristRotation_read_theta4_coe_angle`. That is the reason the solver's one `mirror` flag serves
both joints: the entry lemma states the `Q 2 0` entry with its minus sign in front of the product
rather than on the factor, which is exactly why the solver's call negates that entry before
reading it, and the two minus signs have to cancel for the factor to come out as `-sin β` again. -/
theorem wristRotation_read_theta6_coe_angle (a β c : ℝ) (h : Real.sin β ≠ 0) :
    (atan2 ((wristRotation a β c) 2 1) (-((wristRotation a β c) 2 0)) : Real.Angle) =
      (c : Real.Angle) + (if 0 < Real.sin β then Real.pi else 0) := by
  obtain ⟨-, -, -, h20, h21⟩ := rotZ_mul_rotY_mul_rotZ_entries a (-β) c
  simp only [wristRotation]
  -- `Q 2 1` is the plain product; `-Q 2 0` needs its negation moved onto the factor, which is
  -- what `neg_mul` does and why the statement reads the *negated* entry.
  have h21' : (rotZ a * rotY (-β) * rotZ c) 2 1 = (-Real.sin β) * Real.sin c := by
    rw [h21, Real.sin_neg]
  have h20' : -((rotZ a * rotY (-β) * rotZ c) 2 0) = (-Real.sin β) * Real.cos c := by
    rw [h20, Real.sin_neg]
    ring
  rw [h21', h20']
  -- From here the read is the joint-4 read with `c` in place of `a`, offset included.
  have hne : (Real.cos c, Real.sin c) ≠ (0, 0) := by
    intro h0
    have hc : Real.cos c = 0 := congrArg Prod.fst h0
    have hs : Real.sin c = 0 := congrArg Prod.snd h0
    have h1 : (0 : ℝ) = 1 := by simpa [hc, hs] using Real.sin_sq_add_cos_sq c
    exact one_ne_zero h1.symm
  rcases lt_or_gt_of_ne h with hneg | hpos
  · rw [atan2_pos_mul_coe_angle (neg_pos.mpr hneg), atan2_cos_sin_coe_angle c,
      ite_eq_right (not_lt.mpr hneg.le), Real.Angle.coe_zero, add_zero]
  · rw [atan2_neg_mul_coe_angle (neg_lt_zero.mpr hpos) hne, atan2_cos_sin_coe_angle c,
      ite_eq_left hpos]

/-- The solver's middle read-off, on the branch sign the solver uses: the signed
`atan2 (hypot Q₀₂ Q₁₂) Q₂₂` - the `hypot` being `|sin β|` - is the commanded `β` exactly, not
merely up to a half turn.

The solver takes its sign from `sin β` itself, `1` where the sine is positive and `-1` where it is
negative, which is the integer `if` in the statement; and that is exactly the sign the read needs.
`atan2 (|sin β|) (cos β)` is `β` when `sin β` is positive, and when `sin β` is negative it is `-β`
- `|sin β|` is then `sin (-β)` and `cos β` is `cos (-β)`, so the pair read is the pair of the
*negated* angle - which the `-1` brings back to `β`. The hypothesis `Real.sin β ≠ 0` is needed here
for a different reason than in the two outer reads: at the singularity `hypot Q₀₂ Q₁₂` is `0`, so
there is no `(cos, sin)` pair left to read an angle off at all, and the solver has to flatten the
wrist instead of reading this. -/
theorem wristRotation_read_theta5_coe_angle (a β c : ℝ) (h : Real.sin β ≠ 0) :
    ((((if 0 < Real.sin β then (1 : ℤ) else -1) : ℤ) : ℝ) *
        atan2 (hypot ((wristRotation a β c) 0 2) ((wristRotation a β c) 1 2))
          ((wristRotation a β c) 2 2) : Real.Angle) = (β : Real.Angle) := by
  obtain ⟨-, -, h22, -, -⟩ := rotZ_mul_rotY_mul_rotZ_entries a (-β) c
  -- Both halves of the read are already named: the `hypot` is the third column's length and the
  -- second entry is `cos (-β)`, so the middle angle is the only thing left to identify.
  rw [wristRotation_hypot_third_column a β c]
  simp only [wristRotation]
  rw [h22, Real.cos_neg]
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- `sin β < 0`: `|sin β|` is `sin (-β)` and `cos β` is `cos (-β)`, so the read is the angle
    -- `-β`; the statement's `-1` negates it back, and the two `coe_neg`s are where the inner
    -- negation comes back out of the `Real.Angle` coercion.
    rw [ite_eq_right (not_lt.mpr hneg.le), Int.cast_neg, Int.cast_one, neg_one_mul,
      abs_of_neg hneg, ← Real.sin_neg, ← Real.cos_neg, Real.Angle.coe_neg, atan2_cos_sin_coe_angle,
      Real.Angle.coe_neg, neg_neg]
  · -- `sin β > 0`: `|sin β|` is `sin β`, so the read is `β` itself and the branch sign is `1`.
    rw [ite_eq_left hpos, Int.cast_one, one_mul, abs_of_pos hpos, atan2_cos_sin_coe_angle]

/-- At the wrist singularity the flat split loses nothing: with `sin β = 0` the middle factor of
`wristRotation a β c` is a diagonal matrix, so the product depends on `a` and `c` only through the
combination that diagonal lets through - `a + c` when `cos β = 1`, `c - a` when `cos β = -1` - and
the solver's split, which holds `θ4` at zero and hands the whole combination to `θ6`, rebuilds the
same product.

`sin β = 0` puts `β` at a multiple of `π`, and `sin² + cos² = 1` then leaves just the two cases
`cos β = ±1`, which are the two halves of the proof. With `cos β = 1` the middle factor is the
identity, `rotY (-β) = 1`, and the two z rotations simply add - which is the `a` the statement's
`if` picks. With `cos β = -1` it is `diag (-1, 1, -1)`, and such a diagonal turns a z rotation into
the z rotation of the *opposite* angle: `rotZ a * D = D * rotZ (-a)`, so `rotZ a` passes from the
left of the middle factor to the right negated and the product sees `c - a` - which is the `-a`
the `if` picks. Both cases are why the `if` is on the sign of `cos β` and not, say, on whether the
product is `rotZ (a + c)` or `rotZ (c - a)`: the two are the two halves of the singular set. -/
theorem wristRotation_singular_flat (a β c : ℝ) (h : Real.sin β = 0) :
    wristRotation a β c = wristRotation 0 β (c + (if 0 < Real.cos β then a else -a)) := by
  -- `sin β = 0` leaves `cos β = ±1`; `sq_eq_one_iff` is that step, and the two cases below are
  -- the two halves of the statement's `if`.
  have hcos2 : Real.cos β ^ 2 = 1 := by
    simpa [h] using Real.sin_sq_add_cos_sq β
  rcases sq_eq_one_iff.mp hcos2 with hcos | hcos
  · -- `cos β = 1`: the middle factor is the identity, and `rotZ_add` adds the two z rotations.
    have hsin' : Real.sin (-β) = 0 := by rw [Real.sin_neg, h, neg_zero]
    have hcos' : Real.cos (-β) = 1 := by rw [Real.cos_neg, hcos]
    have hY : rotY (-β) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rotY, hsin', hcos']
    -- The statement's `if` is true in this case, and `hY` collapses the middle factor, so both
    -- sides are `rotZ a * rotZ c` up to the order of the sum.
    rw [hcos, ite_eq_left zero_lt_one]
    simp only [wristRotation, rotZ_zero, hY, Matrix.one_mul, Matrix.mul_one]
    rw [rotZ_add a c, add_comm a c]
  · -- `cos β = -1`: the middle factor is `diag (-1, 1, -1)`, which conjugates the two z rotations
    -- - `rotZ a` moves to the right of it as `rotZ (-a)` - so the sum is taken the other way.
    have hsin' : Real.sin (-β) = 0 := by rw [Real.sin_neg, h, neg_zero]
    have hcos' : Real.cos (-β) = -1 := by rw [Real.cos_neg, hcos]
    have hD : rotY (-β) = !![(-1 : ℝ), 0, 0; 0, 1, 0; 0, 0, -1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rotY, hsin', hcos']
    have hconj : rotZ a * rotY (-β) = rotY (-β) * rotZ (-a) := by
      -- `hD` is what makes the two sides match entry by entry: with the literal diagonal in
      -- place of `rotY (-β)` every entry is a product of `±1`, `sin a` and `cos a` once `simp`
      -- has evaluated `cos (-a)` and `sin (-a)`, and its arithmetic normalisation closes them.
      rw [hD]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three]
    rw [hcos, ite_eq_right (not_lt.mpr (neg_nonpos.mpr zero_le_one))]
    -- `hconj` is the pass-through that names the combination the `if` picked, and `rotZ_add`
    -- then collects the two z rotations into one.
    simp only [wristRotation, rotZ_zero, Matrix.one_mul]
    rw [hconj, Matrix.mul_assoc (rotY (-β)) (rotZ (-a)) (rotZ c), rotZ_add,
      show -a + c = c + -a by ring]

/-- With `θ5 = 0` the wrist is a single z rotation: only `θ4 + θ6` is observable.

Written out, this is the `cos β = 1` half of `wristRotation_singular_flat` at `β = 0`, and it is
the statement `mathematics.md`'s section 8 makes when it says that at `θ5 = 0` only `θ4 + θ6` is
observable: the middle factor is the identity, so `wristRotation a 0 c` and `wristRotation 0 0
(a + c)` are the same rotation and nothing in the product can tell the two outer angles apart -
the solver may hold `θ4` at zero and hand the sum to `θ6`, which is exactly the flat branch's
`atan2` read of `rotZ θ6`. -/
theorem wristRotation_zero_middle (a c : ℝ) : wristRotation a 0 c = wristRotation 0 0 (a + c) := by
  -- `rotY 0 = 1` and `rotZ 0 = 1`, leaving `rotZ a * rotZ c` against `rotZ (a + c)`.
  simp only [wristRotation, neg_zero, rotY_zero, rotZ_zero, Matrix.one_mul, Matrix.mul_one]
  rw [rotZ_add a c]

/-- With `θ5 = π` the half-turn in the middle makes only `θ4 - θ6` observable.

This is `wristRotation_singular_flat` at `β = π`, where `cos β = -1` picks the `-a` branch: the
middle factor is the half-turn about y, and conjugating a z rotation with it turns the angle
negative, so the product sees `θ4 - θ6` and not their sum - the other of the two sentences of
`mathematics.md`'s section 8, and the reason the flat branch's `atan2` reads a *difference* when
`θ5` comes out at `π` rather than at `0`. -/
theorem wristRotation_pi_middle (a c : ℝ) : wristRotation a Real.pi c = wristRotation 0 Real.pi (c - a) := by
  -- The half-turn about y is `diag (-1, 1, -1)`, and that diagonal is the conjugation above; it
  -- is stated for `-π` because that is the angle `wristRotation` hands its middle factor.
  have hconj : rotZ a * rotY (-Real.pi) = rotY (-Real.pi) * rotZ (-a) := by
    -- No `ring` after the expansion: every entry here is a product of at most three of
    -- `±1`, `sin a` and `cos a` once `simp` has evaluated `cos (-π)`, `sin (-π)`, `cos (-a)`
    -- and `sin (-a)`, and `simp`'s arithmetic normalisation already sees that the two sides
    -- match - there is no trigonometric addition to expand.
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, rotY, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [wristRotation, rotZ_zero, Matrix.one_mul]
  rw [hconj, Matrix.mul_assoc (rotY (-Real.pi)) (rotZ (-a)) (rotZ c), rotZ_add,
    show -a + c = c - a by ring]

end Kinematics
