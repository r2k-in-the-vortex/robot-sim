module
-- The public imports cover everything the exported theorem's statement and proof
-- mention; the file is deliberately independent of `Motion.Basic`.
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Order.OrderClosed

noncomputable section
open Set Filter
open scoped Topology

@[expose] public section

/-!
# Piecewise `C^n` gluing

The corrected gluing lemma for `docs/motion_control.md` §4.2. Two globally `C^n` real
functions that agree in value and in their first `n` derivatives at `c` glue to a globally
`C^n` function. The draft's `∀ k < n` condition was off by one: `C^n` gluing needs the
`n`-th derivative to match too, and one-sided `iteratedDeriv` at an endpoint is a junk
value. Requiring global smoothness of the pieces avoids every one-sided issue; every
segment of a motion profile is a polynomial, so this is all that is needed.

Mathlib has no ready piecewise lemma (`ContDiffOn.union_of_isOpen` requires open sets);
this proof is the special case the motion layer uses.
-/

namespace Motion

/-- Two globally `C^n` real functions that agree in value and in their first `n`
derivatives at `c` glue to a globally `C^n` function. -/
theorem contDiff_piecewise_le {n : ℕ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (h : ∀ k ≤ n, iteratedDeriv k f c = iteratedDeriv k g c) :
    ContDiff ℝ n (fun t => if t ≤ c then f t else g t) := by
  induction n generalizing f g with
  | zero =>
      have hf0 : (0 : WithTop ℕ∞) = (↑(0 : ℕ) : WithTop ℕ∞) := by simp
      rw [show (↑(0 : ℕ) : WithTop ℕ∞) = 0 from by simp, contDiff_zero]
      refine continuous_if_le continuous_id continuous_const
        hf.continuous.continuousOn hg.continuous.continuousOn ?_
      intro x hx
      have h0 := h 0 (Nat.zero_le 0)
      simpa [hx] using h0
  | succ n ih =>
      have hstep : ∀ x : ℝ, HasDerivAt (fun t => if t ≤ c then f t else g t)
          (if x ≤ c then deriv f x else deriv g x) x := by
        intro x
        by_cases hx : x < c
        · have hev : (fun t => if t ≤ c then f t else g t) =ᶠ[𝓝 x] f := by
            filter_upwards [Iio_mem_nhds hx] with t ht
            have ht' : t < c := ht
            simp [le_of_lt ht']
          have hfd : HasDerivAt f (deriv f x) x :=
            (hf.differentiable (by simp)).differentiableAt.hasDerivAt
          have := hfd.congr_of_eventuallyEq hev
          simpa [if_pos (le_of_lt hx)] using this
        · by_cases hcx : c < x
          · have hev : (fun t => if t ≤ c then f t else g t) =ᶠ[𝓝 x] g := by
              filter_upwards [Ioi_mem_nhds hcx] with t ht
              have ht' : c < t := ht
              simp [not_le.mpr ht']
            have hgd : HasDerivAt g (deriv g x) x :=
              (hg.differentiable (by simp)).differentiableAt.hasDerivAt
            have := hgd.congr_of_eventuallyEq hev
            simpa [if_neg (not_le.mpr hcx)] using this
          · have hxc : x = c := le_antisymm (le_of_not_gt hcx) (le_of_not_gt hx)
            subst x
            have hdf : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) (deriv f c) (Iic c) c := by
              refine ((hf.differentiable (by simp)).differentiableAt.hasDerivAt.hasDerivWithinAt).congr ?_ ?_
              · intro y hy
                have hy' : y ≤ c := hy
                simp [hy']
              · simp
            have hfcg : f c = g c := by
              have h0 := h 0 (Nat.zero_le (n + 1))
              simpa using h0
            have hdg : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) (deriv g c) (Ici c) c := by
              refine ((hg.differentiable (by simp)).differentiableAt.hasDerivAt.hasDerivWithinAt).congr ?_ ?_
              · intro y hy
                have hy' : c ≤ y := hy
                by_cases hyc : y ≤ c
                · have hye : y = c := le_antisymm hyc hy'
                  subst y
                  simp [hfcg]
                · simp [hyc]
              · simp [hfcg]
            have hfg' : deriv f c = deriv g c := by
              have h1 := h 1 (Nat.succ_le_succ (Nat.zero_le n))
              simpa [iteratedDeriv_one] using h1
            rw [← hfg'] at hdg
            have hunion := hdf.union hdg
            rw [Iic_union_Ici] at hunion
            simpa using hunion
      rw [show (↑(n + 1) : WithTop ℕ∞) = (↑n : WithTop ℕ∞) + 1 from by simp,
        contDiff_succ_iff_deriv]
      refine ⟨fun x => (hstep x).differentiableAt, ?_, ?_⟩
      · intro hn
        exact absurd hn (by simp)
      · rw [deriv_eq hstep]
        exact ih hf.deriv' hg.deriv' (fun k hk => by
          rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
          exact h (k + 1) (Nat.succ_le_succ hk))

end Motion
