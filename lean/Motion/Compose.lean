module
-- These are `public import`s because the declarations below are exported
-- (`@[expose] public section`): everything their types and bodies mention has to be
-- part of this module's public interface, or importers cannot use them.
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

noncomputable section

@[expose] public section

/-!
# Composition bounds for a reparameterised trajectory

This file is `docs/motion_control.md` §4.4's master composition lemma, proved once and
independently of the planner so that both the time-scaling supervisor and the Cartesian
certificate (§5, M5) can consume it.

For `C³` functions `f` (the reference) and `σ` (the clock or path parameter), with
derivative bounds `M1 M2 M3` on `f` and `S1 S2 S3` on `σ`, the chain rule gives

* `(f ∘ σ)'   = f' σ'`,
* `(f ∘ σ)''  = f'' (σ')² + f' σ''`,
* `(f ∘ σ)''' = f''' (σ')³ + 3 f'' σ' σ'' + f' σ''',

and the triangle inequality turns those into the three bounds `L1 L2 L3` once the three
arithmetic inequalities `h1 h2 h3` hold. The identities are Mathlib's
`iteratedDeriv_comp_two` and `iteratedDeriv_comp_three`.

## The range hypothesis

`hσmaps` is not part of the displayed statement in §4.4, but it is necessary: `hf1`–`hs3`
bound `f`'s derivatives only on `(a, b)`, while the chain rule evaluates them at `σ t`.
Without `σ (Ioo a b) ⊆ Ioo a b` the statement is false: take `f x = max (x - 1) 0 ^ 4`
and `σ t = t + 10` on `(0, 1)`. Then `f` vanishes on `(-∞, 1]`, so `M1 = M2 = M3 = 0`
and `L1 = L2 = L3 = 0`, but `deriv (f ∘ σ) t = 4 (t + 9)³ ≠ 0`. The Cartesian instance
in §5 carries the same condition as `hsmap`.
-/

namespace Motion

/-- **Master composition lemma.** If `f` is `C³` on `(a, b)` with its first three
derivatives bounded by `M1 M2 M3`, `σ` is `C³` on `(a, b)` with derivatives bounded by
`S1 S2 S3`, and `σ` maps `(a, b)` into itself, then the composition `f ∘ σ` satisfies the
velocity, acceleration and jerk bounds `L1 L2 L3`, provided the three bound inequalities
`h1 h2 h3` hold.

The third conclusion is the product rule expansion of the third derivative followed by
the triangle inequality; the hypotheses `hf1`–`hs3` supply each factor's bound. -/
theorem comp_bounds
    (f σ : ℝ → ℝ) {a b : ℝ}
    (M1 M2 M3 S1 S2 S3 L1 L2 L3 : ℝ)
    (hf : ContDiffOn ℝ 3 f (Set.Ioo a b))
    (hσ : ContDiffOn ℝ 3 σ (Set.Ioo a b))
    (hσmaps : Set.MapsTo σ (Set.Ioo a b) (Set.Ioo a b))
    (hf1 : ∀ t ∈ Set.Ioo a b, |deriv f t| ≤ M1)
    (hf2 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 2 f t| ≤ M2)
    (hf3 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 3 f t| ≤ M3)
    (hs1 : ∀ t ∈ Set.Ioo a b, |deriv σ t| ≤ S1)
    (hs2 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 2 σ t| ≤ S2)
    (hs3 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 3 σ t| ≤ S3)
    (h1 : M1 * S1 ≤ L1)
    (h2 : M2 * S1 ^ 2 + M1 * S2 ≤ L2)
    (h3 : M3 * S1 ^ 3 + 3 * M2 * S1 * S2 + M1 * S3 ≤ L3) :
    (∀ t ∈ Set.Ioo a b, |deriv (fun t => f (σ t)) t| ≤ L1) ∧
    (∀ t ∈ Set.Ioo a b, |iteratedDeriv 2 (fun t => f (σ t)) t| ≤ L2) ∧
    (∀ t ∈ Set.Ioo a b, |iteratedDeriv 3 (fun t => f (σ t)) t| ≤ L3) := by
  by_cases hne : (Set.Ioo a b).Nonempty
  · -- The interval is nonempty, so each bound constant is nonnegative: the absolute value
    -- of the corresponding derivative at any point of the interval is one.
    obtain ⟨t₀, ht₀⟩ := hne
    have hM1 : 0 ≤ M1 := (abs_nonneg (deriv f t₀)).trans (hf1 t₀ ht₀)
    have hM2 : 0 ≤ M2 := (abs_nonneg (iteratedDeriv 2 f t₀)).trans (hf2 t₀ ht₀)
    have hM3 : 0 ≤ M3 := (abs_nonneg (iteratedDeriv 3 f t₀)).trans (hf3 t₀ ht₀)
    have hS1 : 0 ≤ S1 := (abs_nonneg (deriv σ t₀)).trans (hs1 t₀ ht₀)
    have hS2 : 0 ≤ S2 := (abs_nonneg (iteratedDeriv 2 σ t₀)).trans (hs2 t₀ ht₀)
    have hS3 : 0 ≤ S3 := (abs_nonneg (iteratedDeriv 3 σ t₀)).trans (hs3 t₀ ht₀)
    refine ⟨?_, ?_, ?_⟩
    · -- First derivative: `(f ∘ σ)' = f' σ'`.
      intro t ht
      have hft : ContDiffAt ℝ 3 f (σ t) :=
        hf.contDiffAt (isOpen_Ioo.mem_nhds (hσmaps ht))
      have hσt : ContDiffAt ℝ 3 σ t := hσ.contDiffAt (isOpen_Ioo.mem_nhds ht)
      have hd : deriv (fun t => f (σ t)) t = deriv f (σ t) * deriv σ t :=
        deriv_comp t (hft.differentiableAt (by norm_num))
          (hσt.differentiableAt (by norm_num))
      rw [hd, abs_mul]
      calc
        |deriv f (σ t)| * |deriv σ t| ≤ M1 * S1 :=
          mul_le_mul (hf1 (σ t) (hσmaps ht)) (hs1 t ht) (abs_nonneg _) hM1
        _ ≤ L1 := h1
    · -- Second derivative: `(f ∘ σ)'' = f'' (σ')² + f' σ''`.
      intro t ht
      have hft : ContDiffAt ℝ 3 f (σ t) :=
        hf.contDiffAt (isOpen_Ioo.mem_nhds (hσmaps ht))
      have hσt : ContDiffAt ℝ 3 σ t := hσ.contDiffAt (isOpen_Ioo.mem_nhds ht)
      have h2eq : iteratedDeriv 2 (fun t => f (σ t)) t =
          iteratedDeriv 2 f (σ t) * deriv σ t ^ 2 + deriv f (σ t) * iteratedDeriv 2 σ t :=
        iteratedDeriv_comp_two (g := f) (f := σ) (x := t)
          (hft.of_le (by norm_num)) (hσt.of_le (by norm_num))
      have hsq : |deriv σ t| ^ 2 ≤ S1 ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg (deriv σ t)) (hs1 t ht) 2
      have hprod1 : |iteratedDeriv 2 f (σ t)| * |deriv σ t| ^ 2 ≤ M2 * S1 ^ 2 :=
        mul_le_mul (hf2 (σ t) (hσmaps ht)) hsq (pow_nonneg (abs_nonneg _) 2) hM2
      have hprod2 : |deriv f (σ t)| * |iteratedDeriv 2 σ t| ≤ M1 * S2 :=
        mul_le_mul (hf1 (σ t) (hσmaps ht)) (hs2 t ht) (abs_nonneg _) hM1
      calc
        |iteratedDeriv 2 (fun t => f (σ t)) t|
            = |iteratedDeriv 2 f (σ t) * deriv σ t ^ 2 +
                deriv f (σ t) * iteratedDeriv 2 σ t| := by rw [h2eq]
        _ ≤ |iteratedDeriv 2 f (σ t) * deriv σ t ^ 2| +
              |deriv f (σ t) * iteratedDeriv 2 σ t| := abs_add_le _ _
        _ = |iteratedDeriv 2 f (σ t)| * |deriv σ t| ^ 2 +
              |deriv f (σ t)| * |iteratedDeriv 2 σ t| := by
              rw [abs_mul, abs_mul, abs_pow]
        _ ≤ M2 * S1 ^ 2 + M1 * S2 := add_le_add hprod1 hprod2
        _ ≤ L2 := h2
    · -- Third derivative: `(f ∘ σ)''' = f''' (σ')³ + 3 f'' σ' σ'' + f' σ'''`.
      intro t ht
      have hft : ContDiffAt ℝ 3 f (σ t) :=
        hf.contDiffAt (isOpen_Ioo.mem_nhds (hσmaps ht))
      have hσt : ContDiffAt ℝ 3 σ t := hσ.contDiffAt (isOpen_Ioo.mem_nhds ht)
      have h3eq : iteratedDeriv 3 (fun t => f (σ t)) t =
          iteratedDeriv 3 f (σ t) * deriv σ t ^ 3 +
          3 * iteratedDeriv 2 f (σ t) * iteratedDeriv 2 σ t * deriv σ t +
          deriv f (σ t) * iteratedDeriv 3 σ t :=
        iteratedDeriv_comp_three (g := f) (f := σ) (x := t) hft hσt
      have hcube : |deriv σ t| ^ 3 ≤ S1 ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg (deriv σ t)) (hs1 t ht) 3
      have hT1 : |iteratedDeriv 3 f (σ t) * deriv σ t ^ 3| ≤ M3 * S1 ^ 3 := by
        rw [abs_mul, abs_pow]
        exact mul_le_mul (hf3 (σ t) (hσmaps ht)) hcube (pow_nonneg (abs_nonneg _) 3) hM3
      have hAB : |iteratedDeriv 2 f (σ t)| * |iteratedDeriv 2 σ t| ≤ M2 * S2 :=
        mul_le_mul (hf2 (σ t) (hσmaps ht)) (hs2 t ht) (abs_nonneg _) hM2
      have hABC : |iteratedDeriv 2 f (σ t)| * |iteratedDeriv 2 σ t| * |deriv σ t| ≤
          M2 * S2 * S1 :=
        mul_le_mul hAB (hs1 t ht) (abs_nonneg _) (mul_nonneg hM2 hS2)
      have hT2 : |3 * iteratedDeriv 2 f (σ t) * iteratedDeriv 2 σ t * deriv σ t| ≤
          3 * M2 * S1 * S2 := by
        have heq : |3 * iteratedDeriv 2 f (σ t) * iteratedDeriv 2 σ t * deriv σ t| =
            3 * (|iteratedDeriv 2 f (σ t)| * |iteratedDeriv 2 σ t| * |deriv σ t|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
          ring
        rw [heq]
        calc
          3 * (|iteratedDeriv 2 f (σ t)| * |iteratedDeriv 2 σ t| * |deriv σ t|)
              ≤ 3 * (M2 * S2 * S1) :=
                mul_le_mul_of_nonneg_left hABC (show (0 : ℝ) ≤ 3 by norm_num)
          _ = 3 * M2 * S1 * S2 := by ring
      have hT3 : |deriv f (σ t) * iteratedDeriv 3 σ t| ≤ M1 * S3 := by
        rw [abs_mul]
        exact mul_le_mul (hf1 (σ t) (hσmaps ht)) (hs3 t ht) (abs_nonneg _) hM1
      calc
        |iteratedDeriv 3 (fun t => f (σ t)) t|
            = |(iteratedDeriv 3 f (σ t) * deriv σ t ^ 3 +
                3 * iteratedDeriv 2 f (σ t) * iteratedDeriv 2 σ t * deriv σ t) +
                deriv f (σ t) * iteratedDeriv 3 σ t| := by rw [h3eq]
        _ ≤ |iteratedDeriv 3 f (σ t) * deriv σ t ^ 3 +
                3 * iteratedDeriv 2 f (σ t) * iteratedDeriv 2 σ t * deriv σ t| +
              |deriv f (σ t) * iteratedDeriv 3 σ t| := abs_add_le _ _
        _ ≤ |iteratedDeriv 3 f (σ t) * deriv σ t ^ 3| +
              |3 * iteratedDeriv 2 f (σ t) * iteratedDeriv 2 σ t * deriv σ t| +
              |deriv f (σ t) * iteratedDeriv 3 σ t| := by
              have := abs_add_le (iteratedDeriv 3 f (σ t) * deriv σ t ^ 3)
                (3 * iteratedDeriv 2 f (σ t) * iteratedDeriv 2 σ t * deriv σ t)
              linarith
        _ ≤ M3 * S1 ^ 3 + 3 * M2 * S1 * S2 + M1 * S3 := by
              linarith [hT1, hT2, hT3]
        _ ≤ L3 := h3
  · -- The interval is empty, so all three quantifiers are vacuous.
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨fun t ht => absurd ht (by simp [hne]),
      fun t ht => absurd ht (by simp [hne]),
      fun t ht => absurd ht (by simp [hne])⟩

/-- The `M = L` form of `comp_bounds`: with no slack constants, the composition's three
derivative bounds are exactly the three composite expressions. This is the `FeasibleOn`
shape of §4.4 without importing the planner layer; the third clause is pointwise, which
implies the a.e. clause `FeasibleOn` asks for. -/
theorem comp_bounds_on_feasible
    (f σ : ℝ → ℝ) {a b : ℝ}
    (M1 M2 M3 S1 S2 S3 : ℝ)
    (hf : ContDiffOn ℝ 3 f (Set.Ioo a b))
    (hσ : ContDiffOn ℝ 3 σ (Set.Ioo a b))
    (hσmaps : Set.MapsTo σ (Set.Ioo a b) (Set.Ioo a b))
    (hf1 : ∀ t ∈ Set.Ioo a b, |deriv f t| ≤ M1)
    (hf2 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 2 f t| ≤ M2)
    (hf3 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 3 f t| ≤ M3)
    (hs1 : ∀ t ∈ Set.Ioo a b, |deriv σ t| ≤ S1)
    (hs2 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 2 σ t| ≤ S2)
    (hs3 : ∀ t ∈ Set.Ioo a b, |iteratedDeriv 3 σ t| ≤ S3) :
    (∀ t ∈ Set.Ioo a b, |deriv (fun t => f (σ t)) t| ≤ M1 * S1) ∧
    (∀ t ∈ Set.Ioo a b,
      |iteratedDeriv 2 (fun t => f (σ t)) t| ≤ M2 * S1 ^ 2 + M1 * S2) ∧
    (∀ t ∈ Set.Ioo a b,
      |iteratedDeriv 3 (fun t => f (σ t)) t| ≤
        M3 * S1 ^ 3 + 3 * M2 * S1 * S2 + M1 * S3) :=
  comp_bounds f σ M1 M2 M3 S1 S2 S3
    (M1 * S1) (M2 * S1 ^ 2 + M1 * S2) (M3 * S1 ^ 3 + 3 * M2 * S1 * S2 + M1 * S3)
    hf hσ hσmaps hf1 hf2 hf3 hs1 hs2 hs3 le_rfl le_rfl le_rfl

end Motion
