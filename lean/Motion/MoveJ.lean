module

public import Motion.Basic
public import Motion.Plan.Conservative
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

noncomputable section

@[expose] public section

/-!
# MoveJ: the scalar joint-space mode

`docs/motion_control.md` §4.4, "Two MoveJ semantics": a single scalar profile `s`
moves the normalised path coordinate from `0` to `1`, and every joint follows the
joint-space straight line

```
q_i(t) = q0_i + (q1_i - q0_i) * s(t).
```

The scalar limits are the minimum over the moving joints (`q1 i - q0 i ≠ 0`) of each
joint limit divided by the joint's displacement magnitude:

```
Vs = min_i vmax_i / |Δ_i|,   As = min_i amax_i / |Δ_i|,   Js = min_i jmax_i / |Δ_i|.
```

Scaling the scalar velocity, acceleration and jerk by `|Δ_i|` therefore stays within
joint `i`'s own limits, which is `movejScalar_feasible`.

When every joint is stationary the moving-joint set is empty: the effective limits are
not computed and the profile is `planRestConservative 0 0 defaultLimits`, the empty
profile with total time `0`. The boundary and feasibility theorems are then trivial.
-/

namespace Motion

/-! ## The moving-joint set -/

/-- The set of moving joints. -/
def movingJoints {n : ℕ} (q0 q1 : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => q1 i - q0 i ≠ 0

@[simp] theorem mem_movingJoints {n : ℕ} {q0 q1 : Fin n → ℝ} {i : Fin n} :
    i ∈ movingJoints q0 q1 ↔ q1 i - q0 i ≠ 0 := by
  simp [movingJoints]

/-- A joint outside the moving set does not move. -/
theorem not_mem_movingJoints_iff {n : ℕ} {q0 q1 : Fin n → ℝ} {i : Fin n} :
    i ∉ movingJoints q0 q1 ↔ q1 i - q0 i = 0 := by
  simp only [movingJoints, Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_not

/-! ## Effective scalar limits -/

/-- The minimum of `f i / |q1 i - q0 i|` over the moving joints. -/
noncomputable def minRatio {n : ℕ} (q0 q1 : Fin n → ℝ) (f : Fin n → ℝ)
    (h : (movingJoints q0 q1).Nonempty) : ℝ :=
  ((movingJoints q0 q1).image fun i => f i / |q1 i - q0 i|).min'
    (h.image fun i => f i / |q1 i - q0 i|)

/-- The minimum over the moving joints is at most every member ratio. -/
theorem minRatio_le {n : ℕ} {q0 q1 : Fin n → ℝ} {f : Fin n → ℝ}
    {h : (movingJoints q0 q1).Nonempty} {i : Fin n} (hi : i ∈ movingJoints q0 q1) :
    minRatio q0 q1 f h ≤ f i / |q1 i - q0 i| := by
  unfold minRatio
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- The minimum over the moving joints is positive when every term of the image is. -/
theorem minRatio_pos {n : ℕ} {q0 q1 : Fin n → ℝ} {f : Fin n → ℝ}
    (h : (movingJoints q0 q1).Nonempty) (hf : ∀ i ∈ movingJoints q0 q1, 0 < f i) :
    0 < minRatio q0 q1 f h := by
  unfold minRatio
  have hmem := Finset.min'_mem
    ((movingJoints q0 q1).image fun i => f i / |q1 i - q0 i|)
    (h.image fun i => f i / |q1 i - q0 i|)
  obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hmem
  rw [← hfi]
  exact div_pos (hf i hi) (abs_pos.mpr (mem_movingJoints.mp hi))

/-- Fallback limits of the all-stationary branch. The profile it is used with has no
segments, so the values are arbitrary; all ones keep the proofs trivial. -/
def defaultLimits : Limits where
  vmax := 1
  amax := 1
  jmax := 1
  vmax_pos := one_pos
  amax_pos := one_pos
  jmax_pos := one_pos

/-- Effective scalar limits; only meaningful when the moving set is nonempty. Each field
is the minimum over the moving joints of the joint limit divided by `|Δ_i|`. -/
noncomputable def scalarLimits {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits)
    (h : (movingJoints q0 q1).Nonempty) : Limits where
  vmax := minRatio q0 q1 (fun i => (lim i).vmax) h
  amax := minRatio q0 q1 (fun i => (lim i).amax) h
  jmax := minRatio q0 q1 (fun i => (lim i).jmax) h
  vmax_pos := minRatio_pos h fun i _ => (lim i).vmax_pos
  amax_pos := minRatio_pos h fun i _ => (lim i).amax_pos
  jmax_pos := minRatio_pos h fun i _ => (lim i).jmax_pos

@[simp] theorem scalarLimits_vmax {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits)
    (h : (movingJoints q0 q1).Nonempty) :
    (scalarLimits q0 q1 lim h).vmax = minRatio q0 q1 (fun i => (lim i).vmax) h :=
  rfl

@[simp] theorem scalarLimits_amax {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits)
    (h : (movingJoints q0 q1).Nonempty) :
    (scalarLimits q0 q1 lim h).amax = minRatio q0 q1 (fun i => (lim i).amax) h :=
  rfl

@[simp] theorem scalarLimits_jmax {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits)
    (h : (movingJoints q0 q1).Nonempty) :
    (scalarLimits q0 q1 lim h).jmax = minRatio q0 q1 (fun i => (lim i).jmax) h :=
  rfl

theorem scalarVmax_le {n : ℕ} {q0 q1 : Fin n → ℝ} {lim : Fin n → Limits}
    {h : (movingJoints q0 q1).Nonempty} {i : Fin n} (hi : i ∈ movingJoints q0 q1) :
    (scalarLimits q0 q1 lim h).vmax ≤ (lim i).vmax / |q1 i - q0 i| := by
  rw [scalarLimits_vmax]
  exact minRatio_le hi

theorem scalarAmax_le {n : ℕ} {q0 q1 : Fin n → ℝ} {lim : Fin n → Limits}
    {h : (movingJoints q0 q1).Nonempty} {i : Fin n} (hi : i ∈ movingJoints q0 q1) :
    (scalarLimits q0 q1 lim h).amax ≤ (lim i).amax / |q1 i - q0 i| := by
  rw [scalarLimits_amax]
  exact minRatio_le hi

theorem scalarJmax_le {n : ℕ} {q0 q1 : Fin n → ℝ} {lim : Fin n → Limits}
    {h : (movingJoints q0 q1).Nonempty} {i : Fin n} (hi : i ∈ movingJoints q0 q1) :
    (scalarLimits q0 q1 lim h).jmax ≤ (lim i).jmax / |q1 i - q0 i| := by
  rw [scalarLimits_jmax]
  exact minRatio_le hi

/-! ## The scalar profile and the induced trajectory -/

/-- The scalar profile: `0 → 1` under the effective limits, or the empty profile when no
joint moves. -/
noncomputable def movejScalar {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits) : Profile :=
  if h : (movingJoints q0 q1).Nonempty then
    planRestConservative 0 1 (scalarLimits q0 q1 lim h)
  else
    planRestConservative 0 0 defaultLimits

/-- The induced joint position trajectory. -/
noncomputable def movejPos {n : ℕ} (q0 q1 : Fin n → ℝ) (s : Profile) (i : Fin n) (t : ℝ) : ℝ :=
  q0 i + (q1 i - q0 i) * s.q t

/-! ## Feasibility of the induced joint trajectories -/

/-- Every induced joint trajectory respects every joint's own velocity, acceleration and
jerk limits. -/
def MovejFeasible {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits) (s : Profile) : Prop :=
  (∀ i, ∀ t ∈ Set.Icc 0 s.totalTime, |(q1 i - q0 i) * s.v t| ≤ (lim i).vmax) ∧
  (∀ i, ∀ t ∈ Set.Icc 0 s.totalTime, |(q1 i - q0 i) * s.a t| ≤ (lim i).amax) ∧
  (∀ i, ∀ seg ∈ s.segments, seg.dur > 0 → |(q1 i - q0 i) * seg.jerk| ≤ (lim i).jmax)

/-- Scaling a bounded scalar quantity by a displacement: if the scalar bound `Vs` is at
most `L / |Δ|`, then `Δ` times the quantity is within `L`. -/
theorem abs_mul_le_of_le_div {Δ x Vs L : ℝ} (hΔ : 0 < |Δ|)
    (hx : |x| ≤ Vs) (hle : Vs ≤ L / |Δ|) : |Δ * x| ≤ L := by
  have hmul : Vs * |Δ| ≤ L := (le_div_iff₀ hΔ).mp hle
  rw [abs_mul]
  calc
    |Δ| * |x| ≤ |Δ| * Vs := mul_le_mul_of_nonneg_left hx hΔ.le
    _ = Vs * |Δ| := mul_comm _ _
    _ ≤ L := hmul

/-! ## The theorem ladder -/

/-- Boundary conditions: in the moving case the scalar profile runs from `0` to `1` at
rest; in the stationary case every joint is already at its target and the total time is
zero. -/
theorem movejScalar_boundary {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits) :
    let s := movejScalar q0 q1 lim
    s.q 0 = 0 ∧ s.q s.totalTime = 1 ∧ s.v 0 = 0 ∧ s.v s.totalTime = 0 ∧
      s.a 0 = 0 ∧ s.a s.totalTime = 0 ∨
    (∀ i, q1 i = q0 i) ∧ s.totalTime = 0 := by
  dsimp only
  by_cases h : (movingJoints q0 q1).Nonempty
  · have hs : movejScalar q0 q1 lim =
        planRestConservative 0 1 (scalarLimits q0 q1 lim h) := by
      unfold movejScalar
      exact dite_eq_left h
    rw [hs]
    exact Or.inl (planRestConservative_boundary 0 1 (scalarLimits q0 q1 lim h))
  · have hempty : movingJoints q0 q1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hstat : ∀ i : Fin n, q1 i = q0 i := by
      intro i
      have hi : i ∉ movingJoints q0 q1 := by simp [hempty]
      exact sub_eq_zero.mp (not_mem_movingJoints_iff.mp hi)
    have hs : movejScalar q0 q1 lim = planRestConservative 0 0 defaultLimits := by
      unfold movejScalar
      exact dite_eq_right h
    have hT : (planRestConservative 0 0 defaultLimits).totalTime = 0 := by
      have hsub : (0 : ℝ) - 0 = 0 := sub_self 0
      unfold planRestConservative
      rw [ite_eq_left hsub]
      simp [Profile.totalTime]
    rw [hs]
    exact Or.inr ⟨hstat, hT⟩

/-- In the moving case the scalar boundary conditions are unconditional: the profile runs
from `0` to `1`, at rest at both ends. -/
theorem movejScalar_boundary_of_moving {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits)
    (h : (movingJoints q0 q1).Nonempty) :
    (movejScalar q0 q1 lim).q 0 = 0 ∧ (movejScalar q0 q1 lim).q (movejScalar q0 q1 lim).totalTime = 1 ∧
      (movejScalar q0 q1 lim).v 0 = 0 ∧ (movejScalar q0 q1 lim).v (movejScalar q0 q1 lim).totalTime = 0 ∧
      (movejScalar q0 q1 lim).a 0 = 0 ∧ (movejScalar q0 q1 lim).a (movejScalar q0 q1 lim).totalTime = 0 := by
  have hs : movejScalar q0 q1 lim = planRestConservative 0 1 (scalarLimits q0 q1 lim h) := by
    unfold movejScalar
    exact dite_eq_left h
  rw [hs]
  exact planRestConservative_boundary 0 1 (scalarLimits q0 q1 lim h)

/-- The induced joint positions meet their targets in the moving case. -/
theorem movejScalar_joint_boundary_of_moving {n : ℕ} (q0 q1 : Fin n → ℝ)
    (lim : Fin n → Limits) (h : (movingJoints q0 q1).Nonempty) (i : Fin n) :
    movejPos q0 q1 (movejScalar q0 q1 lim) i 0 = q0 i ∧
      movejPos q0 q1 (movejScalar q0 q1 lim) i (movejScalar q0 q1 lim).totalTime = q1 i := by
  obtain ⟨h0, h1, -⟩ := movejScalar_boundary_of_moving q0 q1 lim h
  constructor
  · simp [movejPos, h0]
  · rw [movejPos, h1]
    ring

/-- When no joint moves, the scalar profile is the empty zero-motion profile. -/
theorem movejScalar_stationary {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits)
    (h : ∀ i, q1 i = q0 i) :
    movejScalar q0 q1 lim = planRestConservative 0 0 defaultLimits := by
  have hnot : ¬ (movingJoints q0 q1).Nonempty := by
    intro hne
    obtain ⟨i, hi⟩ := hne
    exact (mem_movingJoints.mp hi) (sub_eq_zero.mpr (h i))
  unfold movejScalar
  exact dite_eq_right hnot

/-- The induced joint trajectory is the joint-space straight line: definitionally
`q0_i + Δ_i s(t)`. -/
theorem movejScalar_path {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits) (i : Fin n) :
    ∀ t, movejPos q0 q1 (movejScalar q0 q1 lim) i t =
      q0 i + (q1 i - q0 i) * (movejScalar q0 q1 lim).q t := by
  intro t
  rfl

/-- Every induced joint trajectory respects every joint's limits. In the moving case the
scalar profile is feasible under the effective limits, and each effective limit is at
most the joint's own limit divided by `|Δ_i|`; multiplying through by `|Δ_i|` gives the
joint-space bounds. In the stationary case every displacement is zero. -/
theorem movejScalar_feasible {n : ℕ} (q0 q1 : Fin n → ℝ) (lim : Fin n → Limits) :
    MovejFeasible q0 q1 lim (movejScalar q0 q1 lim) := by
  by_cases h : (movingJoints q0 q1).Nonempty
  · have hs : movejScalar q0 q1 lim =
        planRestConservative 0 1 (scalarLimits q0 q1 lim h) := by
      unfold movejScalar
      exact dite_eq_left h
    have hfeas := planRestConservative_feasible 0 1 (scalarLimits q0 q1 lim h)
    rw [hs]
    refine ⟨?_, ?_, ?_⟩
    · intro i t ht
      by_cases hi : i ∈ movingJoints q0 q1
      · exact abs_mul_le_of_le_div (abs_pos.mpr (mem_movingJoints.mp hi))
          (hfeas.1 t ht) (scalarVmax_le hi)
      · have hz := not_mem_movingJoints_iff.mp hi
        rw [hz, zero_mul, abs_zero]
        exact (lim i).vmax_pos.le
    · intro i t ht
      by_cases hi : i ∈ movingJoints q0 q1
      · exact abs_mul_le_of_le_div (abs_pos.mpr (mem_movingJoints.mp hi))
          (hfeas.2.1 t ht) (scalarAmax_le hi)
      · have hz := not_mem_movingJoints_iff.mp hi
        rw [hz, zero_mul, abs_zero]
        exact (lim i).amax_pos.le
    · intro i seg hseg hdur
      by_cases hi : i ∈ movingJoints q0 q1
      · exact abs_mul_le_of_le_div (abs_pos.mpr (mem_movingJoints.mp hi))
          (hfeas.2.2 seg hseg hdur) (scalarJmax_le hi)
      · have hz := not_mem_movingJoints_iff.mp hi
        rw [hz, zero_mul, abs_zero]
        exact (lim i).jmax_pos.le
  · have hempty : movingJoints q0 q1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hstat : ∀ i : Fin n, q1 i = q0 i := by
      intro i
      have hi : i ∉ movingJoints q0 q1 := by simp [hempty]
      exact sub_eq_zero.mp (not_mem_movingJoints_iff.mp hi)
    have hs : movejScalar q0 q1 lim = planRestConservative 0 0 defaultLimits := by
      unfold movejScalar
      exact dite_eq_right h
    have hz : ∀ i : Fin n, q1 i - q0 i = 0 := fun i => sub_eq_zero.mpr (hstat i)
    rw [hs]
    refine ⟨?_, ?_, ?_⟩
    · intro i t ht
      rw [hz i, zero_mul, abs_zero]
      exact (lim i).vmax_pos.le
    · intro i t ht
      rw [hz i, zero_mul, abs_zero]
      exact (lim i).amax_pos.le
    · intro i seg hseg hdur
      rw [hz i, zero_mul, abs_zero]
      exact (lim i).jmax_pos.le

end Motion
