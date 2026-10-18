module
public import Motion.Basic
public import Motion.Glue
public import Motion.Smooth
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Order.Monotone.Union
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

noncomputable section
set_option maxHeartbeats 800000

@[expose] public section

/-!
# The conservative rational planner (M1-default)

`docs/motion_control.md` §3.8's guaranteed planner: a deliberately conservative
jerk-limited rest-to-rest S-curve with no radicals.

```
τ   = min 1 (min (A/J) (V/J))
Δmin = 2 J τ³
```

For a displacement `Δ = q1 - q0 ≠ 0` with `D = |Δ|` and `s = sign Δ`:

* if `D ≥ Δmin`, the jerk is `J` and the cruise duration is `τc = (D - Δmin)/(J τ²)`;
* otherwise the jerk is `j = D/(2τ³)` and there is no cruise.

Both branches emit the seven slots `(τ, 0, τ, τc, τ, 0, τ)` with jerks
`(s j, 0, -s j, 0, -s j, 0, s j)`. The peak velocity is `j τ² ≤ J τ² ≤ V`, the peak
acceleration is `j τ ≤ J τ ≤ A`, and the displacement is `2 j τ³ + j τ² τc = D`.

The file proves the M1-default theorem ladder: boundary conditions, feasibility,
smoothness, monotonicity, rest endpoints, the total-time sign, the seven-slot length
and the emitted shape.
-/

namespace Motion

/-! ## The template's parameters -/

/-- The template's ramp time `τ = min 1 (min (A/J) (V/J))`. -/
def conservativeTau (lim : Limits) : ℝ :=
  min 1 (min (lim.amax / lim.jmax) (lim.vmax / lim.jmax))

/-- The template's smallest reachable displacement `Δmin = 2 J τ³`. -/
def conservativeDmin (lim : Limits) : ℝ :=
  2 * lim.jmax * conservativeTau lim ^ 3

/-- The template's jerk magnitude: `J` above `Δmin`, `D/(2 τ³)` below. -/
def conservativeJ (D : ℝ) (lim : Limits) : ℝ :=
  if conservativeDmin lim ≤ D then lim.jmax else D / (2 * conservativeTau lim ^ 3)

/-- The template's cruise duration: `(D - Δmin)/(J τ²)` above `Δmin`, `0` below. -/
def conservativeTc (D : ℝ) (lim : Limits) : ℝ :=
  if conservativeDmin lim ≤ D then
    (D - conservativeDmin lim) / (lim.jmax * conservativeTau lim ^ 2)
  else 0

/-- The displacement sign: `+1` for nonnegative `Δ`, `-1` for negative `Δ`. -/
def conservativeSign (Δ : ℝ) : ℝ := if Δ < 0 then -1 else 1

/-! ## Elementary facts about the parameters -/

lemma conservativeTau_pos (lim : Limits) : 0 < conservativeTau lim := by
  unfold conservativeTau
  exact lt_min one_pos
    (lt_min (div_pos lim.amax_pos lim.jmax_pos) (div_pos lim.vmax_pos lim.jmax_pos))

lemma conservativeTau_nonneg (lim : Limits) : 0 ≤ conservativeTau lim :=
  le_of_lt (conservativeTau_pos lim)

lemma conservativeTau_ne_zero (lim : Limits) : conservativeTau lim ≠ 0 :=
  ne_of_gt (conservativeTau_pos lim)

lemma conservativeTau_le_one (lim : Limits) : conservativeTau lim ≤ 1 :=
  min_le_left _ _

lemma conservativeTau_le_amax_div (lim : Limits) :
    conservativeTau lim ≤ lim.amax / lim.jmax :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma conservativeTau_le_vmax_div (lim : Limits) :
    conservativeTau lim ≤ lim.vmax / lim.jmax :=
  (min_le_right _ _).trans (min_le_right _ _)

lemma conservativeTau_mul_jmax_le_amax (lim : Limits) :
    lim.jmax * conservativeTau lim ≤ lim.amax := by
  have h := mul_le_mul_of_nonneg_left (conservativeTau_le_amax_div lim)
    (le_of_lt lim.jmax_pos)
  have heq : lim.jmax * (lim.amax / lim.jmax) = lim.amax := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt lim.jmax_pos)]
  linarith

lemma conservativeTau_mul_jmax_le_vmax (lim : Limits) :
    lim.jmax * conservativeTau lim ≤ lim.vmax := by
  have h := mul_le_mul_of_nonneg_left (conservativeTau_le_vmax_div lim)
    (le_of_lt lim.jmax_pos)
  have heq : lim.jmax * (lim.vmax / lim.jmax) = lim.vmax := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt lim.jmax_pos)]
  linarith

lemma conservativeTau_sq_mul_jmax_le_vmax (lim : Limits) :
    lim.jmax * conservativeTau lim ^ 2 ≤ lim.vmax := by
  have hJV : lim.jmax * conservativeTau lim ≤ lim.vmax :=
    conservativeTau_mul_jmax_le_vmax lim
  have hτ0 := conservativeTau_nonneg lim
  have hτ1 := conservativeTau_le_one lim
  calc
    lim.jmax * conservativeTau lim ^ 2
        = (lim.jmax * conservativeTau lim) * conservativeTau lim := by ring
    _ ≤ lim.vmax * 1 := mul_le_mul hJV hτ1 hτ0 (le_of_lt lim.vmax_pos)
    _ = lim.vmax := by ring

lemma conservativeDmin_pos (lim : Limits) : 0 < conservativeDmin lim := by
  unfold conservativeDmin
  exact mul_pos (mul_pos two_pos lim.jmax_pos)
    (pow_pos (conservativeTau_pos lim) 3)

lemma conservativeDmin_nonneg (lim : Limits) : 0 ≤ conservativeDmin lim :=
  le_of_lt (conservativeDmin_pos lim)

lemma conservativeJ_nonneg (D : ℝ) (lim : Limits) (hD : 0 ≤ D) :
    0 ≤ conservativeJ D lim := by
  unfold conservativeJ
  split_ifs with h
  · exact le_of_lt lim.jmax_pos
  · exact div_nonneg hD
      (mul_nonneg (by norm_num) (pow_nonneg (conservativeTau_nonneg lim) 3))

lemma conservativeJ_pos (D : ℝ) (lim : Limits) (hD : 0 < D) :
    0 < conservativeJ D lim := by
  unfold conservativeJ
  split_ifs with h
  · exact lim.jmax_pos
  · exact div_pos hD (mul_pos two_pos (pow_pos (conservativeTau_pos lim) 3))

lemma conservativeJ_le_jmax (D : ℝ) (lim : Limits) :
    conservativeJ D lim ≤ lim.jmax := by
  unfold conservativeJ
  split_ifs with h
  · exact le_rfl
  · have hlt : D < conservativeDmin lim := lt_of_not_ge h
    unfold conservativeDmin at hlt
    have hden : 0 < 2 * conservativeTau lim ^ 3 :=
      mul_pos two_pos (pow_pos (conservativeTau_pos lim) 3)
    rw [div_le_iff₀ hden]
    nlinarith [hlt]

lemma conservativeJ_mul_tau_le_amax (D : ℝ) (lim : Limits) :
    conservativeJ D lim * conservativeTau lim ≤ lim.amax := by
  unfold conservativeJ
  split_ifs with h
  · exact conservativeTau_mul_jmax_le_amax lim
  · have hlt : D < conservativeDmin lim := lt_of_not_ge h
    unfold conservativeDmin at hlt
    have hτ := conservativeTau_pos lim
    have hτne : conservativeTau lim ≠ 0 := ne_of_gt hτ
    have hden : 0 < 2 * conservativeTau lim ^ 2 := mul_pos two_pos (pow_pos hτ 2)
    have hkey : D / (2 * conservativeTau lim ^ 3) * conservativeTau lim
        = D / (2 * conservativeTau lim ^ 2) := by
      field_simp [hτne]
    rw [hkey]
    have h1 : D / (2 * conservativeTau lim ^ 2) < lim.jmax * conservativeTau lim := by
      rw [div_lt_iff₀ hden]
      nlinarith [hlt]
    exact h1.le.trans (conservativeTau_mul_jmax_le_amax lim)

lemma conservativeJ_mul_tau_sq_le_vmax (D : ℝ) (lim : Limits) :
    conservativeJ D lim * conservativeTau lim ^ 2 ≤ lim.vmax := by
  unfold conservativeJ
  split_ifs with h
  · exact conservativeTau_sq_mul_jmax_le_vmax lim
  · have hlt : D < conservativeDmin lim := lt_of_not_ge h
    unfold conservativeDmin at hlt
    have hτ := conservativeTau_pos lim
    have hτne : conservativeTau lim ≠ 0 := ne_of_gt hτ
    have hden : 0 < 2 * conservativeTau lim := mul_pos two_pos hτ
    have hkey : D / (2 * conservativeTau lim ^ 3) * conservativeTau lim ^ 2
        = D / (2 * conservativeTau lim) := by
      field_simp [hτne]
    rw [hkey]
    have h1 : D / (2 * conservativeTau lim) < lim.jmax * conservativeTau lim ^ 2 := by
      rw [div_lt_iff₀ hden]
      nlinarith [hlt]
    exact h1.le.trans (conservativeTau_sq_mul_jmax_le_vmax lim)

lemma conservativeTc_nonneg (D : ℝ) (lim : Limits) : 0 ≤ conservativeTc D lim := by
  unfold conservativeTc
  split_ifs with h
  · exact div_nonneg (sub_nonneg.mpr h)
      (mul_pos lim.jmax_pos (pow_pos (conservativeTau_pos lim) 2)).le
  · exact le_rfl

lemma abs_conservativeSign (Δ : ℝ) : |conservativeSign Δ| = 1 := by
  unfold conservativeSign
  split_ifs with h
  · rw [abs_neg, abs_one]
  · exact abs_one

lemma conservativeSign_mul_abs (Δ : ℝ) : conservativeSign Δ * |Δ| = Δ := by
  unfold conservativeSign
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

lemma conservativeSign_eq_one_of_nonneg {Δ : ℝ} (h : 0 ≤ Δ) :
    conservativeSign Δ = 1 := by
  unfold conservativeSign
  rw [if_neg (not_lt.mpr h)]

lemma conservativeSign_eq_neg_one_of_neg {Δ : ℝ} (h : Δ < 0) :
    conservativeSign Δ = -1 := by
  unfold conservativeSign
  rw [if_pos h]

/-- The template's displacement identity: `2 j τ³ + j τ² τc = D`. -/
lemma conservative_disp_eq (Δ : ℝ) (lim : Limits) :
    2 * conservativeJ |Δ| lim * conservativeTau lim ^ 3 +
      conservativeJ |Δ| lim * conservativeTau lim ^ 2 * conservativeTc |Δ| lim
      = |Δ| := by
  by_cases h : conservativeDmin lim ≤ |Δ|
  · unfold conservativeJ conservativeTc
    rw [if_pos h, if_pos h]
    unfold conservativeDmin
    have hτne : conservativeTau lim ≠ 0 := conservativeTau_ne_zero lim
    have hJne : lim.jmax ≠ 0 := ne_of_gt lim.jmax_pos
    field_simp [hτne, hJne]
    ring
  · unfold conservativeJ conservativeTc
    rw [if_neg h, if_neg h]
    have hτne : conservativeTau lim ≠ 0 := conservativeTau_ne_zero lim
    field_simp [hτne]
    ring

/-! ## The seven slots -/

/-- The seven slots of the template with explicit jerk magnitude, ramp time and cruise
time. The two adjacent `-j` slots are kept separate so every slot has a single
acceleration sign, which is what `SegmentSafe` consumes. -/
def conservativeSegments (j τ τc s : ℝ) (hτ : 0 ≤ τ) (hτc : 0 ≤ τc) : List Segment :=
  [ { dur := τ, dur_nonneg := hτ, jerk := s * j },
    { dur := 0, dur_nonneg := le_rfl, jerk := 0 },
    { dur := τ, dur_nonneg := hτ, jerk := -(s * j) },
    { dur := τc, dur_nonneg := hτc, jerk := 0 },
    { dur := τ, dur_nonneg := hτ, jerk := -(s * j) },
    { dur := 0, dur_nonneg := le_rfl, jerk := 0 },
    { dur := τ, dur_nonneg := hτ, jerk := s * j } ]

@[simp] lemma conservativeSegments_dur (j τ τc s : ℝ) {hτ : 0 ≤ τ} {hτc : 0 ≤ τc} :
    (conservativeSegments j τ τc s hτ hτc).map Segment.dur =
      [τ, 0, τ, τc, τ, 0, τ] := by
  simp [conservativeSegments]

@[simp] lemma conservativeSegments_jerk (j τ τc s : ℝ) {hτ : 0 ≤ τ} {hτc : 0 ≤ τc} :
    (conservativeSegments j τ τc s hτ hτc).map Segment.jerk =
      [s * j, 0, -(s * j), 0, -(s * j), 0, s * j] := by
  simp [conservativeSegments]

@[simp] lemma conservativeSegments_length (j τ τc s : ℝ) {hτ : 0 ≤ τ} {hτc : 0 ≤ τc} :
    (conservativeSegments j τ τc s hτ hτc).length = 7 := by
  simp [conservativeSegments]

lemma conservativeSegments_totalTime (j τ τc s : ℝ) {hτ : 0 ≤ τ} {hτc : 0 ≤ τc} :
    ((conservativeSegments j τ τc s hτ hτc).map Segment.dur).sum = 4 * τ + τc := by
  simp [conservativeSegments]
  ring

/-- The fold through the seven slots ends at the displacement predicted by §3.8. -/
lemma conservativeSegments_fold (q0 j τ τc s : ℝ) {hτ : 0 ≤ τ} {hτc : 0 ≤ τc} :
    List.foldl Segment.exit { q := q0, v := 0, a := 0 }
        (conservativeSegments j τ τc s hτ hτc) =
      { q := q0 + s * (2 * j * τ ^ 3 + j * τ ^ 2 * τc), v := 0, a := 0 } := by
  apply State.ext
  · simp only [conservativeSegments, List.foldl_cons, List.foldl_nil, Segment.exit,
      Segment.stateAt]
    ring
  · simp only [conservativeSegments, List.foldl_cons, List.foldl_nil, Segment.exit,
      Segment.stateAt]
    ring
  · simp only [conservativeSegments, List.foldl_cons, List.foldl_nil, Segment.exit,
      Segment.stateAt]
    ring

/-- Every slot of the template is `SegmentSafe`, and so is the chain. The hypotheses are
the peak bounds `j τ ≤ A`, `j τ² ≤ V` and `j ≤ J`; §3.8's arithmetic establishes them in
both branches. -/
lemma conservativeSegments_safeFrom (lim : Limits) (q0 j τ τc s : ℝ)
    {hτ : 0 ≤ τ} {hτc : 0 ≤ τc}
    (hj0 : 0 ≤ j) (hjA : j * τ ≤ lim.amax) (hjV : j * τ ^ 2 ≤ lim.vmax)
    (hjJ : j ≤ lim.jmax) (hs : |s| = 1) :
    SafeFrom lim { q := q0, v := 0, a := 0 }
      (conservativeSegments j τ τc s hτ hτc) := by
  have habs_j : |s * j| = j := by
    rw [abs_mul, hs, one_mul, abs_of_nonneg hj0]
  have habs_jt : |s * j * τ| = j * τ := by
    rw [abs_mul, habs_j, abs_of_nonneg hτ]
  have habs_jt2 : |s * j * τ ^ 2| = j * τ ^ 2 := by
    rw [abs_mul, habs_j, abs_of_nonneg (pow_nonneg hτ 2)]
  have hjt20 : 0 ≤ j * τ ^ 2 := mul_nonneg hj0 (pow_nonneg hτ 2)
  have hV1 : |s * j * τ ^ 2 / 2| ≤ lim.vmax := by
    rw [abs_div, habs_jt2, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith
  have hA1 : |s * j * τ| ≤ lim.amax := by
    rw [habs_jt]; exact hjA
  have hV3 : |s * j * τ ^ 2| ≤ lim.vmax := by
    rw [habs_jt2]; exact hjV
  have hJ : |s * j| ≤ lim.jmax := by rw [habs_j]; exact hjJ
  let st1 : State := { q := q0 + s * j * τ ^ 3 / 6, v := s * j * τ ^ 2 / 2, a := s * j * τ }
  let st3 : State := { q := q0 + s * j * τ ^ 3, v := s * j * τ ^ 2, a := 0 }
  let st4 : State := { q := q0 + s * j * τ ^ 3 + s * j * τ ^ 2 * τc,
                        v := s * j * τ ^ 2, a := 0 }
  let st5 : State := { q := q0 + s * j * τ ^ 3 + s * j * τ ^ 2 * τc
                          + s * j * τ ^ 3 - s * j * τ ^ 3 / 6,
                        v := s * j * τ ^ 2 / 2, a := -(s * j * τ) }
  let st7 : State := { q := q0 + 2 * s * j * τ ^ 3 + s * j * τ ^ 2 * τc, v := 0, a := 0 }
  have e1 : Segment.exit { q := q0, v := 0, a := 0 } ⟨τ, hτ, s * j⟩ = st1 := by
    apply State.ext <;> simp [Segment.exit, Segment.stateAt, st1]
  have e2 : Segment.exit st1 ⟨0, le_rfl, 0⟩ = st1 := by
    apply State.ext <;> simp [Segment.exit, Segment.stateAt, st1]
  have e3 : Segment.exit st1 ⟨τ, hτ, -(s * j)⟩ = st3 := by
    apply State.ext <;> simp [Segment.exit, Segment.stateAt, st1, st3] <;> ring
  have e4 : Segment.exit st3 ⟨τc, hτc, 0⟩ = st4 := by
    apply State.ext <;> simp [Segment.exit, Segment.stateAt, st3, st4]
  have e5 : Segment.exit st4 ⟨τ, hτ, -(s * j)⟩ = st5 := by
    apply State.ext <;> simp [Segment.exit, Segment.stateAt, st4, st5] <;> ring
  have e6 : Segment.exit st5 ⟨0, le_rfl, 0⟩ = st5 := by
    apply State.ext <;> simp [Segment.exit, Segment.stateAt, st5]
  have e7 : Segment.exit st5 ⟨τ, hτ, s * j⟩ = st7 := by
    apply State.ext <;> simp [Segment.exit, Segment.stateAt, st5, st7] <;> ring
  unfold conservativeSegments SafeFrom
  repeat' apply And.intro
  all_goals try simp only [e1, e2, e3, e4, e5, e6, e7]
  all_goals try simp only [st1, st3, st4, st5, st7]
  all_goals
    first
    | exact hV1
    | exact hA1
    | exact hV3
    | exact hJ
    | (rw [abs_neg]; exact hJ)
    | (rw [abs_neg]; exact hA1)
    | (rw [abs_zero]; exact lim.jmax_pos.le)
    | (rw [abs_zero]; exact lim.vmax_pos.le)
    | (rw [abs_zero]; exact lim.amax_pos.le)
    | (rw [show s * j * τ * (s * j * τ) = (s * j * τ) ^ 2 by ring]; exact sq_nonneg _)
    | (rw [show -(s * j * τ) * -(s * j * τ) = (s * j * τ) ^ 2 by ring]; exact sq_nonneg _)
    | positivity
    | nlinarith [lim.vmax_pos, lim.amax_pos, lim.jmax_pos]

/-! ## The planner -/

/-- The conservative rational template of `docs/motion_control.md` §3.8 (M1-default).
Total in its arguments; `q0 = q1` is the empty profile. -/
def planRestConservative (q0 q1 : ℝ) (lim : Limits) : Profile :=
  let start : State := { q := q0, v := 0, a := 0 }
  if q1 - q0 = 0 then
    { start := start, segments := [] }
  else
    let D : ℝ := |q1 - q0|
    let τ : ℝ := conservativeTau lim
    let s : ℝ := conservativeSign (q1 - q0)
    if h : conservativeDmin lim ≤ D then
      let τc : ℝ := (D - conservativeDmin lim) / (lim.jmax * τ ^ 2)
      { start := start,
        segments := conservativeSegments lim.jmax τ τc s
          (le_of_lt (conservativeTau_pos lim))
          (div_nonneg (sub_nonneg.mpr h)
            (mul_pos lim.jmax_pos (pow_pos (conservativeTau_pos lim) 2)).le) }
    else
      let j : ℝ := D / (2 * τ ^ 3)
      { start := start,
        segments := conservativeSegments j τ 0 s
          (le_of_lt (conservativeTau_pos lim)) le_rfl }

@[simp] lemma planRestConservative_start (q0 q1 : ℝ) (lim : Limits) :
    (planRestConservative q0 q1 lim).start = { q := q0, v := 0, a := 0 } := by
  unfold planRestConservative
  dsimp only
  split_ifs <;> rfl

/-- The emitted segment list is the seven-slot template with the parameter choices of
§3.8. The proof arguments of `conservativeSegments` are propositionally irrelevant. -/
lemma planRestConservative_segments (q0 q1 : ℝ) (lim : Limits)
    (h : q1 - q0 ≠ 0) {hτ : 0 ≤ conservativeTau lim}
    {hτc : 0 ≤ conservativeTc |q1 - q0| lim} :
    (planRestConservative q0 q1 lim).segments =
      conservativeSegments (conservativeJ |q1 - q0| lim) (conservativeTau lim)
        (conservativeTc |q1 - q0| lim) (conservativeSign (q1 - q0)) hτ hτc := by
  unfold planRestConservative
  rw [if_neg h]
  dsimp only
  split_ifs with hb
  · simp only [conservativeJ, conservativeTc, if_pos hb]
  · simp only [conservativeJ, conservativeTc, if_neg hb]

lemma planRestConservative_totalTime (q0 q1 : ℝ) (lim : Limits) (h : q1 - q0 ≠ 0) :
    (planRestConservative q0 q1 lim).totalTime =
      4 * conservativeTau lim + conservativeTc |q1 - q0| lim := by
  rw [Profile.totalTime, planRestConservative_segments q0 q1 lim h
    (hτ := conservativeTau_nonneg lim)
    (hτc := conservativeTc_nonneg |q1 - q0| lim)]
  exact conservativeSegments_totalTime _ _ _ _

/-- The template's end state: at rest, displaced by `sign Δ · |Δ| = q1 - q0`. -/
lemma planRestConservative_endState (q0 q1 : ℝ) (lim : Limits) (h : q1 - q0 ≠ 0) :
    (planRestConservative q0 q1 lim).endState =
      { q := q0 + conservativeSign (q1 - q0) * |q1 - q0|, v := 0, a := 0 } := by
  have hdisp := conservative_disp_eq (q1 - q0) lim
  rw [Profile.endState, planRestConservative_segments q0 q1 lim h
    (hτ := conservativeTau_nonneg lim)
    (hτc := conservativeTc_nonneg |q1 - q0| lim)]
  rw [planRestConservative_start, conservativeSegments_fold]
  have hq : 2 * conservativeJ |q1 - q0| lim * conservativeTau lim ^ 3 +
      conservativeJ |q1 - q0| lim * conservativeTau lim ^ 2 *
        conservativeTc |q1 - q0| lim = |q1 - q0| := hdisp
  rw [hq]

/-! ## The M1-default theorem ladder -/

/-- The template meets the required boundary conditions. -/
theorem planRestConservative_boundary (q0 q1 : ℝ) (lim : Limits) :
    let p := planRestConservative q0 q1 lim
    p.q 0 = q0 ∧ p.q p.totalTime = q1 ∧
      p.v 0 = 0 ∧ p.v p.totalTime = 0 ∧
      p.a 0 = 0 ∧ p.a p.totalTime = 0 := by
  dsimp only
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    unfold planRestConservative
    rw [if_pos hsub]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Profile.q, Profile.v, Profile.a, Profile.stateAt, Profile.totalTime]
  · have hend := planRestConservative_endState q0 q1 lim hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Profile.q, Profile.stateAt_zero, planRestConservative_start]
    · rw [Profile.q, Profile.stateAt_totalTime, hend]
      have h := conservativeSign_mul_abs (q1 - q0)
      linarith
    · rw [Profile.v, Profile.stateAt_zero, planRestConservative_start]
    · rw [Profile.v, Profile.stateAt_totalTime, hend]
    · rw [Profile.a, Profile.stateAt_zero, planRestConservative_start]
    · rw [Profile.a, Profile.stateAt_totalTime, hend]

/-- The profile starts and ends at rest. -/
theorem planRestConservative_isRest (q0 q1 : ℝ) (lim : Limits) :
    let p := planRestConservative q0 q1 lim
    p.start.v = 0 ∧ p.start.a = 0 ∧ p.endState.v = 0 ∧ p.endState.a = 0 := by
  dsimp only
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    unfold planRestConservative
    rw [if_pos hsub]
    simp [Profile.endState]
  · rw [planRestConservative_endState q0 q1 lim hΔ, planRestConservative_start]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The template is feasible for every pair of positions. -/
theorem planRestConservative_feasible (q0 q1 : ℝ) (lim : Limits) :
    Feasible (planRestConservative q0 q1 lim) lim := by
  apply feasible_of_safeFrom
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    unfold planRestConservative
    rw [if_pos hsub]
    exact ⟨by simpa using lim.vmax_pos.le, by simpa using lim.amax_pos.le⟩
  · rw [planRestConservative_segments q0 q1 lim hΔ
      (hτ := conservativeTau_nonneg lim)
      (hτc := conservativeTc_nonneg |q1 - q0| lim)]
    rw [planRestConservative_start]
    exact conservativeSegments_safeFrom lim q0 _ _ _ _
      (conservativeJ_nonneg _ lim (abs_nonneg _))
      (conservativeJ_mul_tau_le_amax _ lim)
      (conservativeJ_mul_tau_sq_le_vmax _ lim)
      (conservativeJ_le_jmax _ lim)
      (abs_conservativeSign _)

/-- The template is twice continuously differentiable on its interval. -/
theorem planRestConservative_smooth (q0 q1 : ℝ) (lim : Limits) :
    ContDiffOn ℝ 2 (planRestConservative q0 q1 lim).q
      (Set.Icc 0 (planRestConservative q0 q1 lim).totalTime) := by
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    have hseg : (planRestConservative q0 q0 lim).segments = [] := by
      unfold planRestConservative
      rw [ite_eq_left hsub]
    have hqfun : (planRestConservative q0 q0 lim).q = fun _ => q0 := by
      funext t
      simp [Profile.q, Profile.stateAt, hseg, planRestConservative_start, evalFrom]
    rw [hqfun]
    exact contDiff_const.contDiffOn
  · have hseg' := planRestConservative_segments q0 q1 lim hΔ
      (hτ := conservativeTau_nonneg lim)
      (hτc := conservativeTc_nonneg |q1 - q0| lim)
    have hne : (planRestConservative q0 q1 lim).segments ≠ [] := by
      rw [hseg']
      simp [conservativeSegments]
    have hfun : (planRestConservative q0 q1 lim).q =
        fun t => (evalFrom (planRestConservative q0 q1 lim).start
          (planRestConservative q0 q1 lim).segments t).q := by
      funext t
      rw [Profile.q, Profile.stateAt]
    rw [hfun]
    exact (evalFrom_contDiff_q_of_ne _ _ hne).contDiffOn

/-- The template is nondecreasing for a nonnegative displacement. -/
theorem planRestConservative_monotone (q0 q1 : ℝ) (lim : Limits) (h : q0 ≤ q1) :
    MonotoneOn (planRestConservative q0 q1 lim).q
      (Set.Icc 0 (planRestConservative q0 q1 lim).totalTime) := by
  -- The emitted list, with the parameter choices of `planRestConservative`.
  have hseg (hΔ : q1 - q0 ≠ 0) := planRestConservative_segments q0 q1 lim hΔ
    (hτ := conservativeTau_nonneg lim)
    (hτc := conservativeTc_nonneg |q1 - q0| lim)
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    have hseg0 : (planRestConservative q0 q0 lim).segments = [] := by
      unfold planRestConservative
      rw [ite_eq_left hsub]
    have hqfun : (planRestConservative q0 q0 lim).q = fun _ => q0 := by
      funext t
      simp [Profile.q, Profile.stateAt, hseg0, planRestConservative_start, evalFrom]
    rw [hqfun]
    exact monotoneOn_const
  · have hsign : conservativeSign (q1 - q0) = 1 :=
      conservativeSign_eq_one_of_nonneg (sub_nonneg.mpr h)
    -- The profile's position and velocity as a `evalFrom` over the seven slots.
    have hqfun : (planRestConservative q0 q1 lim).q =
        fun t => (evalFrom { q := q0, v := 0, a := 0 }
          (conservativeSegments (conservativeJ |q1 - q0| lim) (conservativeTau lim)
            (conservativeTc |q1 - q0| lim) (conservativeSign (q1 - q0))
            (conservativeTau_nonneg lim) (conservativeTc_nonneg |q1 - q0| lim)) t).q := by
      funext t
      rw [Profile.q, Profile.stateAt, hseg hΔ, planRestConservative_start]
    have hvfun : (planRestConservative q0 q1 lim).v =
        fun t => (evalFrom { q := q0, v := 0, a := 0 }
          (conservativeSegments (conservativeJ |q1 - q0| lim) (conservativeTau lim)
            (conservativeTc |q1 - q0| lim) (conservativeSign (q1 - q0))
            (conservativeTau_nonneg lim) (conservativeTc_nonneg |q1 - q0| lim)) t).v := by
      funext t
      rw [Profile.v, Profile.stateAt, hseg hΔ, planRestConservative_start]
    have hne : (conservativeSegments (conservativeJ |q1 - q0| lim) (conservativeTau lim)
        (conservativeTc |q1 - q0| lim) (conservativeSign (q1 - q0))
        (conservativeTau_nonneg lim) (conservativeTc_nonneg |q1 - q0| lim)) ≠ [] := by
      simp [conservativeSegments]
    have hderiv : ∀ x, deriv (planRestConservative q0 q1 lim).q x =
        (planRestConservative q0 q1 lim).v x := by
      intro x
      rw [hqfun, hvfun]
      exact deriv_evalFrom_q _ _ x hne
    have hv_nonneg : ∀ x ∈ Set.Ioo 0 (planRestConservative q0 q1 lim).totalTime,
        0 ≤ (planRestConservative q0 q1 lim).v x := by
      intro x _
      rw [hvfun, hsign]
      unfold conservativeSegments
      refine evalFrom_template_v_nonneg q0 (1 * conservativeJ |q1 - q0| lim)
        (conservativeTau lim) (conservativeTc |q1 - q0| lim) ?_ x
      exact mul_nonneg zero_le_one (conservativeJ_nonneg _ lim (abs_nonneg _))
    refine monotoneOn_of_deriv_nonneg
      (convex_Icc (0 : ℝ) (planRestConservative q0 q1 lim).totalTime)
      (planRestConservative_smooth q0 q1 lim).continuousOn ?_ ?_
    · exact (planRestConservative_smooth q0 q1 lim).differentiableOn (by simp)
        |>.mono interior_subset
    · intro x hx
      rw [interior_Icc] at hx
      rw [hderiv x]
      exact hv_nonneg x hx

/-- The total time is nonnegative, and positive for a nonzero displacement. -/
theorem planRestConservative_totalTime_nonneg (q0 q1 : ℝ) (lim : Limits) :
    0 ≤ (planRestConservative q0 q1 lim).totalTime ∧
      (q0 ≠ q1 → 0 < (planRestConservative q0 q1 lim).totalTime) := by
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    have hT : (planRestConservative q0 q0 lim).totalTime = 0 := by
      unfold planRestConservative
      rw [if_pos hsub]
      simp [Profile.totalTime]
    refine ⟨by rw [hT], ?_⟩
    intro hne
    exact absurd rfl hne
  · have hT := planRestConservative_totalTime q0 q1 lim hΔ
    have hτ := conservativeTau_pos lim
    have hτc := conservativeTc_nonneg |q1 - q0| lim
    refine ⟨?_, ?_⟩
    · rw [hT]; linarith
    · intro hne
      rw [hT]; linarith

/-- The emitted list has at most the seven slots of §3.8. -/
theorem planRestConservative_length_le (q0 q1 : ℝ) (lim : Limits) :
    (planRestConservative q0 q1 lim).segments.length ≤ 7 := by
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    unfold planRestConservative
    rw [if_pos hsub]
    simp
  · rw [planRestConservative_segments q0 q1 lim hΔ
      (hτ := conservativeTau_nonneg lim)
      (hτc := conservativeTc_nonneg |q1 - q0| lim),
      conservativeSegments_length]

/-- The emitted list is exactly the seven-slot pattern of §3.8:
`(τ, 0, τ, τc, τ, 0, τ)` with jerks `(s j, 0, -s j, 0, -s j, 0, s j)`. -/
theorem planRestConservative_shape (q0 q1 : ℝ) (lim : Limits) (h : q0 ≠ q1) :
    (planRestConservative q0 q1 lim).segments.map Segment.dur =
        [conservativeTau lim, 0, conservativeTau lim,
          conservativeTc |q1 - q0| lim, conservativeTau lim, 0,
          conservativeTau lim] ∧
      (planRestConservative q0 q1 lim).segments.map Segment.jerk =
        [conservativeSign (q1 - q0) * conservativeJ |q1 - q0| lim, 0,
          -(conservativeSign (q1 - q0) * conservativeJ |q1 - q0| lim), 0,
          -(conservativeSign (q1 - q0) * conservativeJ |q1 - q0| lim), 0,
          conservativeSign (q1 - q0) * conservativeJ |q1 - q0| lim] := by
  have hΔ : q1 - q0 ≠ 0 := sub_ne_zero.mpr h.symm
  rw [planRestConservative_segments q0 q1 lim hΔ
    (hτ := conservativeTau_nonneg lim)
    (hτc := conservativeTc_nonneg |q1 - q0| lim)]
  exact ⟨conservativeSegments_dur _ _ _ _, conservativeSegments_jerk _ _ _ _⟩

end Motion
