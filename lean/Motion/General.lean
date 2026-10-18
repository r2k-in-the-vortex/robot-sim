module
public import Motion.Transforms
public import Motion.Plan.Conservative
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 800000

@[expose] public section

/-!
# General boundary conditions (M2)

The stop–move–start planner of `docs/motion_control.md` §3.5: a state can be driven to
rest precisely when its acceleration can be removed without the velocity leaving the
band (`stopFeasible`); between the two stop phases a feasible rest-to-rest profile is
supplied by `planRestConservative`. `Viable` is the exact acceptance predicate of this
decomposition, not a global infeasibility certificate.

The stop profile is the Rust `stop_profile` of `crates/robot-motion/src/general.rs`: one
acceleration-removal ramp (jerk of magnitude `J` against the sign of `a`) followed by a
brake from `v + a|a|/(2J)` to rest, either a `(−J, t_j), (0, t_a), (+J, t_j)` three-phase
brake or the symmetric `(−J, t_r), (+J, t_r)` two-phase brake, mirrored for negative
velocity. The start profile is its time reversal.
-/

namespace Motion

open Classical

/-! ## The viability predicate -/

/-- Reverse velocity, keep position and acceleration. -/
def rev (s : State) : State :=
  { q := s.q, v := -s.v, a := s.a }

@[simp] theorem rev_q (s : State) : (rev s).q = s.q := rfl

@[simp] theorem rev_v (s : State) : (rev s).v = -s.v := rfl

@[simp] theorem rev_a (s : State) : (rev s).a = s.a := rfl

/-- Reversal is an involution. -/
@[simp] theorem rev_rev (s : State) : rev (rev s) = s := by
  ext <;> simp [rev]

/-- The velocity after the fastest legal acceleration-removal ramp,
`v_s = v + a|a|/(2J)`. -/
def stopVelocity (s : State) (lim : Limits) : ℝ :=
  s.v + s.a * |s.a| / (2 * lim.jmax)

/-- The state can be brought to rest without leaving the velocity band. -/
def stopFeasible (s : State) (lim : Limits) : Prop :=
  |s.a| ≤ lim.amax ∧ |s.v| ≤ lim.vmax ∧
    |s.v + s.a * |s.a| / (2 * lim.jmax)| ≤ lim.vmax

/-- The exact viability predicate of the stop–move–start decomposition. -/
def viable (s0 s1 : State) (lim : Limits) : Prop :=
  stopFeasible s0 lim ∧ stopFeasible (rev s1) lim

theorem stopFeasible_iff_stopVelocity (s : State) (lim : Limits) :
    stopFeasible s lim ↔
      |s.a| ≤ lim.amax ∧ |s.v| ≤ lim.vmax ∧ |stopVelocity s lim| ≤ lim.vmax :=
  Iff.rfl

/-! ## Brake parameters -/

/-- The velocity threshold `v_A = A²/J`. -/
def brakeVA (lim : Limits) : ℝ := lim.amax ^ 2 / lim.jmax

/-- The ramp time `t_j = A/J`. -/
def brakeTJ (lim : Limits) : ℝ := lim.amax / lim.jmax

/-- The hold time `t_a = |v|/A - t_j` of the three-phase brake. -/
def brakeTA (v : ℝ) (lim : Limits) : ℝ := |v| / lim.amax - brakeTJ lim

/-- The ramp time `t_r = sqrt (|v|/J)` of the two-phase brake. -/
def brakeTR (v : ℝ) (lim : Limits) : ℝ := Real.sqrt (|v| / lim.jmax)

/-- The velocity sign of the brake: `-1` for negative velocity, `+1` otherwise. -/
def brakeSgn (v : ℝ) : ℝ := if v < 0 then -1 else 1

lemma brakeTJ_pos (lim : Limits) : 0 < brakeTJ lim :=
  div_pos lim.amax_pos lim.jmax_pos

lemma brakeTJ_nonneg (lim : Limits) : 0 ≤ brakeTJ lim :=
  le_of_lt (brakeTJ_pos lim)

lemma brakeVA_nonneg (lim : Limits) : 0 ≤ brakeVA lim :=
  div_nonneg (sq_nonneg _) (le_of_lt lim.jmax_pos)

/-- `v_A = A · t_j`. -/
lemma brakeVA_eq (lim : Limits) : brakeVA lim = lim.amax * brakeTJ lim := by
  unfold brakeVA brakeTJ
  field_simp

/-- `J · t_j² = v_A`. -/
lemma brakeVA_eq_jmax_mul_sq (lim : Limits) :
    lim.jmax * brakeTJ lim ^ 2 = brakeVA lim := by
  unfold brakeVA brakeTJ
  field_simp

/-- `J · t_j = A`. -/
lemma brakeTJ_mul_jmax (lim : Limits) : lim.jmax * brakeTJ lim = lim.amax := by
  unfold brakeTJ
  field_simp [ne_of_gt lim.jmax_pos]

lemma brakeTA_nonneg (v : ℝ) (lim : Limits) (h : brakeVA lim ≤ |v|) :
    0 ≤ brakeTA v lim := by
  have hA := le_of_lt lim.amax_pos
  have hJ := ne_of_gt lim.jmax_pos
  have hsplit : |v| / lim.amax - lim.amax / lim.jmax =
      (|v| - lim.amax * (lim.amax / lim.jmax)) / lim.amax := by
    field_simp
  rw [brakeTA, brakeTJ, hsplit]
  apply div_nonneg _ hA
  have hvA : brakeVA lim = lim.amax * (lim.amax / lim.jmax) := by
    unfold brakeVA
    field_simp
  linarith

lemma brakeTR_nonneg (v : ℝ) (lim : Limits) : 0 ≤ brakeTR v lim :=
  Real.sqrt_nonneg _

lemma brakeTR_pos {v : ℝ} (lim : Limits) (hv : v ≠ 0) : 0 < brakeTR v lim := by
  rw [brakeTR, Real.sqrt_pos]
  exact div_pos (abs_pos.mpr hv) lim.jmax_pos

lemma brakeTR_sq (v : ℝ) (lim : Limits) :
    brakeTR v lim ^ 2 = |v| / lim.jmax :=
  Real.sq_sqrt (div_nonneg (abs_nonneg v) (le_of_lt lim.jmax_pos))

@[simp] lemma brakeSgn_abs (v : ℝ) : |brakeSgn v| = 1 := by
  unfold brakeSgn
  split_ifs with h
  · rw [abs_neg, abs_one]
  · exact abs_one

/-- The signed velocity: `sign v · |v| = v`. -/
lemma brakeSgn_mul_abs (v : ℝ) : brakeSgn v * |v| = v := by
  unfold brakeSgn
  split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.mp h)]; ring

lemma brakeSgn_eq_neg_one {v : ℝ} (h : v < 0) : brakeSgn v = -1 := by
  unfold brakeSgn
  rw [ite_eq_left h]

lemma brakeSgn_eq_one {v : ℝ} (h : ¬ v < 0) : brakeSgn v = 1 := by
  unfold brakeSgn
  rw [ite_eq_right h]

/-! ## Segments -/

/-- The acceleration-removal jerk: `-J` for positive acceleration, `+J` otherwise. -/
def removalJerk (s : State) (lim : Limits) : ℝ :=
  if 0 < s.a then -lim.jmax else lim.jmax

/-- The acceleration-removal segment. Only used when `s.a ≠ 0`; its duration is then
positive. -/
def removalSegment (s : State) (lim : Limits) : Segment :=
  { dur := |s.a| / lim.jmax
    dur_nonneg := div_nonneg (abs_nonneg s.a) (le_of_lt lim.jmax_pos)
    jerk := removalJerk s lim }

lemma removalJerk_abs (s : State) (lim : Limits) : |removalJerk s lim| = lim.jmax := by
  unfold removalJerk
  split_ifs with h
  · rw [abs_neg, abs_of_pos lim.jmax_pos]
  · rw [abs_of_pos lim.jmax_pos]

/-- The brake from velocity `v` to rest; `v` is the velocity after acceleration removal.
This mirrors `brake` in `crates/robot-motion/src/general.rs`. -/
def brakeSegments (v : ℝ) (lim : Limits) : List Segment :=
  if v = 0 then
    []
  else if hvA : brakeVA lim ≤ |v| then
    [ { dur := brakeTJ lim
        dur_nonneg := brakeTJ_nonneg lim
        jerk := -brakeSgn v * lim.jmax },
      { dur := brakeTA v lim
        dur_nonneg := brakeTA_nonneg v lim hvA
        jerk := 0 },
      { dur := brakeTJ lim
        dur_nonneg := brakeTJ_nonneg lim
        jerk := brakeSgn v * lim.jmax } ]
  else
    [ { dur := brakeTR v lim
        dur_nonneg := brakeTR_nonneg v lim
        jerk := -brakeSgn v * lim.jmax },
      { dur := brakeTR v lim
        dur_nonneg := brakeTR_nonneg v lim
        jerk := brakeSgn v * lim.jmax } ]

/-- The three-phase brake (`|v| ≥ v_A`) is safe from the rest-free state `{q, v, 0}`:
the velocity decreases monotonically from `v` to `0`, the acceleration stays in
`[-A, A]`, and the two endpoint checks of `SegmentSafe` cover the interior. -/
lemma safeFrom_brake_three (v q : ℝ) (lim : Limits)
    (hv : |v| ≤ lim.vmax) (hvA : brakeVA lim ≤ |v|) :
    SafeFrom lim { q := q, v := v, a := 0 }
      [ { dur := brakeTJ lim, dur_nonneg := brakeTJ_nonneg lim,
          jerk := -brakeSgn v * lim.jmax },
        { dur := brakeTA v lim, dur_nonneg := brakeTA_nonneg v lim hvA, jerk := 0 },
        { dur := brakeTJ lim, dur_nonneg := brakeTJ_nonneg lim,
          jerk := brakeSgn v * lim.jmax } ] := by
  have hJ : 0 < lim.jmax := lim.jmax_pos
  have hA : 0 < lim.amax := lim.amax_pos
  have hA0 : 0 ≤ lim.amax := le_of_lt hA
  have hJtJ : lim.jmax * brakeTJ lim = lim.amax := brakeTJ_mul_jmax lim
  have hJtJ2 : lim.jmax * brakeTJ lim ^ 2 = brakeVA lim := brakeVA_eq_jmax_mul_sq lim
  have hAtJ : lim.amax * brakeTJ lim = brakeVA lim := (brakeVA_eq lim).symm
  have hsgn_abs : |brakeSgn v| = 1 := brakeSgn_abs v
  have hsgn_mul : brakeSgn v * |v| = v := brakeSgn_mul_abs v
  have hvA0 : 0 ≤ brakeVA lim := brakeVA_nonneg lim
  let st0 : State := { q := q, v := v, a := 0 }
  let st1 : State :=
    { q := q + v * brakeTJ lim + 0 * brakeTJ lim ^ 2 / 2
        + (-brakeSgn v * lim.jmax) * brakeTJ lim ^ 3 / 6
      v := v - brakeSgn v * brakeVA lim / 2
      a := -brakeSgn v * lim.amax }
  let st2 : State :=
    { q := st1.q + st1.v * brakeTA v lim + st1.a * brakeTA v lim ^ 2 / 2
        + 0 * brakeTA v lim ^ 3 / 6
      v := brakeSgn v * brakeVA lim / 2
      a := -brakeSgn v * lim.amax }
  let st3 : State :=
    { q := st2.q + st2.v * brakeTJ lim + st2.a * brakeTJ lim ^ 2 / 2
        + (brakeSgn v * lim.jmax) * brakeTJ lim ^ 3 / 6
      v := 0
      a := 0 }
  let seg1 : Segment := ⟨brakeTJ lim, brakeTJ_nonneg lim, -brakeSgn v * lim.jmax⟩
  let seg2 : Segment := ⟨brakeTA v lim, brakeTA_nonneg v lim hvA, 0⟩
  let seg3 : Segment := ⟨brakeTJ lim, brakeTJ_nonneg lim, brakeSgn v * lim.jmax⟩
  have e1 : Segment.exit st0 seg1 = st1 := by
    apply State.ext
    · simp only [st0, st1, seg1, Segment.exit_q]
    · simp only [st0, st1, seg1, Segment.exit_v]
      linear_combination (-(brakeSgn v) / 2) * hJtJ2
    · simp only [st0, st1, seg1, Segment.exit_a]
      linear_combination (-(brakeSgn v)) * hJtJ
  have e2 : Segment.exit st1 seg2 = st2 := by
    apply State.ext
    · simp only [st1, st2, seg2, Segment.exit_q]
    · simp only [st1, st2, seg2, Segment.exit_v, brakeTA]
      field_simp [ne_of_gt hA]
      linear_combination (-2 * lim.amax ^ 2) * hsgn_mul +
        (2 * brakeSgn v * lim.amax ^ 2) * hAtJ
    · simp only [st1, st2, seg2, Segment.exit_a]
      ring
  have e3 : Segment.exit st2 seg3 = st3 := by
    apply State.ext
    · simp only [st2, st3, seg3, Segment.exit_q]
    · simp only [st2, st3, seg3, Segment.exit_v]
      linear_combination (-(brakeSgn v)) * hAtJ + (brakeSgn v / 2) * hJtJ2
    · simp only [st2, st3, seg3, Segment.exit_a]
      linear_combination (brakeSgn v) * hJtJ
  have hsgn_j1 : |-brakeSgn v * lim.jmax| = lim.jmax := by
    rw [abs_mul, abs_neg, brakeSgn_abs, one_mul, abs_of_pos hJ]
  have hsgn_j3 : |brakeSgn v * lim.jmax| = lim.jmax := by
    rw [abs_mul, brakeSgn_abs, one_mul, abs_of_pos hJ]
  have hst1v : |v - brakeSgn v * brakeVA lim / 2| ≤ lim.vmax := by
    have heq : v - brakeSgn v * brakeVA lim / 2 =
        brakeSgn v * (|v| - brakeVA lim / 2) := by
      rw [mul_sub, hsgn_mul]
      ring
    rw [heq, abs_mul, brakeSgn_abs, one_mul]
    have h2 : 0 ≤ |v| - brakeVA lim / 2 := by linarith
    rw [abs_of_nonneg h2]
    linarith
  have hst2v : |brakeSgn v * brakeVA lim / 2| ≤ lim.vmax := by
    rw [abs_div, abs_mul, brakeSgn_abs, one_mul, abs_of_nonneg hvA0,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hst1a : |-brakeSgn v * lim.amax| ≤ lim.amax := by
    rw [abs_mul, abs_neg, brakeSgn_abs, one_mul, abs_of_pos hA]
  have hst2a : |-brakeSgn v * lim.amax| ≤ lim.amax := hst1a
  have s1safe : SegmentSafe st0 seg1 lim := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [st0] using hv
    · simpa [st0] using hA0
    · change |-brakeSgn v * lim.jmax| ≤ lim.jmax
      exact le_of_eq hsgn_j1
    · rw [e1]; simpa [st1] using hst1v
    · rw [e1]; simpa [st1] using hst1a
    · simp [st0]
  have s2safe : SegmentSafe st1 seg2 lim := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [st1] using hst1v
    · simpa [st1] using hst1a
    · change |(0 : ℝ)| ≤ lim.jmax
      simpa using le_of_lt hJ
    · rw [e2]; simpa [st2] using hst2v
    · rw [e2]; simpa [st2] using hst2a
    · rw [e2]
      simp only [st1, st2]
      ring_nf
      positivity
  have s3safe : SegmentSafe st2 seg3 lim := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [st2] using hst2v
    · simpa [st2] using hst2a
    · simp only [seg3]
      exact le_of_eq hsgn_j3
    · rw [e3]; simp [st3]
      exact le_of_lt lim.vmax_pos
    · rw [e3]; simp [st3]
      exact le_of_lt lim.amax_pos
    · rw [e3]; simp [st3]
  have s0safe : SafeFrom lim st3 [] := by
    simp [SafeFrom, st3, hA0, le_of_lt lim.vmax_pos]
  change SafeFrom lim st0 [seg1, seg2, seg3]
  unfold SafeFrom
  rw [e1]
  refine ⟨s1safe, ?_⟩
  unfold SafeFrom
  rw [e2]
  refine ⟨s2safe, ?_⟩
  unfold SafeFrom
  rw [e3]
  exact ⟨s3safe, s0safe⟩

/-- The two-phase brake (`|v| < v_A`) is safe from `{q, v, 0}`: the acceleration peak
`sqrt (|v| J)` is below `A`, and the velocity decreases from `v` to `0`. -/
lemma safeFrom_brake_two (v q : ℝ) (lim : Limits)
    (hv : |v| ≤ lim.vmax) (hvA : ¬ brakeVA lim ≤ |v|) :
    SafeFrom lim { q := q, v := v, a := 0 }
      [ { dur := brakeTR v lim, dur_nonneg := brakeTR_nonneg v lim,
          jerk := -brakeSgn v * lim.jmax },
        { dur := brakeTR v lim, dur_nonneg := brakeTR_nonneg v lim,
          jerk := brakeSgn v * lim.jmax } ] := by
  have hJ : 0 < lim.jmax := lim.jmax_pos
  have hA : 0 < lim.amax := lim.amax_pos
  have hA0 : 0 ≤ lim.amax := le_of_lt hA
  have hspeed_lt : |v| < lim.amax ^ 2 / lim.jmax := by
    simpa [brakeVA] using not_le.mp hvA
  have hsgn_abs : |brakeSgn v| = 1 := brakeSgn_abs v
  have hsgn_mul : brakeSgn v * |v| = v := brakeSgn_mul_abs v
  have hJtR2 : lim.jmax * brakeTR v lim ^ 2 = |v| := by
    rw [brakeTR_sq]
    field_simp [ne_of_gt hJ]
  have hJtR_nonneg : 0 ≤ lim.jmax * brakeTR v lim :=
    mul_nonneg (le_of_lt hJ) (brakeTR_nonneg v lim)
  have hJtR_sq : (lim.jmax * brakeTR v lim) ^ 2 = |v| * lim.jmax := by
    rw [mul_pow, brakeTR_sq]
    field_simp [ne_of_gt hJ]
  have hspeedJ : |v| * lim.jmax < lim.amax ^ 2 := by
    have h := (lt_div_iff₀ hJ).mp hspeed_lt
    simpa [mul_comm] using h
  have hJtR_lt : lim.jmax * brakeTR v lim < lim.amax := by
    have hsq : (lim.jmax * brakeTR v lim) ^ 2 < lim.amax ^ 2 := by
      rw [hJtR_sq]
      simpa [mul_comm] using hspeedJ
    have h := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg hJtR_nonneg, abs_of_pos hA] at h
  have hst1v : |brakeSgn v * |v| / 2| ≤ lim.vmax := by
    rw [abs_div, abs_mul, brakeSgn_abs, one_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (abs_nonneg v)]
    linarith [abs_nonneg v]
  have hst1a : |-brakeSgn v * lim.jmax * brakeTR v lim| ≤ lim.amax := by
    have heq : -brakeSgn v * lim.jmax * brakeTR v lim =
        -(brakeSgn v * (lim.jmax * brakeTR v lim)) := by ring
    rw [heq, abs_neg, abs_mul, hsgn_abs, one_mul, abs_of_nonneg hJtR_nonneg]
    exact le_of_lt hJtR_lt
  let st0 : State := { q := q, v := v, a := 0 }
  let st1 : State :=
    { q := q + v * brakeTR v lim + 0 * brakeTR v lim ^ 2 / 2
        + (-brakeSgn v * lim.jmax) * brakeTR v lim ^ 3 / 6
      v := brakeSgn v * |v| / 2
      a := -brakeSgn v * lim.jmax * brakeTR v lim }
  let st2 : State :=
    { q := st1.q + st1.v * brakeTR v lim + st1.a * brakeTR v lim ^ 2 / 2
        + (brakeSgn v * lim.jmax) * brakeTR v lim ^ 3 / 6
      v := 0
      a := 0 }
  let seg1 : Segment := ⟨brakeTR v lim, brakeTR_nonneg v lim, -brakeSgn v * lim.jmax⟩
  let seg2 : Segment := ⟨brakeTR v lim, brakeTR_nonneg v lim, brakeSgn v * lim.jmax⟩
  have e1 : Segment.exit st0 seg1 = st1 := by
    apply State.ext
    · simp only [st0, st1, seg1, Segment.exit_q]
    · simp only [st0, st1, seg1, Segment.exit_v]
      linear_combination (-(brakeSgn v) / 2) * hJtR2 - hsgn_mul
    · simp only [st0, st1, seg1, Segment.exit_a]
      ring
  have e2 : Segment.exit st1 seg2 = st2 := by
    apply State.ext
    · simp only [st1, st2, seg2, Segment.exit_q]
    · simp only [st1, st2, seg2, Segment.exit_v]
      linear_combination (-(brakeSgn v) / 2) * hJtR2
    · simp only [st1, st2, seg2, Segment.exit_a]
      ring
  have hsgn_j1 : |-brakeSgn v * lim.jmax| = lim.jmax := by
    rw [abs_mul, abs_neg, brakeSgn_abs, one_mul, abs_of_pos hJ]
  have hsgn_j2 : |brakeSgn v * lim.jmax| = lim.jmax := by
    rw [abs_mul, brakeSgn_abs, one_mul, abs_of_pos hJ]
  have s1safe : SegmentSafe st0 seg1 lim := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [st0] using hv
    · simpa [st0] using hA0
    · change |-brakeSgn v * lim.jmax| ≤ lim.jmax
      exact le_of_eq hsgn_j1
    · rw [e1]; simpa [st1] using hst1v
    · rw [e1]; simpa [st1] using hst1a
    · simp [st0]
  have s2safe : SegmentSafe st1 seg2 lim := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [st1] using hst1v
    · simpa [st1] using hst1a
    · change |brakeSgn v * lim.jmax| ≤ lim.jmax
      exact le_of_eq hsgn_j2
    · rw [e2]; simp [st2]
      exact le_of_lt lim.vmax_pos
    · rw [e2]; simp [st2]
      exact le_of_lt lim.amax_pos
    · rw [e2]; simp [st2]
  have s0safe : SafeFrom lim st2 [] := by
    simp [SafeFrom, st2, hA0, le_of_lt lim.vmax_pos]
  change SafeFrom lim st0 [seg1, seg2]
  unfold SafeFrom
  rw [e1]
  refine ⟨s1safe, ?_⟩
  unfold SafeFrom
  rw [e2]
  exact ⟨s2safe, s0safe⟩

/-- The brake phase of the stop profile is safe from any state at rest with bounded
velocity. -/
theorem brakeSegments_safeFrom (v q : ℝ) (lim : Limits) (hv : |v| ≤ lim.vmax) :
    SafeFrom lim { q := q, v := v, a := 0 } (brakeSegments v lim) := by
  by_cases h0 : v = 0
  · have h : |(0 : ℝ)| ≤ lim.vmax ∧ |(0 : ℝ)| ≤ lim.amax :=
      ⟨by simpa using le_of_lt lim.vmax_pos, by simpa using le_of_lt lim.amax_pos⟩
    simpa [brakeSegments, h0, SafeFrom] using h
  · by_cases hvA : brakeVA lim ≤ |v|
    · rw [brakeSegments, ite_eq_right h0, dite_eq_left hvA]
      exact safeFrom_brake_three v q lim hv hvA
    · rw [brakeSegments, ite_eq_right h0, dite_eq_right hvA]
      exact safeFrom_brake_two v q lim hv hvA

/-- The segment list of a stop profile: the optional acceleration-removal ramp followed
by the brake. -/
def stopSegments (s : State) (lim : Limits) : List Segment :=
  if s.a = 0 then
    brakeSegments s.v lim
  else
    removalSegment s lim :: brakeSegments (stopVelocity s lim) lim

/-- The stop profile: a feasible profile from `s` to rest. Total: outside
`stopFeasible` it falls back to the empty profile. -/
def stopProfile (s : State) (lim : Limits) : Profile :=
  if stopFeasible s lim then
    { start := s, segments := stopSegments s lim }
  else
    { start := s, segments := [] }

/-- A profile from rest to `target`, the time reversal of the stop profile. -/
def startProfile (s1 : State) (lim : Limits) : Profile :=
  (stopProfile (rev s1) lim).reverse

/-- General boundary-condition planner: stop, move, start. -/
def planGeneral (s0 s1 : State) (lim : Limits) : Option Profile :=
  if viable s0 s1 lim then
    let stop := stopProfile s0 lim
    let start := startProfile s1 lim
    let mid := planRestConservative stop.endState.q start.start.q lim
    some (stop.append (mid.append start))
  else
    none

@[simp] theorem stopProfile_start (s : State) (lim : Limits) :
    (stopProfile s lim).start = s := by
  unfold stopProfile
  split_ifs <;> rfl

@[simp] theorem startProfile_start (s1 : State) (lim : Limits) :
    (startProfile s1 lim).start = revState ((stopProfile (rev s1) lim).endState) := rfl

/-- Folding a reversed, jerk-negated chain from the reversed end state returns the
reversed start state. This is the endpoint form of `evalFrom_reverse`. -/
theorem foldl_reverse_revSeg (st : State) (ss : List Segment) :
    (ss.reverse.map revSeg).foldl Segment.exit (revState (ss.foldl Segment.exit st)) =
      revState st := by
  induction ss generalizing st with
  | nil => rfl
  | cons s ss ih =>
      rw [show (s :: ss).foldl Segment.exit st = ss.foldl Segment.exit (s.exit st) from rfl]
      rw [List.reverse_cons, List.map_append, List.map_singleton, List.foldl_append]
      rw [ih (s.exit st)]
      show (revSeg s).exit (revState (s.exit st)) = revState st
      have h := Segment.stateAt_rev st s 0
      simpa [Segment.exit] using h

namespace Profile

/-- Reversing a profile swaps its endpoint states. -/
theorem endState_reverse (p : Profile) : p.reverse.endState = revState p.start := by
  unfold Profile.reverse Profile.endState
  simpa [Profile.endState] using foldl_reverse_revSeg p.start p.segments

end Profile

theorem startProfile_endState (s1 : State) (lim : Limits) :
    (startProfile s1 lim).endState = s1 := by
  unfold startProfile
  rw [Profile.endState_reverse]
  ext <;> simp [rev, revState]

/-! ## The acceleration-removal segment -/

/-- The acceleration-removal ramp leaves velocity `v + a|a|/(2J)`. -/
lemma removalSegment_exit_v (s : State) (lim : Limits) :
    ((removalSegment s lim).exit s).v = stopVelocity s lim := by
  rw [Segment.exit_v]
  simp only [removalSegment, removalJerk, stopVelocity]
  split_ifs with h
  · rw [abs_of_pos h]
    field_simp [ne_of_gt lim.jmax_pos]
    ring
  · rw [abs_of_nonpos (not_lt.mp h)]
    field_simp [ne_of_gt lim.jmax_pos]
    ring

/-- The acceleration-removal ramp ends with zero acceleration. -/
lemma removalSegment_exit_a (s : State) (lim : Limits) :
    ((removalSegment s lim).exit s).a = 0 := by
  rw [Segment.exit_a]
  simp only [removalSegment, removalJerk]
  split_ifs with h
  · rw [abs_of_pos h]
    field_simp [ne_of_gt lim.jmax_pos]
    ring
  · rw [abs_of_nonpos (not_lt.mp h)]
    field_simp [ne_of_gt lim.jmax_pos]
    ring

/-- A feasible state's acceleration-removal ramp is a safe segment. -/
lemma removalSegment_safe (s : State) (lim : Limits) (h : stopFeasible s lim) :
    SegmentSafe s (removalSegment s lim) lim := by
  obtain ⟨hA, hV, hVs⟩ := h
  refine ⟨hV, hA, ?_, ?_, ?_, ?_⟩
  · simp only [removalSegment]
    rw [removalJerk_abs]
  · rw [removalSegment_exit_v]
    exact hVs
  · rw [removalSegment_exit_a]
    simpa using le_of_lt lim.amax_pos
  · rw [removalSegment_exit_a]
    simp

/-- The stop segment chain is safe from every feasible state. -/
lemma stopSegments_safeFrom (s : State) (lim : Limits) (h : stopFeasible s lim) :
    SafeFrom lim s (stopSegments s lim) := by
  obtain ⟨hA, hV, hVs⟩ := h
  by_cases ha : s.a = 0
  · have hsv : |s.v| ≤ lim.vmax := by
      simpa [stopVelocity, ha] using hVs
    have hsegs : stopSegments s lim = brakeSegments s.v lim := by
      simp [stopSegments, ha]
    have hstate : s = { q := s.q, v := s.v, a := 0 } := by
      ext <;> simp [ha]
    rw [hsegs, hstate]
    exact brakeSegments_safeFrom s.v s.q lim hsv
  · have hsegs : stopSegments s lim =
        removalSegment s lim :: brakeSegments (stopVelocity s lim) lim := by
      simp [stopSegments, ha]
    rw [hsegs]
    refine ⟨removalSegment_safe s lim ⟨hA, hV, hVs⟩, ?_⟩
    have hexit : (removalSegment s lim).exit s =
        { q := ((removalSegment s lim).exit s).q, v := stopVelocity s lim, a := 0 } := by
      ext
      · rfl
      · exact removalSegment_exit_v s lim
      · exact removalSegment_exit_a s lim
    rw [hexit]
    exact brakeSegments_safeFrom (stopVelocity s lim) _ lim hVs

/-! ## The stop profile reaches rest -/

/-- The three-phase brake ends at rest, whatever its start position. -/
lemma brakeSegments_end_three (v q : ℝ) (lim : Limits) (h0 : v ≠ 0)
    (hvA : brakeVA lim ≤ |v|) :
    ((brakeSegments v lim).foldl Segment.exit { q := q, v := v, a := 0 }).v = 0 ∧
    ((brakeSegments v lim).foldl Segment.exit { q := q, v := v, a := 0 }).a = 0 := by
  rw [brakeSegments, ite_eq_right h0, dite_eq_left hvA]
  have hJ : 0 < lim.jmax := lim.jmax_pos
  have hA : 0 < lim.amax := lim.amax_pos
  have hJtJ : lim.jmax * brakeTJ lim = lim.amax := brakeTJ_mul_jmax lim
  have hJtJ2 : lim.jmax * brakeTJ lim ^ 2 = brakeVA lim := brakeVA_eq_jmax_mul_sq lim
  have hAtJ : lim.amax * brakeTJ lim = brakeVA lim := (brakeVA_eq lim).symm
  have hsgn_abs : |brakeSgn v| = 1 := brakeSgn_abs v
  have hsgn_mul : brakeSgn v * |v| = v := brakeSgn_mul_abs v
  let st0 : State := { q := q, v := v, a := 0 }
  let st1 : State :=
    { q := q + v * brakeTJ lim + 0 * brakeTJ lim ^ 2 / 2
        + (-brakeSgn v * lim.jmax) * brakeTJ lim ^ 3 / 6
      v := v - brakeSgn v * brakeVA lim / 2
      a := -brakeSgn v * lim.amax }
  let st2 : State :=
    { q := st1.q + st1.v * brakeTA v lim + st1.a * brakeTA v lim ^ 2 / 2
        + 0 * brakeTA v lim ^ 3 / 6
      v := brakeSgn v * brakeVA lim / 2
      a := -brakeSgn v * lim.amax }
  let st3 : State :=
    { q := st2.q + st2.v * brakeTJ lim + st2.a * brakeTJ lim ^ 2 / 2
        + (brakeSgn v * lim.jmax) * brakeTJ lim ^ 3 / 6
      v := 0
      a := 0 }
  let seg1 : Segment := ⟨brakeTJ lim, brakeTJ_nonneg lim, -brakeSgn v * lim.jmax⟩
  let seg2 : Segment := ⟨brakeTA v lim, brakeTA_nonneg v lim hvA, 0⟩
  let seg3 : Segment := ⟨brakeTJ lim, brakeTJ_nonneg lim, brakeSgn v * lim.jmax⟩
  have e1 : Segment.exit st0 seg1 = st1 := by
    apply State.ext
    · simp only [st0, st1, seg1, Segment.exit_q]
    · simp only [st0, st1, seg1, Segment.exit_v]
      linear_combination (-(brakeSgn v) / 2) * hJtJ2
    · simp only [st0, st1, seg1, Segment.exit_a]
      linear_combination (-(brakeSgn v)) * hJtJ
  have e2 : Segment.exit st1 seg2 = st2 := by
    apply State.ext
    · simp only [st1, st2, seg2, Segment.exit_q]
    · simp only [st1, st2, seg2, Segment.exit_v, brakeTA]
      field_simp [ne_of_gt hA]
      linear_combination (-2 * lim.amax ^ 2) * hsgn_mul +
        (2 * brakeSgn v * lim.amax ^ 2) * hAtJ
    · simp only [st1, st2, seg2, Segment.exit_a]
      ring
  have e3 : Segment.exit st2 seg3 = st3 := by
    apply State.ext
    · simp only [st2, st3, seg3, Segment.exit_q]
    · simp only [st2, st3, seg3, Segment.exit_v]
      linear_combination (-(brakeSgn v)) * hAtJ + (brakeSgn v / 2) * hJtJ2
    · simp only [st2, st3, seg3, Segment.exit_a]
      linear_combination (brakeSgn v) * hJtJ
  show ([seg1, seg2, seg3].foldl Segment.exit st0).v = 0 ∧
    ([seg1, seg2, seg3].foldl Segment.exit st0).a = 0
  simp only [List.foldl_cons, List.foldl_nil]
  rw [e1, e2, e3]
  simp [st3]

/-- The symmetric two-phase brake ends at rest, whatever its start position. -/
lemma brakeSegments_end_two (v q : ℝ) (lim : Limits) (h0 : v ≠ 0)
    (hvA : ¬ brakeVA lim ≤ |v|) :
    ((brakeSegments v lim).foldl Segment.exit { q := q, v := v, a := 0 }).v = 0 ∧
    ((brakeSegments v lim).foldl Segment.exit { q := q, v := v, a := 0 }).a = 0 := by
  rw [brakeSegments, ite_eq_right h0, dite_eq_right hvA]
  have hJ : 0 < lim.jmax := lim.jmax_pos
  have hsgn_abs : |brakeSgn v| = 1 := brakeSgn_abs v
  have hsgn_mul : brakeSgn v * |v| = v := brakeSgn_mul_abs v
  have hJtR2 : lim.jmax * brakeTR v lim ^ 2 = |v| := by
    rw [brakeTR_sq]
    field_simp [ne_of_gt hJ]
  let st0 : State := { q := q, v := v, a := 0 }
  let st1 : State :=
    { q := q + v * brakeTR v lim + 0 * brakeTR v lim ^ 2 / 2
        + (-brakeSgn v * lim.jmax) * brakeTR v lim ^ 3 / 6
      v := brakeSgn v * |v| / 2
      a := -brakeSgn v * lim.jmax * brakeTR v lim }
  let st2 : State :=
    { q := st1.q + st1.v * brakeTR v lim + st1.a * brakeTR v lim ^ 2 / 2
        + (brakeSgn v * lim.jmax) * brakeTR v lim ^ 3 / 6
      v := 0
      a := 0 }
  let seg1 : Segment := ⟨brakeTR v lim, brakeTR_nonneg v lim, -brakeSgn v * lim.jmax⟩
  let seg2 : Segment := ⟨brakeTR v lim, brakeTR_nonneg v lim, brakeSgn v * lim.jmax⟩
  have e1 : Segment.exit st0 seg1 = st1 := by
    apply State.ext
    · simp only [st0, st1, seg1, Segment.exit_q]
    · simp only [st0, st1, seg1, Segment.exit_v]
      linear_combination (-(brakeSgn v) / 2) * hJtR2 - hsgn_mul
    · simp only [st0, st1, seg1, Segment.exit_a]
      ring
  have e2 : Segment.exit st1 seg2 = st2 := by
    apply State.ext
    · simp only [st1, st2, seg2, Segment.exit_q]
    · simp only [st1, st2, seg2, Segment.exit_v]
      linear_combination (-(brakeSgn v) / 2) * hJtR2
    · simp only [st1, st2, seg2, Segment.exit_a]
      ring
  show ([seg1, seg2].foldl Segment.exit st0).v = 0 ∧
    ([seg1, seg2].foldl Segment.exit st0).a = 0
  simp only [List.foldl_cons, List.foldl_nil]
  rw [e1, e2]
  simp [st2]

/-- Every brake ends at rest. -/
lemma brakeSegments_end_rest (v q : ℝ) (lim : Limits) :
    ((brakeSegments v lim).foldl Segment.exit { q := q, v := v, a := 0 }).v = 0 ∧
    ((brakeSegments v lim).foldl Segment.exit { q := q, v := v, a := 0 }).a = 0 := by
  by_cases h0 : v = 0
  · rw [h0]
    simp [brakeSegments]
  · by_cases hvA : brakeVA lim ≤ |v|
    · exact brakeSegments_end_three v q lim h0 hvA
    · exact brakeSegments_end_two v q lim h0 hvA

/-- The stop chain ends at rest. -/
lemma stopSegments_end_rest (s : State) (lim : Limits) :
    ((stopSegments s lim).foldl Segment.exit s).v = 0 ∧
    ((stopSegments s lim).foldl Segment.exit s).a = 0 := by
  by_cases ha : s.a = 0
  · have hsegs : stopSegments s lim = brakeSegments s.v lim := by
      simp [stopSegments, ha]
    have hstate : s = { q := s.q, v := s.v, a := 0 } := by
      ext <;> simp [ha]
    rw [hsegs, hstate]
    exact brakeSegments_end_rest s.v s.q lim
  · have hsegs : stopSegments s lim =
        removalSegment s lim :: brakeSegments (stopVelocity s lim) lim := by
      simp [stopSegments, ha]
    have hfold : (removalSegment s lim :: brakeSegments (stopVelocity s lim) lim).foldl
          Segment.exit s =
        (brakeSegments (stopVelocity s lim) lim).foldl Segment.exit
          ((removalSegment s lim).exit s) := rfl
    have hexit : (removalSegment s lim).exit s =
        { q := ((removalSegment s lim).exit s).q, v := stopVelocity s lim, a := 0 } := by
      ext
      · rfl
      · exact removalSegment_exit_v s lim
      · exact removalSegment_exit_a s lim
    rw [hsegs, hfold, hexit]
    exact brakeSegments_end_rest (stopVelocity s lim) _ lim

/-- The stop profile is feasible whenever its start state is. -/
theorem stopProfile_feasible (s : State) (lim : Limits) (h : stopFeasible s lim) :
    Feasible (stopProfile s lim) lim := by
  unfold stopProfile
  rw [ite_eq_left h]
  exact feasible_of_safeFrom (stopSegments_safeFrom s lim h)

/-- The stop profile ends at rest whenever its start state is feasible. -/
theorem stopProfile_ends_at_rest (s : State) (lim : Limits) (h : stopFeasible s lim) :
    (stopProfile s lim).endState.v = 0 ∧ (stopProfile s lim).endState.a = 0 := by
  have hsegs := stopSegments_end_rest s lim
  unfold stopProfile
  rw [ite_eq_left h]
  simpa [Profile.endState] using hsegs

/-- The stop segment list has at most four slots (removal ramp plus brake). -/
lemma brakeSegments_length_le (v : ℝ) (lim : Limits) :
    (brakeSegments v lim).length ≤ 3 := by
  by_cases h0 : v = 0
  · rw [brakeSegments, ite_eq_left h0]
    simp
  · by_cases hvA : brakeVA lim ≤ |v|
    · rw [brakeSegments, ite_eq_right h0, dite_eq_left hvA]
      simp
    · rw [brakeSegments, ite_eq_right h0, dite_eq_right hvA]
      simp

lemma stopSegments_length_le (s : State) (lim : Limits) :
    (stopSegments s lim).length ≤ 4 := by
  by_cases ha : s.a = 0
  · rw [stopSegments, ite_eq_left ha]
    exact le_trans (brakeSegments_length_le s.v lim) (by norm_num)
  · rw [stopSegments, ite_eq_right ha]
    simp only [List.length_cons]
    exact Nat.succ_le_succ (brakeSegments_length_le (stopVelocity s lim) lim)

lemma stopProfile_length_le (s : State) (lim : Limits) (h : stopFeasible s lim) :
    (stopProfile s lim).segments.length ≤ 4 := by
  unfold stopProfile
  rw [ite_eq_left h]
  exact stopSegments_length_le s lim

/-! ## The start profile -/

/-- The start profile is feasible whenever the reversed target is. -/
theorem startProfile_feasible (s1 : State) (lim : Limits)
    (h : stopFeasible (rev s1) lim) : Feasible (startProfile s1 lim) lim := by
  unfold startProfile
  exact Profile.feasible_reverse (stopProfile_feasible (rev s1) lim h)

/-- The start profile starts at rest. -/
theorem startProfile_starts_at_rest (s1 : State) (lim : Limits)
    (h : stopFeasible (rev s1) lim) :
    (startProfile s1 lim).start.v = 0 ∧ (startProfile s1 lim).start.a = 0 := by
  rw [startProfile_start]
  obtain ⟨hv, ha⟩ := stopProfile_ends_at_rest (rev s1) lim h
  constructor <;> simp [revState, hv, ha]

lemma startProfile_length_le (s1 : State) (lim : Limits)
    (h : stopFeasible (rev s1) lim) :
    (startProfile s1 lim).segments.length ≤ 4 := by
  unfold startProfile
  simp only [Profile.reverse, List.length_map, List.length_reverse]
  exact stopProfile_length_le (rev s1) lim h

/-! ## Concatenation -/

/-- Concatenation preserves the end state when the junction states agree. -/
theorem endState_append_eq {p q : Profile} (h : p.endState = q.start) :
    (p.append q).endState = q.endState := by
  unfold Profile.append Profile.endState at *
  rw [List.foldl_append, h]

/-- The rest-to-rest template ends exactly at `q1`, at rest. -/
lemma planRestConservative_endState_eq {q0 q1 : ℝ} (lim : Limits) :
    (planRestConservative q0 q1 lim).endState = { q := q1, v := 0, a := 0 } := by
  by_cases hΔ : q1 - q0 = 0
  · have hq : q1 = q0 := sub_eq_zero.mp hΔ
    rw [hq]
    have hsub : q0 - q0 = 0 := sub_self q0
    unfold planRestConservative
    rw [ite_eq_left hsub]
    simp [Profile.endState]
  · rw [planRestConservative_endState q0 q1 lim hΔ]
    have h := conservativeSign_mul_abs (q1 - q0)
    ext
    · simp
      linarith
    · rfl
    · rfl

/-! ## The general planner -/

/-- The composed stop–move–start profile starts at `s0` and ends at `s1`. -/
theorem boundary_stopMoveStart (s0 s1 : State) (lim : Limits)
    (h0 : stopFeasible s0 lim) (h1 : stopFeasible (rev s1) lim) :
    ((stopProfile s0 lim).append
      ((planRestConservative (stopProfile s0 lim).endState.q
        (startProfile s1 lim).start.q lim).append (startProfile s1 lim))).start = s0 ∧
    ((stopProfile s0 lim).append
      ((planRestConservative (stopProfile s0 lim).endState.q
        (startProfile s1 lim).start.q lim).append (startProfile s1 lim))).endState = s1 := by
  set start := startProfile s1 lim with hstartdef
  set stop := stopProfile s0 lim with hstopdef
  set mid := planRestConservative stop.endState.q start.start.q lim with hmiddef
  constructor
  · show stop.start = s0
    rw [hstopdef]
    exact stopProfile_start s0 lim
  · have hjunction : (mid.append start).start = stop.endState := by
      show mid.start = stop.endState
      rw [hmiddef, planRestConservative_start, hstopdef]
      obtain ⟨hv, ha⟩ := stopProfile_ends_at_rest s0 lim h0
      ext <;> simp [hv, ha]
    have hjunction2 : start.start = mid.endState := by
      rw [hmiddef, planRestConservative_endState_eq, hstartdef]
      obtain ⟨hv, ha⟩ := stopProfile_ends_at_rest (rev s1) lim h1
      ext <;> simp [revState, hv, ha]
    rw [endState_append_eq hjunction.symm, endState_append_eq hjunction2.symm, hstartdef]
    exact startProfile_endState s1 lim

/-- The composed stop–move–start profile is feasible. -/
theorem feasible_stopMoveStart (s0 s1 : State) (lim : Limits)
    (h0 : stopFeasible s0 lim) (h1 : stopFeasible (rev s1) lim) :
    Feasible ((stopProfile s0 lim).append
      ((planRestConservative (stopProfile s0 lim).endState.q
        (startProfile s1 lim).start.q lim).append (startProfile s1 lim))) lim := by
  set start := startProfile s1 lim with hstartdef
  set stop := stopProfile s0 lim with hstopdef
  set mid := planRestConservative stop.endState.q start.start.q lim with hmiddef
  have hstopf : Feasible stop lim := by
    rw [hstopdef]
    exact stopProfile_feasible s0 lim h0
  have hstartf : Feasible start lim := by
    rw [hstartdef]
    exact startProfile_feasible s1 lim h1
  have hmidf : Feasible mid lim := by
    rw [hmiddef]
    exact planRestConservative_feasible _ _ lim
  have hjunction : (mid.append start).start = stop.endState := by
    show mid.start = stop.endState
    rw [hmiddef, planRestConservative_start, hstopdef]
    obtain ⟨hv, ha⟩ := stopProfile_ends_at_rest s0 lim h0
    ext <;> simp [hv, ha]
  have hjunction2 : start.start = mid.endState := by
    rw [hmiddef, planRestConservative_endState_eq, hstartdef]
    obtain ⟨hv, ha⟩ := stopProfile_ends_at_rest (rev s1) lim h1
    ext <;> simp [revState, hv, ha]
  exact Profile.feasible_append hjunction hstopf
    (Profile.feasible_append hjunction2 hmidf hstartf)

/-- The planner only returns viable plans: `some` exactly when viable. -/
theorem planGeneral_isSome_iff (s0 s1 : State) (lim : Limits) :
    (planGeneral s0 s1 lim).isSome ↔ viable s0 s1 lim := by
  unfold planGeneral
  split_ifs with h <;> simp [h]

/-- Every profile returned by `planGeneral` has the requested boundaries. -/
theorem planGeneral_boundary (s0 s1 : State) (lim : Limits) (p : Profile)
    (hp : planGeneral s0 s1 lim = some p) : p.start = s0 ∧ p.endState = s1 := by
  unfold planGeneral at hp
  split_ifs at hp with h
  · dsimp only at hp
    injection hp with hp
    subst hp
    exact boundary_stopMoveStart s0 s1 lim h.1 h.2

/-- Every profile returned by `planGeneral` is feasible. -/
theorem planGeneral_feasible (s0 s1 : State) (lim : Limits) (p : Profile)
    (hp : planGeneral s0 s1 lim = some p) : Feasible p lim := by
  unfold planGeneral at hp
  split_ifs at hp with h
  · dsimp only at hp
    injection hp with hp
    subst hp
    exact feasible_stopMoveStart s0 s1 lim h.1 h.2

/-- Every profile returned by `planGeneral` has at most fifteen segments. -/
theorem planGeneral_length_le (s0 s1 : State) (lim : Limits) (p : Profile)
    (hp : planGeneral s0 s1 lim = some p) : p.segments.length ≤ 15 := by
  unfold planGeneral at hp
  split_ifs at hp with h
  · dsimp only at hp
    injection hp with hp
    subst hp
    have hstop : (stopProfile s0 lim).segments.length ≤ 4 :=
      stopProfile_length_le s0 lim h.1
    have hstart : (startProfile s1 lim).segments.length ≤ 4 :=
      startProfile_length_le s1 lim h.2
    have hmid : (planRestConservative (stopProfile s0 lim).endState.q
        (startProfile s1 lim).start.q lim).segments.length ≤ 7 :=
      planRestConservative_length_le _ _ lim
    simp only [Profile.append, List.length_append]
    have hbc : (planRestConservative (stopProfile s0 lim).endState.q
        (startProfile s1 lim).start.q lim).segments.length +
          (startProfile s1 lim).segments.length ≤ 11 := by
      simpa using Nat.add_le_add hmid hstart
    have h := Nat.add_le_add hstop hbc
    simpa using h

end Motion
