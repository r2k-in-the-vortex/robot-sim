module
-- The declarations in this file are exported (`@[expose] public section`), so
-- everything their types and bodies mention has to be part of the public interface.
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

open MeasureTheory

noncomputable section

@[expose] public section

/-!
# Motion: the structural core

The representation, evaluation and reparameterisation of jerk-limited scalar motion
profiles, as specified in `docs/motion_control.md` §4.1–§4.3.

A `Profile` is the start state plus a list of constant-jerk segments. `evalFrom` folds
the segments, and its singleton clause extends the last cubic past the end of the
profile, which makes a profile a globally piecewise-polynomial function. That is what
lets the gluing lemma in `Motion.Glue` prove smoothness without endpoint case analysis;
Rust's `eval` clamps instead, a difference that only shows for `t > totalTime`.

`Feasible` states the velocity, acceleration and jerk bounds on the representation:
the state fields are the polynomial derivatives, so they can be quantified on the
closed interval, while `FeasibleOn` is the function-level predicate with derivatives
on the open interval. The bridge between the two needs the a.e. third-derivative
identity and is not proved here.
-/

namespace Motion

/-! ## Limits and states -/

/-- Velocity, acceleration and jerk limits. -/
structure Limits where
  vmax : ℝ
  amax : ℝ
  jmax : ℝ
  vmax_pos : 0 < vmax
  amax_pos : 0 < amax
  jmax_pos : 0 < jmax

/-- A scalar motion state: position, velocity and acceleration. -/
@[ext] structure State where
  q : ℝ
  v : ℝ
  a : ℝ

/-- A constant-jerk segment. -/
structure Segment where
  dur : ℝ
  dur_nonneg : 0 ≤ dur
  jerk : ℝ

/-- A profile: the start state and the list of segments. -/
structure Profile where
  start : State
  segments : List Segment

namespace Segment

/-- The state `τ` into the segment, starting from `st`. -/
def stateAt (st : State) (s : Segment) (τ : ℝ) : State :=
  { q := st.q + st.v*τ + st.a*τ^2/2 + s.jerk*τ^3/6
    v := st.v + st.a*τ + s.jerk*τ^2/2
    a := st.a + s.jerk*τ }

/-- The segment's exit state. -/
def exit (st : State) (s : Segment) : State :=
  s.stateAt st s.dur

@[simp] theorem stateAt_q (st : State) (s : Segment) (τ : ℝ) :
    (s.stateAt st τ).q = st.q + st.v*τ + st.a*τ^2/2 + s.jerk*τ^3/6 := rfl

@[simp] theorem stateAt_v (st : State) (s : Segment) (τ : ℝ) :
    (s.stateAt st τ).v = st.v + st.a*τ + s.jerk*τ^2/2 := rfl

@[simp] theorem stateAt_a (st : State) (s : Segment) (τ : ℝ) :
    (s.stateAt st τ).a = st.a + s.jerk*τ := rfl

@[simp] theorem exit_q (st : State) (s : Segment) :
    (s.exit st).q = st.q + st.v*s.dur + st.a*s.dur^2/2 + s.jerk*s.dur^3/6 := rfl

@[simp] theorem exit_v (st : State) (s : Segment) :
    (s.exit st).v = st.v + st.a*s.dur + s.jerk*s.dur^2/2 := rfl

@[simp] theorem exit_a (st : State) (s : Segment) :
    (s.exit st).a = st.a + s.jerk*s.dur := rfl

/-- At the start of a segment the state is unchanged. -/
@[simp] theorem stateAt_zero (st : State) (s : Segment) : s.stateAt st 0 = st := by
  ext <;> simp [Segment.stateAt]

/-- A zero-duration segment has no effect. -/
theorem exit_of_dur_eq_zero {st : State} {s : Segment} (h : s.dur = 0) : s.exit st = st := by
  rw [Segment.exit, h]
  simp

/-- The acceleration at time `τ` is the affine interpolation of the endpoint
accelerations (when the duration is positive). -/
theorem stateAt_a_eq (st : State) (s : Segment) {τ : ℝ} (hd : 0 < s.dur) :
    (s.stateAt st τ).a = (1 - τ / s.dur) * st.a + (τ / s.dur) * (s.exit st).a := by
  simp only [stateAt_a, exit_a]
  field_simp
  ring

/-- A segment whose endpoint accelerations are both nonnegative has nonnegative
acceleration throughout. -/
theorem stateAt_a_nonneg (st : State) (s : Segment) {τ : ℝ}
    (h0 : 0 ≤ st.a) (h1 : 0 ≤ (s.exit st).a) (hτ : τ ∈ Set.Icc 0 s.dur) :
    0 ≤ (s.stateAt st τ).a := by
  rcases eq_or_lt_of_le s.dur_nonneg with hd | hd
  · have hτ0 : τ = 0 := le_antisymm (hd ▸ hτ.2) hτ.1
    rw [hτ0]
    simpa using h0
  · rw [stateAt_a_eq st s hd]
    have hlam0 : 0 ≤ τ / s.dur := div_nonneg hτ.1 (le_of_lt hd)
    have hlam1 : τ / s.dur ≤ 1 := (div_le_one hd).mpr hτ.2
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hlam1) h0) (mul_nonneg hlam0 h1)

/-- A segment whose endpoint accelerations are both nonpositive has nonpositive
acceleration throughout. -/
theorem stateAt_a_nonpos (st : State) (s : Segment) {τ : ℝ}
    (h0 : st.a ≤ 0) (h1 : (s.exit st).a ≤ 0) (hτ : τ ∈ Set.Icc 0 s.dur) :
    (s.stateAt st τ).a ≤ 0 := by
  rcases eq_or_lt_of_le s.dur_nonneg with hd | hd
  · have hτ0 : τ = 0 := le_antisymm (hd ▸ hτ.2) hτ.1
    rw [hτ0]
    simpa using h0
  · rw [stateAt_a_eq st s hd]
    have hlam0 : 0 ≤ τ / s.dur := div_nonneg hτ.1 (le_of_lt hd)
    have hlam1 : τ / s.dur ≤ 1 := (div_le_one hd).mpr hτ.2
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlam1) h0)
      (mul_nonpos_of_nonneg_of_nonpos hlam0 h1)

/-- Velocity increment over `[0, τ]` in terms of the mean acceleration. -/
theorem stateAt_v_sub (st : State) (s : Segment) (τ : ℝ) :
    (s.stateAt st τ).v - st.v = τ * (st.a + (s.stateAt st τ).a) / 2 := by
  simp only [stateAt_v, stateAt_a]
  ring

/-- The remaining velocity increment over `[τ, dur]`. -/
theorem exit_v_sub (st : State) (s : Segment) (τ : ℝ) :
    (s.exit st).v - (s.stateAt st τ).v =
      (s.dur - τ) * ((s.stateAt st τ).a + (s.exit st).a) / 2 := by
  simp only [stateAt_v, stateAt_a, exit_v, exit_a]
  ring

end Segment

/-! ## Evaluation -/

/-- Evaluate a segment list from a start state. The last segment's cubic is extended past
its end, so the result is globally piecewise polynomial. -/
def evalFrom (st : State) : List Segment → ℝ → State
  | [], _      => st
  | [s], t     => s.stateAt st t
  | s :: ss, t =>
      if t < s.dur then s.stateAt st t
      else evalFrom (s.exit st) ss (t - s.dur)

/-- The fold equation for a list with a nonempty tail. -/
theorem evalFrom_cons_ne (st : State) (s : Segment) (ss : List Segment) (t : ℝ)
    (hne : ss ≠ []) :
    evalFrom st (s :: ss) t =
      if t < s.dur then s.stateAt st t else evalFrom (s.exit st) ss (t - s.dur) :=
  evalFrom.eq_3 st t s ss (by simpa using hne)

/-- The fold equation for a list of at least two segments. -/
theorem evalFrom_cons_cons (st : State) (s s' : Segment) (ss : List Segment) (t : ℝ) :
    evalFrom st (s :: s' :: ss) t =
      if t < s.dur then s.stateAt st t
      else evalFrom (s.exit st) (s' :: ss) (t - s.dur) :=
  evalFrom_cons_ne st s (s' :: ss) t (by simp)

/-- Evaluation at `0` returns the start state. -/
@[simp] theorem evalFrom_zero (st : State) (ss : List Segment) : evalFrom st ss 0 = st := by
  induction ss generalizing st with
  | nil => rfl
  | cons s ss ih =>
      cases ss with
      | nil =>
          rw [evalFrom]
          exact Segment.stateAt_zero st s
      | cons s' rest =>
          rw [evalFrom_cons_cons]
          by_cases h : 0 < s.dur
          · rw [if_pos h]
            exact Segment.stateAt_zero st s
          · rw [if_neg h]
            have hd : s.dur = 0 := le_antisymm (le_of_not_gt h) s.dur_nonneg
            rw [Segment.exit_of_dur_eq_zero hd, hd, sub_zero]
            exact ih st

/-- Durations are nonnegative. -/
theorem durations_nonneg (ss : List Segment) : 0 ≤ (ss.map Segment.dur).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih => exact add_nonneg s.dur_nonneg ih

/-- Evaluation at the total time returns the folded end state. -/
theorem evalFrom_totalTime (st : State) (ss : List Segment) :
    evalFrom st ss (ss.map Segment.dur).sum = ss.foldl Segment.exit st := by
  induction ss generalizing st with
  | nil => rfl
  | cons s ss ih =>
      cases ss with
      | nil =>
          rw [evalFrom]
          simp [Segment.exit]
      | cons s' rest =>
          rw [evalFrom_cons_cons]
          have hsum : ((s :: s' :: rest).map Segment.dur).sum
              = s.dur + ((s' :: rest).map Segment.dur).sum := by simp
          rw [hsum]
          have hnonneg : 0 ≤ ((s' :: rest).map Segment.dur).sum := durations_nonneg _
          have hlt : ¬ s.dur + ((s' :: rest).map Segment.dur).sum < s.dur := by linarith
          rw [if_neg hlt]
          have hsub : s.dur + ((s' :: rest).map Segment.dur).sum - s.dur
              = ((s' :: rest).map Segment.dur).sum := by ring
          rw [hsub]
          exact ih (s.exit st)

namespace Profile

/-- Profile evaluation. -/
def stateAt (p : Profile) (t : ℝ) : State :=
  evalFrom p.start p.segments t

/-- Total duration. -/
def totalTime (p : Profile) : ℝ :=
  (p.segments.map Segment.dur).sum

/-- The folded end state. -/
def endState (p : Profile) : State :=
  p.segments.foldl Segment.exit p.start

@[simp] theorem stateAt_zero (p : Profile) : p.stateAt 0 = p.start :=
  evalFrom_zero p.start p.segments

theorem stateAt_totalTime (p : Profile) : p.stateAt p.totalTime = p.endState :=
  evalFrom_totalTime p.start p.segments

/-- The position trajectory. -/
def q (p : Profile) (t : ℝ) : ℝ := (p.stateAt t).q

/-- The velocity trajectory. -/
def v (p : Profile) (t : ℝ) : ℝ := (p.stateAt t).v

/-- The acceleration trajectory. -/
def a (p : Profile) (t : ℝ) : ℝ := (p.stateAt t).a

end Profile

/-- The active segment's jerk under the later-segment rule; `0` for an empty profile. -/
def jerkAtFrom : List Segment → ℝ → ℝ
  | [], _      => 0
  | [s], _     => s.jerk
  | s :: ss, t => if t < s.dur then s.jerk else jerkAtFrom ss (t - s.dur)

/-- The profile's jerk. -/
def Profile.jerkAt (p : Profile) (t : ℝ) : ℝ := jerkAtFrom p.segments t

/-! ## Displacement -/

/-- The displacement contributed by a segment chain. -/
def displacementFrom (st : State) : List Segment → ℝ
  | [] => 0
  | s :: ss =>
      (st.v*s.dur + st.a*s.dur^2/2 + s.jerk*s.dur^3/6)
        + displacementFrom (s.exit st) ss

namespace Profile

/-- The total position change of a profile. -/
def displacement (p : Profile) : ℝ := displacementFrom p.start p.segments

end Profile

theorem endState_q_from (st : State) (ss : List Segment) :
    (ss.foldl Segment.exit st).q = st.q + displacementFrom st ss := by
  induction ss generalizing st with
  | nil => simp [displacementFrom]
  | cons s ss ih =>
      rw [List.foldl_cons, ih (s.exit st)]
      simp only [displacementFrom, Segment.exit, Segment.stateAt]
      ring

theorem endState_q (p : Profile) :
    p.endState.q = p.start.q + p.displacement :=
  endState_q_from p.start p.segments

/-! ## Feasibility -/

/-- The representation-level feasibility predicate. The zero-duration guard in the jerk
clause is deliberate: a zero-duration segment is invisible to the a.e. third
derivative, and the planners emit those slots with `jerk = 0`. -/
def Feasible (p : Profile) (lim : Limits) : Prop :=
  (∀ t ∈ Set.Icc 0 p.totalTime, |p.v t| ≤ lim.vmax) ∧
  (∀ t ∈ Set.Icc 0 p.totalTime, |p.a t| ≤ lim.amax) ∧
  (∀ s ∈ p.segments, s.dur > 0 → |s.jerk| ≤ lim.jmax)

/-- The function-level feasibility predicate, with derivatives taken on the open
interval and the jerk bound almost everywhere. -/
def FeasibleOn (f : ℝ → ℝ) (lim : Limits) (a b : ℝ) : Prop :=
  (∀ t ∈ Set.Ioo a b, |deriv f t| ≤ lim.vmax) ∧
  (∀ t ∈ Set.Ioo a b, |iteratedDeriv 2 f t| ≤ lim.amax) ∧
  (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b →
    |iteratedDeriv 3 f t| ≤ lim.jmax)

/-! ## Segment safety -/

/-- The local certificate a planner case discharges for one segment. -/
def SegmentSafe (st : State) (s : Segment) (lim : Limits) : Prop :=
  |st.v| ≤ lim.vmax ∧ |st.a| ≤ lim.amax ∧ |s.jerk| ≤ lim.jmax ∧
  |(s.exit st).v| ≤ lim.vmax ∧ |(s.exit st).a| ≤ lim.amax ∧
  0 ≤ st.a * (s.exit st).a

/-- An affine interpolation of two numbers bounded by `A` is bounded by `A`. -/
theorem abs_affine_le {x y A lam : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ A)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : |(1 - lam) * x + lam * y| ≤ A := by
  rw [abs_le]
  have hxm := abs_le.mp hx
  have hym := abs_le.mp hy
  constructor
  · have hx' := mul_le_mul_of_nonneg_left hxm.1 (sub_nonneg.mpr h1)
    have hy' := mul_le_mul_of_nonneg_left hym.1 h0
    nlinarith
  · have hx' := mul_le_mul_of_nonneg_left hxm.2 (sub_nonneg.mpr h1)
    have hy' := mul_le_mul_of_nonneg_left hym.2 h0
    nlinarith

/-- The local safety certificate bounds velocity and acceleration throughout the
segment: the acceleration is an affine interpolation of its endpoints, and the
velocity lies between its endpoint values because the acceleration has one sign. -/
theorem segmentSafe_bounds {st : State} {s : Segment} {lim : Limits}
    (h : SegmentSafe st s lim) :
    ∀ τ ∈ Set.Icc 0 s.dur,
      |(s.stateAt st τ).v| ≤ lim.vmax ∧ |(s.stateAt st τ).a| ≤ lim.amax := by
  rintro τ hτ
  obtain ⟨hsv, hsa, hsj, hev, hea, hprod⟩ := h
  have haa : |(s.stateAt st τ).a| ≤ lim.amax := by
    rcases eq_or_lt_of_le s.dur_nonneg with hd | hd
    · have hτ0 : τ = 0 := le_antisymm (hd ▸ hτ.2) hτ.1
      rw [hτ0]
      simpa using hsa
    · rw [Segment.stateAt_a_eq st s hd]
      exact abs_affine_le hsa hea (div_nonneg hτ.1 (le_of_lt hd))
        ((div_le_one hd).mpr hτ.2)
  have hvv : |(s.stateAt st τ).v| ≤ lim.vmax := by
    have hsign : (0 ≤ st.a ∧ 0 ≤ (s.exit st).a) ∨ (st.a ≤ 0 ∧ (s.exit st).a ≤ 0) :=
      mul_nonneg_iff.mp hprod
    have hv1 : (s.stateAt st τ).v - st.v
        = τ * (st.a + (s.stateAt st τ).a) / 2 := Segment.stateAt_v_sub st s τ
    have hv2 : (s.exit st).v - (s.stateAt st τ).v
        = (s.dur - τ) * ((s.stateAt st τ).a + (s.exit st).a) / 2 :=
      Segment.exit_v_sub st s τ
    have hsv' := abs_le.mp hsv
    have hev' := abs_le.mp hev
    rcases hsign with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have haτ : 0 ≤ (s.stateAt st τ).a := Segment.stateAt_a_nonneg st s h0 h1 hτ
      have hlow : st.v ≤ (s.stateAt st τ).v := by nlinarith [hτ.1]
      have hhigh : (s.stateAt st τ).v ≤ (s.exit st).v := by
        have hdτ : 0 ≤ s.dur - τ := sub_nonneg.mpr hτ.2
        have hprod2 : 0 ≤ (s.dur - τ) * ((s.stateAt st τ).a + (s.exit st).a) / 2 :=
          div_nonneg (mul_nonneg hdτ (by linarith)) (by norm_num)
        linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have haτ : (s.stateAt st τ).a ≤ 0 := Segment.stateAt_a_nonpos st s h0 h1 hτ
      have hhigh : (s.stateAt st τ).v ≤ st.v := by nlinarith [hτ.1]
      have hlow : (s.exit st).v ≤ (s.stateAt st τ).v := by
        have hdτ : 0 ≤ s.dur - τ := sub_nonneg.mpr hτ.2
        have hsum : (s.stateAt st τ).a + (s.exit st).a ≤ 0 := by linarith
        have hmul : (s.dur - τ) * ((s.stateAt st τ).a + (s.exit st).a) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hdτ hsum
        have hprod2 : (s.dur - τ) * ((s.stateAt st τ).a + (s.exit st).a) / 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hmul (by norm_num)
        linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ⟨hvv, haa⟩

/-- The recursive safety predicate over a segment chain. The nil case is load-bearing:
an empty profile is evaluated at `t = 0` and must satisfy the bounds there. -/
def SafeFrom (lim : Limits) (st : State) : List Segment → Prop
  | []      => |st.v| ≤ lim.vmax ∧ |st.a| ≤ lim.amax
  | s :: ss => SegmentSafe st s lim ∧ SafeFrom lim (s.exit st) ss

/-- A safe chain satisfies the velocity and acceleration bounds on its whole time
interval. -/
theorem bounds_of_safeFrom (lim : Limits) :
    ∀ (ss : List Segment) (st : State) (t : ℝ), SafeFrom lim st ss →
      t ∈ Set.Icc 0 (ss.map Segment.dur).sum →
      |(evalFrom st ss t).v| ≤ lim.vmax ∧ |(evalFrom st ss t).a| ≤ lim.amax := by
  intro ss
  induction ss with
  | nil =>
      intro st t h ht
      simpa [evalFrom, SafeFrom] using h
  | cons s ss ih =>
      intro st t h ht
      cases ss with
      | nil =>
          rw [evalFrom]
          have ht' : t ∈ Set.Icc 0 s.dur := by simpa using ht
          exact segmentSafe_bounds h.1 t ht'
      | cons s' rest =>
          rw [evalFrom_cons_cons]
          by_cases hlt : t < s.dur
          · rw [if_pos hlt]
            exact segmentSafe_bounds h.1 t ⟨ht.1, le_of_lt hlt⟩
          · rw [if_neg hlt]
            have hsum : ((s :: s' :: rest).map Segment.dur).sum
                = s.dur + ((s' :: rest).map Segment.dur).sum := by simp
            rw [hsum] at ht
            have ht' : t - s.dur ∈ Set.Icc 0 ((s' :: rest).map Segment.dur).sum :=
              ⟨by linarith [ht.1], by linarith [ht.2]⟩
            exact ih (s.exit st) (t - s.dur) h.2 ht'

/-- Every positive-duration segment of a safe chain has a bounded jerk. -/
theorem jerk_bound_of_safeFrom (lim : Limits) (ss : List Segment) (st : State)
    (h : SafeFrom lim st ss) :
    ∀ s ∈ ss, s.dur > 0 → |s.jerk| ≤ lim.jmax := by
  induction ss generalizing st with
  | nil => intro s hs; simp at hs
  | cons a as ih =>
      intro s hs hpos
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact h.1.2.2.1
      · exact ih (a.exit st) h.2 s hs' hpos

/-- The safety certificate implies feasibility. -/
theorem feasible_of_safeFrom {lim : Limits} {p : Profile}
    (h : SafeFrom lim p.start p.segments) : Feasible p lim := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (bounds_of_safeFrom lim p.segments p.start t h ht).1
  · intro t ht
    exact (bounds_of_safeFrom lim p.segments p.start t h ht).2
  · exact jerk_bound_of_safeFrom lim p.segments p.start h

end Motion
