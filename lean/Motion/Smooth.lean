module
public import Motion.Basic
public import Motion.Glue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open Set Filter
open scoped Topology

@[expose] public section

/-!
# Smoothness of motion profiles

`Motion.Glue` proves that two globally `C^n` functions agreeing in value and in their
first `n` derivatives glue into a globally `C^n` piecewise function. This file applies
that lemma to `evalFrom`: every segment is a cubic, the join conditions are the fold's
exit/entry conditions, and induction over the segment list yields global `C^2` regularity
of the position trajectory together with the derivative identities
`q' = v`, `v' = a`.

The intermediate value conditions also give the mean-value inputs used by the planner
proofs downstream, and the seven-slot rest-to-rest template's velocity is shown
nonnegative so that the conservative planner's position trajectory is monotone.
-/

namespace Motion

/-! ## Derivatives of a single cubic -/

/-- The position of a cubic segment has the segment velocity as its derivative. -/
theorem hasDerivAt_stateAt_q (st : State) (s : Segment) (t : ℝ) :
    HasDerivAt (fun τ => (s.stateAt st τ).q) (s.stateAt st t).v t := by
  have hq : HasDerivAt
      (fun τ : ℝ => st.q + st.v * τ + st.a * τ ^ 2 / 2 + s.jerk * τ ^ 3 / 6)
      (st.v + st.a * t + s.jerk * t ^ 2 / 2) t := by
    have h3 : HasDerivAt (fun τ : ℝ => τ ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have h2 : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 : HasDerivAt (fun τ : ℝ => st.v * τ) st.v t := by
      simpa using hasDerivAt_const_mul (x := t) (c := st.v)
    have h0 : HasDerivAt (fun _ : ℝ => st.q) 0 t := hasDerivAt_const (x := t) (c := st.q)
    have h2' : HasDerivAt (fun τ : ℝ => st.a * τ ^ 2 / 2) (st.a * (2 * t) / 2) t := by
      simpa using (h2.const_mul st.a).div_const 2
    have h3' : HasDerivAt (fun τ : ℝ => s.jerk * τ ^ 3 / 6) (s.jerk * (3 * t ^ 2) / 6) t := by
      simpa using (h3.const_mul s.jerk).div_const 6
    have h := ((h0.add h1).add h2').add h3'
    convert h using 1; ring
  have hfun : (fun τ => (s.stateAt st τ).q) =
      fun τ : ℝ => st.q + st.v * τ + st.a * τ ^ 2 / 2 + s.jerk * τ ^ 3 / 6 := by
    funext τ; rfl
  rw [hfun]
  exact hq

/-- The velocity of a cubic segment has the segment acceleration as its derivative. -/
theorem hasDerivAt_stateAt_v (st : State) (s : Segment) (t : ℝ) :
    HasDerivAt (fun τ => (s.stateAt st τ).v) (s.stateAt st t).a t := by
  have ha : HasDerivAt (fun τ : ℝ => st.v + st.a * τ + s.jerk * τ ^ 2 / 2)
      (st.a + s.jerk * t) t := by
    have h2 : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 : HasDerivAt (fun τ : ℝ => st.a * τ) st.a t := by
      simpa using hasDerivAt_const_mul (x := t) (c := st.a)
    have h0 : HasDerivAt (fun _ : ℝ => st.v) 0 t := hasDerivAt_const (x := t) (c := st.v)
    have h2' : HasDerivAt (fun τ : ℝ => s.jerk * τ ^ 2 / 2) (s.jerk * (2 * t) / 2) t := by
      simpa using (h2.const_mul s.jerk).div_const 2
    have h := (h0.add h1).add h2'
    convert h using 1; ring
  have hfun : (fun τ => (s.stateAt st τ).v) =
      fun τ : ℝ => st.v + st.a * τ + s.jerk * τ ^ 2 / 2 := by
    funext τ; rfl
  rw [hfun]
  exact ha

/-- The derivative of a segment's position is its velocity. -/
theorem deriv_stateAt_q (st : State) (s : Segment) (t : ℝ) :
    deriv (fun τ => (s.stateAt st τ).q) t = (s.stateAt st t).v :=
  (hasDerivAt_stateAt_q st s t).deriv

/-- The derivative of a segment's velocity is its acceleration. -/
theorem deriv_stateAt_v (st : State) (s : Segment) (t : ℝ) :
    deriv (fun τ => (s.stateAt st τ).v) t = (s.stateAt st t).a :=
  (hasDerivAt_stateAt_v st s t).deriv

/-- The second derivative of a segment's position is its acceleration. -/
theorem iteratedDeriv_two_stateAt_q (st : State) (s : Segment) (t : ℝ) :
    iteratedDeriv 2 (fun τ => (s.stateAt st τ).q) t = (s.stateAt st t).a := by
  have hderiv : deriv (fun τ => (s.stateAt st τ).q) = fun τ => (s.stateAt st τ).v := by
    funext τ
    exact deriv_stateAt_q st s τ
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv]
  exact deriv_stateAt_v st s t

/-- A cubic segment's position is `C^2` (it is a polynomial). -/
theorem contDiff_stateAt_q (st : State) (s : Segment) :
    ContDiff ℝ 2 (fun τ => (s.stateAt st τ).q) := by
  fun_prop

/-! ## Piecewise gluing -/

/-- Two globally `C^n` real functions that agree in value and in their first `n`
derivatives at `c` glue to a globally `C^n` function at a strict cut. -/
theorem hasDerivAt_piecewise_lt {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hfc : f c = g c) :
    HasDerivAt (fun t => if t < c then f t else g t) d c := by
  have hf' : HasDerivWithinAt (fun t => if t < c then f t else g t) d (Set.Iic c) c := by
    refine hf.hasDerivWithinAt.congr ?_ ?_
    · intro y hy
      have hyc : y ≤ c := hy
      by_cases hlt : y < c
      · simp [hlt]
      · have hye : y = c := le_antisymm hyc (le_of_not_gt hlt)
        subst hye
        simp [hfc]
    · simp [hfc]
  have hg' : HasDerivWithinAt (fun t => if t < c then f t else g t) d (Set.Ici c) c := by
    refine hg.hasDerivWithinAt.congr ?_ ?_
    · intro y hy
      have hyc : c ≤ y := hy
      by_cases hlt : y < c
      · exact absurd hlt (not_lt.mpr hyc)
      · simp [hlt]
    · simp
  have hunion := hf'.union hg'
  rw [Set.Iic_union_Ici] at hunion
  simpa using hunion

/-- The strict-cut variant of `contDiff_piecewise_le`: two globally `C^n` real functions
that agree in value and in their first `n` derivatives at `c` glue to a globally `C^n`
function across the cut `t < c`. -/
theorem contDiff_piecewise_lt {n : ℕ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (h : ∀ k ≤ n, iteratedDeriv k f c = iteratedDeriv k g c) :
    ContDiff ℝ n (fun t => if t < c then f t else g t) := by
  have hfc : f c = g c := by
    have h0 := h 0 (Nat.zero_le n)
    simpa using h0
  have heq : (fun t => if t < c then f t else g t) =
      fun t => if t ≤ c then f t else g t := by
    funext t
    by_cases hlt : t < c
    · simp [hlt, le_of_lt hlt]
    · by_cases htc : t = c
      · subst htc
        simp [hfc]
      · have hle : ¬ t ≤ c := fun h => hlt (lt_of_le_of_ne h htc)
        simp [hlt, hle]
  rw [heq]
  exact contDiff_piecewise_le hf hg h

/-! ## Derivatives along a segment chain -/

/-- The position of a nonempty segment chain has the chain's velocity as its derivative. -/
private theorem evalFrom_hasDerivAt_q_aux :
    ∀ (ss : List Segment) (st : State) (t : ℝ), ss ≠ [] →
      HasDerivAt (fun τ => (evalFrom st ss τ).q) ((evalFrom st ss t).v) t := by
  intro ss
  induction ss with
  | nil => intro st t h; exact absurd rfl h
  | cons s ss ih =>
      intro st t _
      cases ss with
      | nil => simpa [evalFrom] using hasDerivAt_stateAt_q st s t
      | cons s' rest =>
          have htail : HasDerivAt
              (fun τ => (evalFrom (s.exit st) (s' :: rest) τ).q)
              ((evalFrom (s.exit st) (s' :: rest) (t - s.dur)).v) (t - s.dur) :=
            ih (s.exit st) (t - s.dur) (by simp)
          by_cases hlt : t < s.dur
          · have hev : (fun τ => (evalFrom st (s :: s' :: rest) τ).q) =ᶠ[𝓝 t]
                (fun τ => (s.stateAt st τ).q) := by
              filter_upwards [Iio_mem_nhds hlt] with τ hτ
              rw [evalFrom_cons_cons]
              split_ifs with h
              · rfl
              · exact absurd hτ h
            have h' := (hasDerivAt_stateAt_q st s t).congr_of_eventuallyEq hev
            simpa [evalFrom_cons_cons, hlt] using h'
          · by_cases hgt : s.dur < t
            · have hev : (fun τ => (evalFrom st (s :: s' :: rest) τ).q) =ᶠ[𝓝 t]
                  (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).q) := by
                filter_upwards [Ioi_mem_nhds hgt] with τ hτ
                have hτ' : s.dur < τ := hτ
                rw [evalFrom_cons_cons]
                split_ifs with h
                · exact absurd h (not_lt.mpr (le_of_lt hτ'))
                · rfl
              have h' := (htail.comp_sub_const t s.dur).congr_of_eventuallyEq hev
              simpa [evalFrom_cons_cons, not_lt.mpr (le_of_lt hgt)] using h'
            · have htc : t = s.dur :=
                (le_antisymm (le_of_not_gt hlt) (le_of_not_gt hgt)).symm
              subst htc
              have hf : HasDerivAt (fun τ => (s.stateAt st τ).q) ((s.stateAt st s.dur).v) s.dur :=
                hasDerivAt_stateAt_q st s s.dur
              have hg : HasDerivAt
                  (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).q)
                  ((s.stateAt st s.dur).v) s.dur := by
                simpa [Segment.exit] using htail.comp_sub_const s.dur s.dur
              have hfc : (s.stateAt st s.dur).q =
                  (evalFrom (s.exit st) (s' :: rest) (s.dur - s.dur)).q := by
                simp [Segment.exit]
              have hpiece := hasDerivAt_piecewise_lt hf hg hfc
              have hgoal : (fun τ => (evalFrom st (s :: s' :: rest) τ).q) =
                  fun τ => if τ < s.dur then (s.stateAt st τ).q
                    else (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).q := by
                funext τ
                rw [evalFrom_cons_cons]
                split_ifs with h
                · rfl
                · rfl
              rw [hgoal]
              convert hpiece using 1
              simp [evalFrom_cons_cons, Segment.exit]

/-- The velocity of a nonempty segment chain has the chain's acceleration as its
derivative. -/
private theorem evalFrom_hasDerivAt_v_aux :
    ∀ (ss : List Segment) (st : State) (t : ℝ), ss ≠ [] →
      HasDerivAt (fun τ => (evalFrom st ss τ).v) ((evalFrom st ss t).a) t := by
  intro ss
  induction ss with
  | nil => intro st t h; exact absurd rfl h
  | cons s ss ih =>
      intro st t _
      cases ss with
      | nil => simpa [evalFrom] using hasDerivAt_stateAt_v st s t
      | cons s' rest =>
          have htail : HasDerivAt
              (fun τ => (evalFrom (s.exit st) (s' :: rest) τ).v)
              ((evalFrom (s.exit st) (s' :: rest) (t - s.dur)).a) (t - s.dur) :=
            ih (s.exit st) (t - s.dur) (by simp)
          by_cases hlt : t < s.dur
          · have hev : (fun τ => (evalFrom st (s :: s' :: rest) τ).v) =ᶠ[𝓝 t]
                (fun τ => (s.stateAt st τ).v) := by
              filter_upwards [Iio_mem_nhds hlt] with τ hτ
              rw [evalFrom_cons_cons]
              split_ifs with h
              · rfl
              · exact absurd hτ h
            have h' := (hasDerivAt_stateAt_v st s t).congr_of_eventuallyEq hev
            simpa [evalFrom_cons_cons, hlt] using h'
          · by_cases hgt : s.dur < t
            · have hev : (fun τ => (evalFrom st (s :: s' :: rest) τ).v) =ᶠ[𝓝 t]
                  (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).v) := by
                filter_upwards [Ioi_mem_nhds hgt] with τ hτ
                have hτ' : s.dur < τ := hτ
                rw [evalFrom_cons_cons]
                split_ifs with h
                · exact absurd h (not_lt.mpr (le_of_lt hτ'))
                · rfl
              have h' := (htail.comp_sub_const t s.dur).congr_of_eventuallyEq hev
              simpa [evalFrom_cons_cons, not_lt.mpr (le_of_lt hgt)] using h'
            · have htc : t = s.dur :=
                (le_antisymm (le_of_not_gt hlt) (le_of_not_gt hgt)).symm
              subst htc
              have hf : HasDerivAt (fun τ => (s.stateAt st τ).v) ((s.stateAt st s.dur).a) s.dur :=
                hasDerivAt_stateAt_v st s s.dur
              have hg : HasDerivAt
                  (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).v)
                  ((s.stateAt st s.dur).a) s.dur := by
                simpa [Segment.exit] using htail.comp_sub_const s.dur s.dur
              have hfc : (s.stateAt st s.dur).v =
                  (evalFrom (s.exit st) (s' :: rest) (s.dur - s.dur)).v := by
                simp [Segment.exit]
              have hpiece := hasDerivAt_piecewise_lt hf hg hfc
              have hgoal : (fun τ => (evalFrom st (s :: s' :: rest) τ).v) =
                  fun τ => if τ < s.dur then (s.stateAt st τ).v
                    else (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).v := by
                funext τ
                rw [evalFrom_cons_cons]
                split_ifs with h
                · rfl
                · rfl
              rw [hgoal]
              convert hpiece using 1
              simp [evalFrom_cons_cons, Segment.exit]

/-- The position derivative of a nonempty segment chain is its velocity. -/
theorem evalFrom_hasDerivAt_q (st : State) (s : Segment) (ss : List Segment) (t : ℝ) :
    HasDerivAt (fun τ => (evalFrom st (s :: ss) τ).q) ((evalFrom st (s :: ss) t).v) t :=
  evalFrom_hasDerivAt_q_aux (s :: ss) st t (by simp)

/-- The velocity derivative of a nonempty segment chain is its acceleration. -/
theorem evalFrom_hasDerivAt_v (st : State) (s : Segment) (ss : List Segment) (t : ℝ) :
    HasDerivAt (fun τ => (evalFrom st (s :: ss) τ).v) ((evalFrom st (s :: ss) t).a) t :=
  evalFrom_hasDerivAt_v_aux (s :: ss) st t (by simp)

/-- The derivative of a nonempty chain's position is its velocity. -/
theorem deriv_evalFrom_q (ss : List Segment) (st : State) (t : ℝ) (hne : ss ≠ []) :
    deriv (fun τ => (evalFrom st ss τ).q) t = (evalFrom st ss t).v :=
  (evalFrom_hasDerivAt_q_aux ss st t hne).deriv

/-- The derivative of a nonempty chain's velocity is its acceleration. -/
theorem deriv_evalFrom_v (ss : List Segment) (st : State) (t : ℝ) (hne : ss ≠ []) :
    deriv (fun τ => (evalFrom st ss τ).v) t = (evalFrom st ss t).a :=
  (evalFrom_hasDerivAt_v_aux ss st t hne).deriv

/-- The second derivative of a nonempty chain's position at `0` is the start
acceleration. -/
theorem evalFrom_iteratedDeriv_two_zero (st : State) (s : Segment) (ss : List Segment) :
    iteratedDeriv 2 (fun t => (evalFrom st (s :: ss) t).q) 0 = st.a := by
  have hne : (s :: ss) ≠ [] := by simp
  have hderiv : deriv (fun t => (evalFrom st (s :: ss) t).q) =
      fun t => (evalFrom st (s :: ss) t).v := by
    funext t
    exact deriv_evalFrom_q (s :: ss) st t hne
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv]
  have hv : deriv (fun t => (evalFrom st (s :: ss) t).v) 0 =
      (evalFrom st (s :: ss) 0).a :=
    (evalFrom_hasDerivAt_v_aux (s :: ss) st 0 hne).deriv
  rw [hv, evalFrom_zero]

/-! ## Smoothness of the chain -/

/-- The position trajectory of a nonempty segment chain is globally `C^2`. -/
private theorem evalFrom_contDiff_q_aux :
    ∀ (ss : List Segment) (st : State), ss ≠ [] →
      ContDiff ℝ 2 (fun t => (evalFrom st ss t).q) := by
  intro ss
  induction ss with
  | nil => intro st h; exact absurd rfl h
  | cons s ss ih =>
      intro st _
      cases ss with
      | nil => simpa [evalFrom] using contDiff_stateAt_q st s
      | cons s' rest =>
          have htail : ContDiff ℝ 2 (fun t => (evalFrom (s.exit st) (s' :: rest) t).q) :=
            ih (s.exit st) (by simp)
          have hg : ContDiff ℝ 2
              (fun t => (evalFrom (s.exit st) (s' :: rest) (t - s.dur)).q) := by
            have hsub : ContDiff ℝ 2 (fun t : ℝ => t - s.dur) :=
              contDiff_id.sub contDiff_const
            exact htail.comp hsub
          have hfun : (fun t => (evalFrom st (s :: s' :: rest) t).q) =
              fun t => if t < s.dur then (s.stateAt st t).q
                else (evalFrom (s.exit st) (s' :: rest) (t - s.dur)).q := by
            funext t
            rw [evalFrom_cons_cons]
            split_ifs with h
            · rfl
            · rfl
          rw [hfun]
          refine contDiff_piecewise_lt (contDiff_stateAt_q st s) hg ?_
          intro k hk
          interval_cases k
          · -- value
            simp [Segment.exit]
          · -- first derivative
            have h1 : iteratedDeriv 1 (fun τ => (s.stateAt st τ).q) s.dur =
                (s.exit st).v := by
              rw [iteratedDeriv_one, deriv_stateAt_q]
              rfl
            have h2 : iteratedDeriv 1
                (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).q) s.dur =
                (s.exit st).v := by
              have hshift : iteratedDeriv 1
                  (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).q) =
                  fun t => iteratedDeriv 1
                    (fun u => (evalFrom (s.exit st) (s' :: rest) u).q) (t - s.dur) := by
                simpa only [Function.comp_def] using
                  (iteratedDeriv_comp_sub_const (n := 1)
                    (f := fun u => (evalFrom (s.exit st) (s' :: rest) u).q) (s := s.dur))
              rw [hshift]
              simp only [sub_self, iteratedDeriv_one]
              rw [deriv_evalFrom_q (s' :: rest) (s.exit st) 0 (by simp)]
              simp
            rw [h1, h2]
          · -- second derivative
            have h1 : iteratedDeriv 2 (fun τ => (s.stateAt st τ).q) s.dur =
                (s.exit st).a := by
              rw [iteratedDeriv_two_stateAt_q]
              rfl
            have h2 : iteratedDeriv 2
                (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).q) s.dur =
                (s.exit st).a := by
              have hshift : iteratedDeriv 2
                  (fun τ => (evalFrom (s.exit st) (s' :: rest) (τ - s.dur)).q) =
                  fun t => iteratedDeriv 2
                    (fun u => (evalFrom (s.exit st) (s' :: rest) u).q) (t - s.dur) := by
                simpa only [Function.comp_def] using
                  (iteratedDeriv_comp_sub_const (n := 2)
                    (f := fun u => (evalFrom (s.exit st) (s' :: rest) u).q) (s := s.dur))
              rw [hshift]
              simp only [sub_self]
              rw [evalFrom_iteratedDeriv_two_zero]
            rw [h1, h2]

/-- The position trajectory of a nonempty segment chain is globally `C^2`, stated for
an arbitrary nonempty list. -/
theorem evalFrom_contDiff_q_of_ne (ss : List Segment) (st : State) (hne : ss ≠ []) :
    ContDiff ℝ 2 (fun t => (evalFrom st ss t).q) :=
  evalFrom_contDiff_q_aux ss st hne

/-- The position trajectory of a list with a distinguished head is globally `C^2`. -/
theorem evalFrom_contDiff_q (st : State) (s : Segment) (ss : List Segment) :
    ContDiff ℝ 2 (fun t => (evalFrom st (s :: ss) t).q) :=
  evalFrom_contDiff_q_aux (s :: ss) st (by simp)

/-! ## The seven-slot rest-to-rest template -/

/-- The seven-slot template `(τ, 0, τ, τc, τ, 0, τ)` with jerks `(j, 0, -j, 0, -j, 0, j)`
starting from rest has nonnegative velocity at every time. This is what makes the
conservative planner's position trajectory monotone. -/
theorem evalFrom_template_v_nonneg (q0 j τ τc : ℝ) {hτ : 0 ≤ τ} {hτc : 0 ≤ τc}
    (hj : 0 ≤ j) (t : ℝ) :
    0 ≤ (evalFrom { q := q0, v := 0, a := 0 }
      [ { dur := τ, dur_nonneg := hτ, jerk := j },
        { dur := 0, dur_nonneg := le_rfl, jerk := 0 },
        { dur := τ, dur_nonneg := hτ, jerk := -j },
        { dur := τc, dur_nonneg := hτc, jerk := 0 },
        { dur := τ, dur_nonneg := hτ, jerk := -j },
        { dur := 0, dur_nonneg := le_rfl, jerk := 0 },
        { dur := τ, dur_nonneg := hτ, jerk := j } ] t).v := by
  simp only [evalFrom_cons_cons]
  split_ifs with h1 h2 h3 h4 h5 h6
  · -- ramp up: `v = j t²/2`
    simp only [Segment.stateAt]
    nlinarith [mul_nonneg hj (sq_nonneg t)]
  · -- the zero-duration slot cannot be entered with a negative local time
    linarith
  · -- ramp down from the first peak: `v = j τ²/2 + j τ u - j u²/2`
    simp only [Segment.exit, Segment.stateAt]
    nlinarith [mul_nonneg hj (sq_nonneg (τ - (t - τ - 0))),
      mul_nonneg hj (mul_nonneg (by linarith : (0:ℝ) ≤ t - τ - 0)
        (by linarith : (0:ℝ) ≤ 2 * τ - (t - τ - 0))),
      mul_nonneg hj (sq_nonneg τ)]
  · -- cruise at the peak velocity `j τ²`
    simp only [Segment.exit, Segment.stateAt]
    nlinarith [mul_nonneg hj (sq_nonneg τ)]
  · -- ramp down from the cruise: `v = j τ² - j τ u + j u²/2`
    simp only [Segment.exit, Segment.stateAt]
    nlinarith [mul_nonneg hj (sq_nonneg τ),
      mul_nonneg hj (sq_nonneg (τ - (t - τ - 0 - τ - τc)))]
  · -- the second zero-duration slot cannot be entered with a negative local time
    linarith
  · -- final ramp: `v = j (τ - u)²/2`
    simp only [evalFrom, Segment.exit, Segment.stateAt]
    nlinarith [mul_nonneg (div_nonneg hj (by norm_num : (0:ℝ) ≤ 2))
      (sq_nonneg (τ - (t - τ - 0 - τ - τc - τ - 0)))]

end Motion
