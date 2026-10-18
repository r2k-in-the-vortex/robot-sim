module
public import Motion.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

noncomputable section

@[expose] public section

/-!
# Motion: concatenation and transforms

The structural algebra on profiles that the planners consume: concatenation (`append`, with
its evaluation and feasibility lemmas), and the four transforms that map a profile to
another profile of the same feasibility class - position translation, spatial mirroring,
time stretching and time reversal.

`evalFrom` extends a profile's last cubic past its end, so the concatenation law holds
only where the appended tail is nonempty; `evalFrom_append` states that precisely. The
transform laws (`evalFrom_translate`, `evalFrom_mirror`, `evalFrom_stretch`) are proved at
the `evalFrom` level and read off for `Profile` in `stateAt_*`; reversal needs the
boundary hypothesis `t ∈ Icc 0 totalTime` and is stated as `evalFrom_reverse`.
-/

namespace Motion

/-! ## Concatenation -/

namespace Profile

/-- Concatenate two profiles. -/
def append (p q : Profile) : Profile :=
  { start := p.start, segments := p.segments ++ q.segments }

@[simp] theorem totalTime_append (p q : Profile) :
    (p.append q).totalTime = p.totalTime + q.totalTime := by
  simp [Profile.totalTime, Profile.append, List.map_append, List.sum_append]

/-- Evaluation of a concatenation. The tail must be nonempty: with an empty `q` the
singleton extension of `p`'s last cubic is *not* the constant `q.start`, so the
statement would be false past `p.totalTime`. -/
theorem evalFrom_append (st qstart : State) (ss : List Segment) :
    ∀ (ts : List Segment) (t : ℝ), qstart = ss.foldl Segment.exit st → 0 ≤ t →
      ts ≠ [] →
      evalFrom st (ss ++ ts) t =
        if t < (ss.map Segment.dur).sum then evalFrom st ss t
        else evalFrom qstart ts (t - (ss.map Segment.dur).sum) := by
  induction ss generalizing st with
  | nil =>
      intro ts t h ht hne
      have hq : qstart = st := by simpa using h
      subst hq
      rw [List.nil_append, List.map_nil, List.sum_nil]
      rw [ite_eq_right (not_lt.mpr ht)]
      simp
  | cons s ss ih =>
      intro ts t h ht hne
      cases ss with
      | nil =>
          have hq : qstart = s.exit st := by simpa using h
          subst hq
          rw [List.singleton_append, evalFrom_cons_ne st s ts t hne]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            evalFrom.eq_2]
      | cons s' rest =>
          have h' : qstart = (s' :: rest).foldl Segment.exit (s.exit st) := by
            simpa using h
          rw [show s :: s' :: rest ++ ts = s :: ((s' :: rest) ++ ts) from rfl]
          rw [evalFrom_cons_ne st s ((s' :: rest) ++ ts) t (by simp)]
          have hsum : ((s :: s' :: rest).map Segment.dur).sum
              = s.dur + ((s' :: rest).map Segment.dur).sum := by simp
          rw [hsum]
          by_cases hlt : t < s.dur
          · rw [ite_eq_left hlt, ite_eq_left (by linarith [hsum, durations_nonneg (s' :: rest)])]
            rw [evalFrom_cons_ne st s (s' :: rest) t (by simp), ite_eq_left hlt]
          · rw [ite_eq_right hlt]
            have hIH := ih (s.exit st) ts (t - s.dur) h' (by linarith) hne
            rw [hIH]
            rw [evalFrom_cons_ne st s (s' :: rest) t (by simp), ite_eq_right hlt]
            by_cases hlt2 : t - s.dur < ((s' :: rest).map Segment.dur).sum
            · rw [ite_eq_left hlt2, ite_eq_left (by linarith)]
            · rw [ite_eq_right hlt2, ite_eq_right (by linarith)]
              congr 1
              ring

/-- Evaluation of a concatenation, in profile form. -/
theorem stateAt_append (p q : Profile) (t : ℝ) (h : q.start = p.endState)
    (hq : q.segments ≠ []) (ht : 0 ≤ t) :
    (p.append q).stateAt t =
      if t < p.totalTime then p.stateAt t else q.stateAt (t - p.totalTime) := by
  have h' : q.start = p.segments.foldl Segment.exit p.start := by
    simpa [Profile.endState] using h
  have key := evalFrom_append p.start q.start p.segments q.segments t h' ht hq
  change evalFrom p.start (p.segments ++ q.segments) t =
    if t < p.totalTime then p.stateAt t else q.stateAt (t - p.totalTime)
  rw [show p.totalTime = (p.segments.map Segment.dur).sum from rfl]
  rw [key]
  by_cases hlt : t < (p.segments.map Segment.dur).sum
  · rw [ite_eq_left hlt, ite_eq_left hlt]
    rfl
  · rw [ite_eq_right hlt, ite_eq_right hlt]
    rfl

/-- Concatenation of feasible profiles with matching junction state. -/
theorem feasible_append {p q : Profile} {lim : Limits}
    (h : q.start = p.endState) (hp : Feasible p lim) (hq : Feasible q lim) :
    Feasible (p.append q) lim := by
  obtain ⟨hpv, hpa, hpj⟩ := hp
  obtain ⟨hqv, hqa, hqj⟩ := hq
  cases hqs : q.segments with
  | nil =>
      have hpq : p.append q = p := by
        simp [Profile.append, hqs]
      rw [hpq]
      exact ⟨hpv, hpa, hpj⟩
  | cons s ss =>
      have hqne : q.segments ≠ [] := by simp [hqs]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        change |((p.append q).stateAt t).v| ≤ lim.vmax
        have hT : (p.append q).totalTime = p.totalTime + q.totalTime := totalTime_append p q
        rw [hT] at ht
        rw [stateAt_append p q t h hqne ht.1]
        by_cases hlt : t < p.totalTime
        · rw [ite_eq_left hlt]
          exact hpv t ⟨ht.1, le_of_lt hlt⟩
        · rw [ite_eq_right hlt]
          have ht' : t - p.totalTime ∈ Set.Icc 0 q.totalTime :=
            ⟨by linarith [ht.1], by linarith [ht.2]⟩
          simpa [Profile.v] using hqv (t - p.totalTime) ht'
      · intro t ht
        change |((p.append q).stateAt t).a| ≤ lim.amax
        have hT : (p.append q).totalTime = p.totalTime + q.totalTime := totalTime_append p q
        rw [hT] at ht
        rw [stateAt_append p q t h hqne ht.1]
        by_cases hlt : t < p.totalTime
        · rw [ite_eq_left hlt]
          exact hpa t ⟨ht.1, le_of_lt hlt⟩
        · rw [ite_eq_right hlt]
          have ht' : t - p.totalTime ∈ Set.Icc 0 q.totalTime :=
            ⟨by linarith [ht.1], by linarith [ht.2]⟩
          simpa [Profile.a] using hqa (t - p.totalTime) ht'
      · intro seg hseg hpos
        have hmem : seg ∈ p.segments ∨ seg ∈ q.segments := by
          simpa [Profile.append] using hseg
        rcases hmem with hmem | hmem
        · exact hpj seg hmem hpos
        · exact hqj seg hmem hpos

end Profile

/-! ## Transforms -/

/-- Time-reversal of a state: position and acceleration are kept, velocity is negated. -/
def revState (σ : State) : State :=
  { q := σ.q, v := -σ.v, a := σ.a }

/-- Time-reversal of a segment: the jerk is negated. -/
def revSeg (s : Segment) : Segment :=
  { s with jerk := -s.jerk }

namespace Segment

@[simp] theorem dur_revSeg (s : Segment) : (revSeg s).dur = s.dur := rfl

@[simp] theorem jerk_revSeg (s : Segment) : (revSeg s).jerk = -s.jerk := rfl

end Segment

/-- The start state of a mirrored profile: velocity and acceleration flip sign, position is
unchanged. -/
def mirrorState (σ : State) : State :=
  { σ with v := -σ.v, a := -σ.a }

/-- Reflection of a state through the position `q₀`: the position reflects about `q₀`, velocity
and acceleration flip sign. -/
def reflectState (q₀ : ℝ) (σ : State) : State :=
  { q := 2 * q₀ - σ.q, v := -σ.v, a := -σ.a }

namespace Profile

/-- Position translation. -/
def translate (d : ℝ) (p : Profile) : Profile :=
  { start := { p.start with q := p.start.q + d }, segments := p.segments }

/-- Reflection about the start position, matching the planner's `plan_rest_to_rest`: the start
position and the durations are kept, the start velocity and acceleration and every segment's
jerk flip sign. After the transform the trajectory is reflected about `p.start.q`, i.e. the
position at time `t` is `2 * p.start.q - p.q t`. -/
def mirror (p : Profile) : Profile :=
  { start := mirrorState p.start
    segments := p.segments.map revSeg }

/-- The scaled start state of a stretched profile. -/
def stretchState (k : ℝ) (σ : State) : State :=
  { q := σ.q, v := σ.v / k, a := σ.a / k^2 }

/-- A stretched segment. -/
def stretchSeg (k : ℝ) (hk : 0 < k) (s : Segment) : Segment :=
  { dur := s.dur * k
    dur_nonneg := mul_nonneg s.dur_nonneg (le_of_lt hk)
    jerk := s.jerk / k^3 }

@[simp] theorem dur_stretchSeg (k : ℝ) (hk : 0 < k) (s : Segment) :
    (stretchSeg k hk s).dur = s.dur * k := rfl

@[simp] theorem jerk_stretchSeg (k : ℝ) (hk : 0 < k) (s : Segment) :
    (stretchSeg k hk s).jerk = s.jerk / k^3 := rfl

/-- Time stretching by `k > 0`. -/
def stretch (k : ℝ) (hk : 0 < k) (p : Profile) : Profile :=
  { start := stretchState k p.start, segments := p.segments.map (stretchSeg k hk) }

/-- Time reversal. -/
def reverse (p : Profile) : Profile :=
  { start := revState p.endState
    segments := p.segments.reverse.map revSeg }

end Profile

namespace Segment

/-- The single-segment time-reversal identity. -/
theorem stateAt_rev (st : State) (s : Segment) (τ : ℝ) :
    (revSeg s).stateAt (revState (s.exit st)) (s.dur - τ) =
      revState (s.stateAt st τ) := by
  ext <;> simp [Segment.stateAt, Segment.exit, revSeg, revState] <;> ring

end Segment

theorem evalFrom_translate (st : State) (d : ℝ) (ss : List Segment) (t : ℝ) :
    evalFrom { st with q := st.q + d } ss t =
      { evalFrom st ss t with q := (evalFrom st ss t).q + d } := by
  revert t
  induction ss generalizing st with
  | nil =>
      intro t
      rfl
  | cons s ss ih =>
      intro t
      cases ss with
      | nil =>
          simp only [evalFrom.eq_2]
          ext <;> simp [Segment.stateAt]; ring
      | cons s' rest =>
          rw [evalFrom_cons_cons, evalFrom_cons_cons]
          by_cases h : t < s.dur
          · rw [ite_eq_left h, ite_eq_left h]
            ext <;> simp [Segment.stateAt]; ring
          · rw [ite_eq_right h, ite_eq_right h]
            have he : s.exit { st with q := st.q + d }
                = { s.exit st with q := (s.exit st).q + d } := by
              ext <;> simp [Segment.exit, Segment.stateAt]; ring
            rw [he]
            exact ih (s.exit st) (t - s.dur)

namespace Segment

/-- The single-segment mirror identity. -/
theorem stateAt_revSeg_mirror (st : State) (s : Segment) (τ : ℝ) :
    (revSeg s).stateAt (mirrorState st) τ = reflectState st.q (s.stateAt st τ) := by
  ext <;> simp [Segment.stateAt, revSeg, mirrorState, reflectState] <;> ring

/-- The mirrored segment's exit state is the reflected exit state. -/
theorem exit_revSeg_mirror (st : State) (s : Segment) :
    (revSeg s).exit (mirrorState st) = reflectState st.q (s.exit st) := by
  rw [Segment.exit, Segment.exit]
  exact stateAt_revSeg_mirror st s s.dur

end Segment

theorem evalFrom_mirror (st : State) (ss : List Segment) (t : ℝ) :
    evalFrom (mirrorState st) (ss.map revSeg) t = reflectState st.q (evalFrom st ss t) := by
  revert t
  induction ss generalizing st with
  | nil =>
      intro t
      change mirrorState st = reflectState st.q st
      ext <;> simp [mirrorState, reflectState]; ring
  | cons s ss ih =>
      intro t
      cases ss with
      | nil =>
          rw [List.map_cons, List.map_nil]
          simp only [evalFrom.eq_2]
          exact Segment.stateAt_revSeg_mirror st s t
      | cons s' rest =>
          rw [List.map_cons]
          rw [evalFrom_cons_ne (mirrorState st) (revSeg s) (List.map revSeg (s' :: rest)) t
            (by simp)]
          rw [evalFrom_cons_ne st s (s' :: rest) t (by simp)]
          have hdur : (revSeg s).dur = s.dur := rfl
          by_cases h : t < s.dur
          · rw [ite_eq_left (by simpa [hdur] using h), ite_eq_left h]
            exact Segment.stateAt_revSeg_mirror st s t
          · rw [ite_eq_right (by simpa [hdur] using h), ite_eq_right h]
            rw [hdur]
            rw [Segment.exit_revSeg_mirror]
            have hshift : reflectState st.q (s.exit st) =
                { mirrorState (s.exit st) with
                  q := (mirrorState (s.exit st)).q + (2 * (st.q - (s.exit st).q)) } := by
              ext <;> simp [reflectState, mirrorState]; ring
            rw [hshift, evalFrom_translate]
            rw [ih (s.exit st) (t - s.dur)]
            ext <;> simp [reflectState]; ring

namespace Profile

/-- The stretched state is the state of the stretched segment at the scaled time. -/
theorem stretchState_stateAt (k : ℝ) (hk : 0 < k) (st : State) (s : Segment) (τ : ℝ) :
    (stretchSeg k hk s).stateAt (stretchState k st) (k * τ) =
      stretchState k (s.stateAt st τ) := by
  ext <;> simp [Segment.stateAt, stretchSeg, stretchState] <;> field_simp

/-- The stretched segment's exit state is the stretched exit state. -/
theorem stretchState_exit (k : ℝ) (hk : 0 < k) (st : State) (s : Segment) :
    (stretchSeg k hk s).exit (stretchState k st) = stretchState k (s.exit st) := by
  rw [Segment.exit, Segment.exit]
  rw [dur_stretchSeg k hk s]
  rw [show s.dur * k = k * s.dur by ring]
  exact stretchState_stateAt k hk st s s.dur

end Profile

theorem evalFrom_stretch (k : ℝ) (hk : 0 < k) (st : State) (ss : List Segment) (t : ℝ) :
    evalFrom (Profile.stretchState k st) (ss.map (Profile.stretchSeg k hk)) (k * t) =
      Profile.stretchState k (evalFrom st ss t) := by
  revert t
  induction ss generalizing st with
  | nil =>
      intro t
      change Profile.stretchState k st = Profile.stretchState k st
      rfl
  | cons s ss ih =>
      intro t
      cases ss with
      | nil =>
          rw [List.map_cons, List.map_nil]
          simp only [evalFrom.eq_2]
          exact Profile.stretchState_stateAt k hk st s t
      | cons s' rest =>
          rw [List.map_cons]
          have hcond : k * t < (Profile.stretchSeg k hk s).dur ↔ t < s.dur := by
            rw [Profile.dur_stretchSeg k hk s]
            constructor <;> intro hh <;> nlinarith
          rw [evalFrom_cons_ne (Profile.stretchState k st) (Profile.stretchSeg k hk s)
            (List.map (Profile.stretchSeg k hk) (s' :: rest)) (k * t) (by simp)]
          rw [evalFrom_cons_ne st s (s' :: rest) t (by simp)]
          by_cases h : t < s.dur
          · rw [ite_eq_left (hcond.mpr h), ite_eq_left h]
            exact Profile.stretchState_stateAt k hk st s t
          · rw [ite_eq_right (fun hh => h (hcond.mp hh)), ite_eq_right h]
            rw [Profile.stretchState_exit k hk st s]
            rw [show k * t - (Profile.stretchSeg k hk s).dur = k * (t - s.dur) by
              rw [Profile.dur_stretchSeg k hk s]; ring]
            exact ih (s.exit st) (t - s.dur)

namespace Profile

theorem stateAt_translate (d : ℝ) (p : Profile) (t : ℝ) :
    (p.translate d).stateAt t = { p.stateAt t with q := (p.stateAt t).q + d } :=
  evalFrom_translate p.start d p.segments t

theorem stateAt_mirror (p : Profile) (t : ℝ) :
    p.mirror.stateAt t = reflectState p.start.q (p.stateAt t) :=
  evalFrom_mirror p.start p.segments t

theorem stateAt_stretch (k : ℝ) (hk : 0 < k) (p : Profile) (t : ℝ) :
    (p.stretch k hk).stateAt (k * t) = stretchState k (p.stateAt t) :=
  evalFrom_stretch k hk p.start p.segments t

theorem totalTime_stretch (k : ℝ) (hk : 0 < k) (p : Profile) :
    (p.stretch k hk).totalTime = k * p.totalTime := by
  unfold Profile.stretch Profile.totalTime
  rw [List.map_map]
  simp only [Function.comp_def, dur_stretchSeg]
  induction p.segments with
  | nil => simp
  | cons s ss ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem totalTime_mirror (p : Profile) : p.mirror.totalTime = p.totalTime := by
  unfold Profile.mirror Profile.totalTime
  rw [List.map_map]
  simp only [Function.comp_def, Segment.dur_revSeg]

theorem totalTime_translate (d : ℝ) (p : Profile) :
    (p.translate d).totalTime = p.totalTime := rfl

theorem totalTime_reverse (p : Profile) : p.reverse.totalTime = p.totalTime := by
  unfold Profile.reverse Profile.totalTime
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [List.map_reverse, List.sum_reverse]
  simp only [Segment.dur_revSeg]

theorem feasible_translate {p : Profile} {lim : Limits} (d : ℝ) (h : Feasible p lim) :
    Feasible (p.translate d) lim := by
  obtain ⟨hv, ha, hj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    change |((p.translate d).stateAt t).v| ≤ lim.vmax
    rw [stateAt_translate]
    have hb : |(p.stateAt t).v| ≤ lim.vmax := hv t ht
    simpa using hb
  · intro t ht
    change |((p.translate d).stateAt t).a| ≤ lim.amax
    rw [stateAt_translate]
    have hb : |(p.stateAt t).a| ≤ lim.amax := ha t ht
    simpa using hb
  · intro s hs hpos
    exact hj s (by simpa [Profile.translate] using hs) hpos

theorem feasible_mirror {p : Profile} {lim : Limits} (h : Feasible p lim) :
    Feasible p.mirror lim := by
  obtain ⟨hv, ha, hj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    change |(p.mirror.stateAt t).v| ≤ lim.vmax
    rw [stateAt_mirror]
    have ht' : t ∈ Set.Icc 0 p.totalTime := by
      simpa [Profile.totalTime_mirror] using ht
    have hb : |(p.stateAt t).v| ≤ lim.vmax := hv t ht'
    simpa [reflectState] using hb
  · intro t ht
    change |(p.mirror.stateAt t).a| ≤ lim.amax
    rw [stateAt_mirror]
    have ht' : t ∈ Set.Icc 0 p.totalTime := by
      simpa [Profile.totalTime_mirror] using ht
    have hb : |(p.stateAt t).a| ≤ lim.amax := ha t ht'
    simpa [reflectState] using hb
  · intro s hs hpos
    rcases List.mem_map.mp (by simpa [Profile.mirror] using hs) with ⟨s0, hs0, rfl⟩
    simpa [revSeg] using hj s0 hs0 hpos

theorem feasible_stretch {p : Profile} {lim : Limits} (k : ℝ) (hk : 0 < k)
    (hk1 : 1 ≤ k) (h : Feasible p lim) : Feasible (p.stretch k hk) lim := by
  obtain ⟨hv, ha, hj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    change |((p.stretch k hk).stateAt u).v| ≤ lim.vmax
    rw [← (show k * (u / k) = u by field_simp)]
    rw [stateAt_stretch]
    change |(p.stateAt (u / k)).v / k| ≤ lim.vmax
    have ht : u / k ∈ Set.Icc 0 p.totalTime := by
      constructor
      · exact div_nonneg hu.1 (le_of_lt hk)
      · have hT : (p.stretch k hk).totalTime = k * p.totalTime := totalTime_stretch k hk p
        rw [hT] at hu
        rw [div_le_iff₀ hk]
        linarith [hu.2]
    have hb : |(p.stateAt (u / k)).v| ≤ lim.vmax := hv (u / k) ht
    rw [abs_div, abs_of_pos hk]
    calc |(p.stateAt (u / k)).v| / k ≤ |(p.stateAt (u / k)).v| :=
          div_le_self (abs_nonneg _) hk1
      _ ≤ lim.vmax := hb
  · intro u hu
    change |((p.stretch k hk).stateAt u).a| ≤ lim.amax
    rw [← (show k * (u / k) = u by field_simp)]
    rw [stateAt_stretch]
    change |(p.stateAt (u / k)).a / k^2| ≤ lim.amax
    have ht : u / k ∈ Set.Icc 0 p.totalTime := by
      constructor
      · exact div_nonneg hu.1 (le_of_lt hk)
      · have hT : (p.stretch k hk).totalTime = k * p.totalTime := totalTime_stretch k hk p
        rw [hT] at hu
        rw [div_le_iff₀ hk]
        linarith [hu.2]
    have hb : |(p.stateAt (u / k)).a| ≤ lim.amax := ha (u / k) ht
    have hk2 : (1 : ℝ) ≤ k^2 := by nlinarith
    rw [abs_div, abs_of_pos (pow_pos hk 2)]
    calc |(p.stateAt (u / k)).a| / k^2 ≤ |(p.stateAt (u / k)).a| :=
          div_le_self (abs_nonneg _) hk2
      _ ≤ lim.amax := hb
  · intro s hs hpos
    rcases List.mem_map.mp (by simpa [Profile.stretch] using hs) with ⟨s0, hs0, rfl⟩
    have hpos' : 0 < s0.dur * k := hpos
    have hdur0 : 0 < s0.dur := pos_of_mul_pos_right (by linarith [hpos']) (le_of_lt hk)
    have hj0 := hj s0 hs0 hdur0
    have hk3 : (1 : ℝ) ≤ k^3 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hk1 3
    change |s0.jerk / k^3| ≤ lim.jmax
    rw [abs_div, abs_of_pos (pow_pos hk 3)]
    calc |s0.jerk| / k^3 ≤ |s0.jerk| := div_le_self (abs_nonneg _) hk3
      _ ≤ lim.jmax := hj0

end Profile

/-- The single-list time-reversal identity: reversing a chain and evaluating at `t` is the
same as evaluating the original at `totalTime - t` and reversing the resulting state. The
`t ∈ Icc 0 totalTime` hypothesis is needed because the singleton extension past the end of
the reversed chain does not match the original's extension before its start. -/
theorem evalFrom_reverse (st : State) (ss : List Segment) :
    ∀ t ∈ Set.Icc 0 (ss.map Segment.dur).sum,
      evalFrom (revState (ss.foldl Segment.exit st)) (ss.reverse.map revSeg) t =
        revState (evalFrom st ss ((ss.map Segment.dur).sum - t)) := by
  induction ss generalizing st with
  | nil =>
      intro t ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      rfl
  | cons s ss ih =>
      intro t ht
      set Tss := (ss.map Segment.dur).sum with hTss
      have hTss_nonneg : 0 ≤ Tss := durations_nonneg ss
      have hT : ((s :: ss).map Segment.dur).sum = s.dur + Tss := by simp [hTss]
      rw [hT] at ht ⊢
      have hfold : (s :: ss).foldl Segment.exit st = ss.foldl Segment.exit (s.exit st) := rfl
      have hrev : (s :: ss).reverse.map revSeg = ss.reverse.map revSeg ++ [revSeg s] := by
        rw [List.reverse_cons, List.map_append, List.map_singleton]
      have hsum_rev : ((ss.reverse.map revSeg).map Segment.dur).sum = Tss := by
        rw [List.map_map]
        simp only [Function.comp_def]
        rw [List.map_reverse, List.sum_reverse]
        rfl
      -- The reversed prefix ends at the time-reversed junction state.
      have hend : (ss.reverse.map revSeg).foldl Segment.exit
          (revState ((s :: ss).foldl Segment.exit st)) = revState (s.exit st) := by
        have h1 : evalFrom (revState ((s :: ss).foldl Segment.exit st))
            (ss.reverse.map revSeg) ((ss.reverse.map revSeg).map Segment.dur).sum
            = (ss.reverse.map revSeg).foldl Segment.exit
                (revState ((s :: ss).foldl Segment.exit st)) :=
          evalFrom_totalTime _ _
        rw [← h1, hsum_rev, hfold]
        have hIH := ih (s.exit st) Tss ⟨hTss_nonneg, le_rfl⟩
        rw [hIH, sub_self, evalFrom_zero]
      rw [hrev]
      rw [Profile.evalFrom_append (revState ((s :: ss).foldl Segment.exit st))
        (revState (s.exit st)) (ss.reverse.map revSeg) [revSeg s] t hend.symm ht.1 (by simp)]
      rw [hsum_rev]
      by_cases hlt : t < Tss
      · -- The original is in the later-segment branch.
        rw [ite_eq_left hlt]
        rw [hfold]
        have hIH := ih (s.exit st) t ⟨ht.1, le_of_lt hlt⟩
        rw [hIH]
        cases ss with
        | nil =>
            have hTss0 : Tss = 0 := by simp [hTss]
            linarith [ht.1, hlt, hTss0]
        | cons s' rest =>
            rw [evalFrom_cons_ne st s (s' :: rest) (s.dur + Tss - t) (by simp)]
            have hge : ¬ (s.dur + Tss - t < s.dur) := by linarith
            rw [ite_eq_right hge]
            congr 1
            ring_nf
      · -- The reversed profile is in its last segment.
        rw [ite_eq_right hlt]
        rw [evalFrom.eq_2]
        rw [show t - Tss = s.dur - (s.dur + Tss - t) by ring]
        rw [Segment.stateAt_rev]
        cases ss with
        | nil =>
            rw [evalFrom.eq_2]
        | cons s' rest =>
            rw [evalFrom_cons_ne st s (s' :: rest) (s.dur + Tss - t) (by simp)]
            by_cases hle : s.dur + Tss - t < s.dur
            · rw [ite_eq_left hle]
            · rw [ite_eq_right hle]
              have htT : t = Tss := by linarith [le_of_not_gt hle, ht.2]
              have hX : s.dur + Tss - t = s.dur := by rw [htT]; ring
              rw [hX]
              simp [Segment.exit]

namespace Profile

theorem stateAt_reverse (p : Profile) {t : ℝ} (ht : t ∈ Set.Icc 0 p.totalTime) :
    p.reverse.stateAt t =
      { q := (p.stateAt (p.totalTime - t)).q,
        v := -(p.stateAt (p.totalTime - t)).v,
        a := (p.stateAt (p.totalTime - t)).a } := by
  have h := evalFrom_reverse p.start p.segments t (by simpa [Profile.totalTime] using ht)
  simpa [Profile.reverse, Profile.stateAt, Profile.totalTime, Profile.endState, revState] using h

theorem feasible_reverse {p : Profile} {lim : Limits} (h : Feasible p lim) :
    Feasible p.reverse lim := by
  obtain ⟨hv, ha, hj⟩ := h
  have hT := totalTime_reverse p
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    change |(p.reverse.stateAt t).v| ≤ lim.vmax
    rw [hT] at ht
    rw [stateAt_reverse p ht]
    have ht' : p.totalTime - t ∈ Set.Icc 0 p.totalTime :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hb : |(p.stateAt (p.totalTime - t)).v| ≤ lim.vmax := hv (p.totalTime - t) ht'
    simpa using hb
  · intro t ht
    change |(p.reverse.stateAt t).a| ≤ lim.amax
    rw [hT] at ht
    rw [stateAt_reverse p ht]
    have ht' : p.totalTime - t ∈ Set.Icc 0 p.totalTime :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hb : |(p.stateAt (p.totalTime - t)).a| ≤ lim.amax := ha (p.totalTime - t) ht'
    simpa using hb
  · intro s hs hpos
    rcases List.mem_map.mp (by simpa [Profile.reverse] using hs) with ⟨s0, hs0, rfl⟩
    simpa [revSeg] using hj s0 hs0 hpos

end Profile

end Motion
