module
public import Motion.Transforms
public import Motion.General
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

noncomputable section

@[expose] public section

/-!
# Motion: stretching and synchronisation

M3 of `docs/motion_control.md` §4.4: the rest-to-rest predicate `IsRest`, the
common-duration bundle `JointProfile`, and the construction that stretches every joint
profile to the common maximum duration, with a constant hold for zero-motion joints.

The M3 table's `stretch_feasible`, `stretch_totalTime` and `stateAt_stretch` are the
existing `Profile.feasible_stretch`, `Profile.totalTime_stretch` and
`Profile.stateAt_stretch` of `Motion.Transforms`; they are not duplicated here.
`Profile.stretch_isRest` is added because `stretchTo_isRest` consumes it.

The two branches of `stretchTo` are the design's: a profile with zero total time is held
at its start position for the common duration, and every other profile is stretched by
the factor `T / p.totalTime ≥ 1`.
-/

namespace Motion

/-- A rest-to-rest boundary predicate. -/
def IsRest (p : Profile) : Prop :=
  p.start.v = 0 ∧ p.start.a = 0 ∧ p.endState.v = 0 ∧ p.endState.a = 0

/-- A common-duration bundle of joint profiles. -/
structure JointProfile (n : ℕ) where
  profiles : Fin n → Profile
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  same_duration : ∀ i, (profiles i).totalTime = duration

/-- A constant zero-jerk profile of duration `T` at position `q`. -/
def hold (q T : ℝ) (hT : 0 ≤ T) : Profile :=
  { start := { q := q, v := 0, a := 0 },
    segments := [{ dur := T, dur_nonneg := hT, jerk := 0 }] }

theorem hold_start (q T : ℝ) (hT : 0 ≤ T) :
    (hold q T hT).start = { q := q, v := 0, a := 0 } := rfl

theorem hold_totalTime (q T : ℝ) (hT : 0 ≤ T) : (hold q T hT).totalTime = T := by
  simp [hold, Profile.totalTime]

theorem hold_endState (q T : ℝ) (hT : 0 ≤ T) :
    (hold q T hT).endState = { q := q, v := 0, a := 0 } := by
  simp [hold, Profile.endState, Segment.exit, Segment.stateAt]

/-- A hold's state is its start state at every time. -/
theorem hold_stateAt (q T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    (hold q T hT).stateAt t = { q := q, v := 0, a := 0 } := by
  show Segment.stateAt { q := q, v := 0, a := 0 }
    { dur := T, dur_nonneg := hT, jerk := 0 } t = { q := q, v := 0, a := 0 }
  simp [Segment.stateAt]

theorem hold_feasible (q T : ℝ) (hT : 0 ≤ T) (lim : Limits) :
    Feasible (hold q T hT) lim := by
  apply feasible_of_safeFrom
  simp [SafeFrom, SegmentSafe, hold, Segment.exit, Segment.stateAt,
    lim.vmax_pos.le, lim.amax_pos.le, lim.jmax_pos.le]

theorem hold_isRest (q T : ℝ) (hT : 0 ≤ T) : IsRest (hold q T hT) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hold, Profile.endState, Segment.exit, Segment.stateAt]

namespace Profile

/-- Total times are nonnegative. -/
theorem totalTime_nonneg (p : Profile) : 0 ≤ p.totalTime :=
  durations_nonneg p.segments

/-- A chain whose durations sum to zero folds to its start state: every duration is zero,
so every segment's exit is the identity. -/
private theorem foldl_exit_eq_of_sum_eq_zero (st : State) (ss : List Segment)
    (h : (ss.map Segment.dur).sum = 0) : ss.foldl Segment.exit st = st := by
  induction ss generalizing st with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.map_cons, List.sum_cons] at h
      have hs : s.dur = 0 := by
        have h1 : 0 ≤ s.dur := s.dur_nonneg
        have h2 : 0 ≤ (ss.map Segment.dur).sum := durations_nonneg ss
        linarith
      have hss : (ss.map Segment.dur).sum = 0 := by
        have h2 : 0 ≤ (ss.map Segment.dur).sum := durations_nonneg ss
        linarith
      rw [List.foldl_cons, Segment.exit_of_dur_eq_zero hs, ih st hss]

/-- A zero-total-time profile ends where it starts. -/
theorem endState_eq_start_of_totalTime_eq_zero (p : Profile) (h : p.totalTime = 0) :
    p.endState = p.start :=
  foldl_exit_eq_of_sum_eq_zero p.start p.segments h

/-- The stretched profile's end state is the stretched end state. -/
theorem stretch_endState (k : ℝ) (hk : 0 < k) (p : Profile) :
    (p.stretch k hk).endState = Profile.stretchState k p.endState := by
  rw [← Profile.stateAt_totalTime (p.stretch k hk), Profile.totalTime_stretch,
    Profile.stateAt_stretch, Profile.stateAt_totalTime]

/-- Stretching preserves the rest boundary conditions. -/
theorem stretch_isRest {p : Profile} (k : ℝ) (hk : 0 < k) (h : IsRest p) :
    IsRest (p.stretch k hk) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Profile.stretch, Profile.stretchState, h1]
  · simp [Profile.stretch, Profile.stretchState, h2]
  · rw [Profile.stretch_endState]
    simp [Profile.stretchState, h3]
  · rw [Profile.stretch_endState]
    simp [Profile.stretchState, h4]

end Profile

/-- The common maximum duration; `foldr max 0` handles `n = 0`. -/
noncomputable def syncTime {n : ℕ} (p : Fin n → Profile) : ℝ :=
  (List.ofFn fun i => (p i).totalTime).foldr max 0

/-- Every member of a list is at most the list's `foldr max 0`. -/
private theorem le_foldr_max_of_mem {l : List ℝ} {x : ℝ} (h : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · rw [heq]
        exact le_max_left a _
      · exact le_trans (ih hmem) (le_max_right a _)

/-- A list's `foldr max 0` is nonnegative, because of the seed. -/
private theorem foldr_max_nonneg (l : List ℝ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => exact le_refl 0
  | cons a l ih =>
      rw [List.foldr_cons]
      exact le_trans ih (le_max_right a _)

/-- A list all of whose members are zero folds, under `max`, to zero. -/
private theorem foldr_max_eq_zero {l : List ℝ} (h : ∀ x ∈ l, x = 0) :
    l.foldr max 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldr_cons, h a (by simp)]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
      simp

theorem syncTime_nonneg {n : ℕ} (p : Fin n → Profile) : 0 ≤ syncTime p :=
  foldr_max_nonneg _

theorem totalTime_le_syncTime {n : ℕ} (p : Fin n → Profile) (i : Fin n) :
    (p i).totalTime ≤ syncTime p :=
  le_foldr_max_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- Stretch `p` to duration `T ≥ p.totalTime`; a zero-duration profile is held. -/
noncomputable def stretchTo (T : ℝ) (p : Profile) (hT : 0 ≤ T)
    (hle : p.totalTime ≤ T) : Profile :=
  if h0 : p.totalTime = 0 then hold p.start.q T hT
  else
    have hp : 0 < p.totalTime := lt_of_le_of_ne (Profile.totalTime_nonneg p) (Ne.symm h0)
    have hTpos : 0 < T := lt_of_lt_of_le hp hle
    Profile.stretch (T / p.totalTime) (div_pos hTpos hp) p

theorem stretchTo_totalTime (T : ℝ) (p : Profile) (hT : 0 ≤ T) (hle : p.totalTime ≤ T) :
    (stretchTo T p hT hle).totalTime = T := by
  unfold stretchTo
  split
  · exact hold_totalTime p.start.q T hT
  · rename_i h0
    rw [Profile.totalTime_stretch, div_mul_cancel₀ T h0]

theorem stretchTo_feasible (T : ℝ) (p : Profile) (hT : 0 ≤ T) (hle : p.totalTime ≤ T)
    {lim : Limits} (h : Feasible p lim) : Feasible (stretchTo T p hT hle) lim := by
  unfold stretchTo
  split
  · exact hold_feasible p.start.q T hT lim
  · rename_i h0
    have hp : 0 < p.totalTime :=
      lt_of_le_of_ne (Profile.totalTime_nonneg p) (Ne.symm h0)
    have hk : 0 < T / p.totalTime := div_pos (lt_of_lt_of_le hp hle) hp
    have hk1 : 1 ≤ T / p.totalTime := by
      rw [le_div_iff₀ hp]
      simpa using hle
    exact Profile.feasible_stretch (T / p.totalTime) hk hk1 h

theorem stretchTo_isRest (T : ℝ) (p : Profile) (hT : 0 ≤ T) (hle : p.totalTime ≤ T)
    (h : IsRest p) : IsRest (stretchTo T p hT hle) := by
  unfold stretchTo
  split
  · exact hold_isRest p.start.q T hT
  · rename_i h0
    have hp : 0 < p.totalTime :=
      lt_of_le_of_ne (Profile.totalTime_nonneg p) (Ne.symm h0)
    have hk : 0 < T / p.totalTime := div_pos (lt_of_lt_of_le hp hle) hp
    exact Profile.stretch_isRest (T / p.totalTime) hk h

theorem stretchTo_endpoints (T : ℝ) (p : Profile) (hT : 0 ≤ T) (hle : p.totalTime ≤ T) :
    (stretchTo T p hT hle).start.q = p.start.q ∧
    (stretchTo T p hT hle).endState.q = p.endState.q := by
  unfold stretchTo
  split
  · rename_i h0
    refine ⟨rfl, ?_⟩
    rw [hold_endState, Profile.endState_eq_start_of_totalTime_eq_zero p h0]
  · rename_i h0
    have hp : 0 < p.totalTime :=
      lt_of_le_of_ne (Profile.totalTime_nonneg p) (Ne.symm h0)
    have hk : 0 < T / p.totalTime := div_pos (lt_of_lt_of_le hp hle) hp
    exact ⟨rfl, by rw [Profile.stretch_endState]; simp [Profile.stretchState]⟩

noncomputable def synchronize {n : ℕ} (p : Fin n → Profile) : JointProfile n :=
  { profiles := fun i =>
      stretchTo (syncTime p) (p i) (syncTime_nonneg p) (totalTime_le_syncTime p i)
    duration := syncTime p
    duration_nonneg := syncTime_nonneg p
    same_duration := fun i =>
      stretchTo_totalTime (syncTime p) (p i) (syncTime_nonneg p) (totalTime_le_syncTime p i) }

theorem synchronize_feasible {n : ℕ} {p : Fin n → Profile} {lim : Fin n → Limits}
    (h : ∀ i, Feasible (p i) (lim i)) :
    ∀ i, Feasible ((synchronize p).profiles i) (lim i) := by
  intro i
  exact stretchTo_feasible (syncTime p) (p i) (syncTime_nonneg p)
    (totalTime_le_syncTime p i) (h i)

theorem synchronize_isRest {n : ℕ} {p : Fin n → Profile}
    (h : ∀ i, IsRest (p i)) : ∀ i, IsRest ((synchronize p).profiles i) := by
  intro i
  exact stretchTo_isRest (syncTime p) (p i) (syncTime_nonneg p)
    (totalTime_le_syncTime p i) (h i)

theorem synchronize_totalTime {n : ℕ} (p : Fin n → Profile) (i : Fin n) :
    ((synchronize p).profiles i).totalTime = (synchronize p).duration :=
  (synchronize p).same_duration i

set_option linter.unusedVariables false in
theorem synchronize_endpoints {n : ℕ} {p : Fin n → Profile}
    (h : ∀ i, IsRest (p i)) (i : Fin n) :
    ((synchronize p).profiles i).start.q = (p i).start.q ∧
    ((synchronize p).profiles i).endState.q = (p i).endState.q :=
  stretchTo_endpoints (syncTime p) (p i) (syncTime_nonneg p) (totalTime_le_syncTime p i)

theorem synchronize_rest_to_rest {n : ℕ} {p : Fin n → Profile}
    (h : ∀ i, IsRest (p i)) (i : Fin n) :
    ((synchronize p).profiles i).start.v = 0 ∧ ((synchronize p).profiles i).start.a = 0 ∧
    ((synchronize p).profiles i).endState.v = 0 ∧ ((synchronize p).profiles i).endState.a = 0 :=
  synchronize_isRest h i

theorem synchronize_zero_motion {n : ℕ} {p : Fin n → Profile} (i : Fin n)
    (h0 : (p i).totalTime = 0) :
    (synchronize p).profiles i = hold (p i).start.q (syncTime p) (syncTime_nonneg p) := by
  show stretchTo (syncTime p) (p i) (syncTime_nonneg p) (totalTime_le_syncTime p i) = _
  unfold stretchTo
  rw [dite_eq_left h0]

theorem synchronize_all_zero {n : ℕ} {p : Fin n → Profile}
    (h0 : ∀ i, (p i).totalTime = 0) :
    syncTime p = 0 ∧ (synchronize p).duration = 0 ∧
      ∀ i (t : ℝ), ((synchronize p).profiles i).q t = (p i).start.q := by
  have hsync : syncTime p = 0 := by
    unfold syncTime
    apply foldr_max_eq_zero
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    exact hi.symm.trans (h0 i)
  refine ⟨hsync, hsync, ?_⟩
  intro i t
  rw [synchronize_zero_motion i (h0 i), Profile.q,
    hold_stateAt (p i).start.q (syncTime p) (syncTime_nonneg p) t]

/-! ## Synchronised stop

The supervisor's re-plan from motion: brake every joint to rest with `stopProfile`, then
hold each joint until the common maximum stop duration. Unlike `synchronize`, the
per-joint stop profiles are not stretched, so their start states are the measured states.
-/

/-- For each measured state, brake to rest with `stopProfile`, then hold until the common
maximum stop duration. The per-joint profiles are not stretched, so their start states are
the measured states. -/
noncomputable def synchronizedStop {n : ℕ} (s : Fin n → State) (lim : Fin n → Limits) :
    JointProfile n :=
  let p : Fin n → Profile := fun i => stopProfile (s i) (lim i)
  { profiles := fun i =>
      (p i).append (hold (p i).endState.q
        (syncTime p - (p i).totalTime)
        (sub_nonneg.mpr (totalTime_le_syncTime p i)))
    duration := syncTime p
    duration_nonneg := syncTime_nonneg p
    same_duration := fun i => by
      rw [Profile.totalTime_append, hold_totalTime]
      ring }

/-- The per-joint shape of `synchronizedStop`, with the internal `let` unfolded. -/
private theorem synchronizedStop_profiles {n : ℕ} (s : Fin n → State)
    (lim : Fin n → Limits) (i : Fin n) :
    (synchronizedStop s lim).profiles i =
      (stopProfile (s i) (lim i)).append
        (hold ((stopProfile (s i) (lim i)).endState.q)
          (syncTime (fun j => stopProfile (s j) (lim j)) - (stopProfile (s i) (lim i)).totalTime)
          (sub_nonneg.mpr
            (totalTime_le_syncTime (fun j => stopProfile (s j) (lim j)) i))) :=
  rfl

theorem synchronizedStop_totalTime {n : ℕ} (s : Fin n → State) (lim : Fin n → Limits)
    (i : Fin n) :
    ((synchronizedStop s lim).profiles i).totalTime = (synchronizedStop s lim).duration :=
  (synchronizedStop s lim).same_duration i

theorem synchronizedStop_rest_at_Tmax {n : ℕ} (s : Fin n → State) (lim : Fin n → Limits)
    (h : ∀ i, stopFeasible (s i) (lim i)) (i : Fin n) :
    ((synchronizedStop s lim).profiles i).endState.v = 0 ∧
    ((synchronizedStop s lim).profiles i).endState.a = 0 := by
  rw [synchronizedStop_profiles]
  have hrest := stopProfile_ends_at_rest (s i) (lim i) (h i)
  have hstart : (hold ((stopProfile (s i) (lim i)).endState.q)
      (syncTime (fun j => stopProfile (s j) (lim j)) - (stopProfile (s i) (lim i)).totalTime)
      (sub_nonneg.mpr
        (totalTime_le_syncTime (fun j => stopProfile (s j) (lim j)) i))).start =
      (stopProfile (s i) (lim i)).endState := by
    rw [hold_start]
    ext <;> simp [hrest.1, hrest.2]
  rw [endState_append_eq hstart.symm, hold_endState]
  exact ⟨rfl, rfl⟩

theorem synchronizedStop_feasible {n : ℕ} {s : Fin n → State} {lim : Fin n → Limits}
    (h : ∀ i, stopFeasible (s i) (lim i)) (i : Fin n) :
    Feasible ((synchronizedStop s lim).profiles i) (lim i) := by
  rw [synchronizedStop_profiles]
  have hrest := stopProfile_ends_at_rest (s i) (lim i) (h i)
  have hstart : (hold ((stopProfile (s i) (lim i)).endState.q)
      (syncTime (fun j => stopProfile (s j) (lim j)) - (stopProfile (s i) (lim i)).totalTime)
      (sub_nonneg.mpr
        (totalTime_le_syncTime (fun j => stopProfile (s j) (lim j)) i))).start =
      (stopProfile (s i) (lim i)).endState := by
    rw [hold_start]
    ext <;> simp [hrest.1, hrest.2]
  exact Profile.feasible_append hstart
    (stopProfile_feasible (s i) (lim i) (h i))
    (hold_feasible _ _ _ (lim i))

theorem synchronizedStop_start {n : ℕ} {s : Fin n → State} {lim : Fin n → Limits}
    (i : Fin n) :
    ((synchronizedStop s lim).profiles i).start = s i := by
  rw [synchronizedStop_profiles]
  exact stopProfile_start (s i) (lim i)

end Motion
