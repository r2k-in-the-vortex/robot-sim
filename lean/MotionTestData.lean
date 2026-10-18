module
/-
# Exact ground-truth data for the motion controllers

`Motion.lean` is the specification of the jerk-limited motion controller. This file
evaluates that specification over `ℚ` and writes the results out as JSON for the Rust
implementation to be checked against.

Every number here is exact. The polynomial layer - `State`, `Segment`, `Profile`, cubic
evaluation, stretch and synchronisation - is restated at `ℚ`, and the conservative planner
of `docs/motion_control.md` §3.8 is restated exactly: it uses only `min`, comparison,
multiplication and division, never `sqrt` or `cbrt`. The optimal 7-phase cases are not
computed by a planner here; they are constructed from rational shapes (a rational `t_j`,
`t_a`, `t_c`, `t_r` or `v_p`) so that the emitted durations and jerks are exact, and each
case re-derives its defining equation before the file is written.

The optimal planner of §3.3 needs radicals. This generator never calls them: it chooses
perfect squares and cubes, so the planner's roots are rational witnesses, and the
defining equations (`2Jt_r³ = D`, `v_p²/A + v_p t_j = D`, `V = A(t_j+t_a)`,
`V = J t_r²`) are checked exactly.

Every case is re-checked by evaluation before anything is written - endpoints, rest
boundaries, phase-start advance identities, per-segment endpoint bounds, constant
acceleration sign within each segment, the jerk bound, the case-defining equation and the
exact maxima (acceleration is linear on a segment, jerk is constant, and velocity is
quadratic with its vertex at `-a₀/j`). The generator refuses to write a file if a check
fails.

Regenerate the data with, from `lean/`:

    lake exe motion_test_data ../test_data/motion_profiles.json

`Motion` is imported so the generator re-elaborates whenever the specification changes,
even though the rational definitions below are a restatement rather than an
instantiation. The mirror is held to the specification by reading and by the invariants
each case re-derives, exactly as `KinematicsTestData.lean` documents for the forward
chain.
-/

public import Lean.Data.Json.Basic
public import Lean.Data.Json.Printer
public import Mathlib.Algebra.Field.Rat
public import Motion

open Lean (Json)

@[expose] public section

namespace MotionTestData

/-! ## The polynomial layer over `ℚ` -/

/-- `|x|`, written out so the file needs no `Abs` instance. -/
def qabs (x : ℚ) : ℚ := if x < 0 then -x else x

/-- `min`, written out so the file needs no `Min` instance. -/
def qmin (x y : ℚ) : ℚ := if x ≤ y then x else y

/-- `max`, written out so the file needs no `Max` instance. -/
def qmax (x y : ℚ) : ℚ := if x ≤ y then y else x

/-- A joint state: position, velocity, acceleration. -/
structure State where
  q : ℚ
  v : ℚ
  a : ℚ
deriving DecidableEq, Repr

/-- One constant-jerk segment. -/
structure Segment where
  dur : ℚ
  jerk : ℚ
deriving DecidableEq, Repr

/-- A start state plus a list of cubic segments. -/
structure Profile where
  start : State
  segments : List Segment
deriving DecidableEq, Repr

/-- Symmetric kinematic limits. -/
structure Limits where
  vmax : ℚ
  amax : ℚ
  jmax : ℚ
deriving DecidableEq, Repr

def limitsOf (vmax amax jmax : ℚ) : Limits := ⟨vmax, amax, jmax⟩

/-- The state on a segment of local time `τ`: the specification's `Segment.stateAt`. -/
def Segment.stateAt (s : Segment) (st : State) (τ : ℚ) : State :=
  { q := st.q + st.v * τ + st.a * τ ^ 2 / 2 + s.jerk * τ ^ 3 / 6
    v := st.v + st.a * τ + s.jerk * τ ^ 2 / 2
    a := st.a + s.jerk * τ }

/-- The segment's exit state. -/
def Segment.exit (s : Segment) (st : State) : State := s.stateAt st s.dur

/-- Total time: the sum of the durations. -/
def Profile.totalTime (p : Profile) : ℚ :=
  p.segments.foldl (fun acc s => acc + s.dur) 0

/-- The end state, obtained by advancing through the segments. -/
def Profile.endState (p : Profile) : State :=
  p.segments.foldl (fun st s => s.exit st) p.start

/-- The entry state of each segment, in order (one entry per segment). -/
def Profile.phaseStarts (p : Profile) : List State :=
  let rec go (st : State) : List Segment → List State
    | [] => []
    | s :: ss => st :: go (s.exit st) ss
  go p.start p.segments

/-- The cumulative boundary times `0, t₁, t₁+t₂, …, T`, one more entry than segments. -/
def Profile.cumulativeTimes (p : Profile) : List ℚ :=
  let rec go (t : ℚ) : List Segment → List ℚ
    | [] => [t]
    | s :: ss => t :: go (t + s.dur) ss
  go 0 p.segments

/-- The specification's `evalFrom`: extend the last cubic, and at an internal boundary
select the later segment (`if t < s.dur`). -/
def evalFrom (st : State) : List Segment → ℚ → State
  | [], _ => st
  | [s], t => s.stateAt st t
  | s :: ss, t =>
      if t < s.dur then s.stateAt st t
      else evalFrom (s.exit st) ss (t - s.dur)

/-- Rust's `Profile::eval`: clamp to `[0, totalTime]`, later segment at a boundary. -/
def Profile.eval (p : Profile) (t : ℚ) : State :=
  if t ≤ 0 then p.start
  else if t ≥ p.totalTime then p.endState
  else evalFrom p.start p.segments t

/-- Affine time stretch: `q(t) ↦ q(t/k)`. Durations are multiplied by `k`, jerks divided
by `k³`, and the start velocity and acceleration by `k` and `k²`. -/
def Profile.stretch (k : ℚ) (p : Profile) : Profile :=
  { start := { q := p.start.q, v := p.start.v / k, a := p.start.a / (k * k) }
    segments := p.segments.map fun s =>
      { dur := s.dur * k, jerk := s.jerk / (k * k * k) } }

/-! ## Conservative planner (§3.8), exactly -/

/-- `+1` for a nonnegative displacement, `-1` otherwise. -/
def signOf (x : ℚ) : ℚ := if x < 0 then -1 else 1

/-- The conservative rational template: `τ = min 1 (min (A/J) (V/J))`,
`Δmin = 2Jτ³`; for `D ≥ Δmin`, `j = J`, `τc = (D−Δmin)/(Jτ²)`; otherwise
`j = D/(2τ³)`, `τc = 0`; durations `(τ,0,τ,τc,τ,0,τ)`, jerks
`(s·j,0,−s·j,0,−s·j,0,s·j)`. `D = 0` returns the empty profile. -/
def planConservative (q0 q1 : ℚ) (lim : Limits) : Profile :=
  let start : State := ⟨q0, 0, 0⟩
  let delta := q1 - q0
  if delta = 0 then
    { start := start, segments := [] }
  else
    let d := qabs delta
    let tau := qmin 1 (qmin (lim.amax / lim.jmax) (lim.vmax / lim.jmax))
    let dmin := 2 * lim.jmax * tau ^ 3
    let j := if d ≥ dmin then lim.jmax else d / (2 * tau ^ 3)
    let tc := if d ≥ dmin then (d - dmin) / (lim.jmax * tau ^ 2) else 0
    let s := signOf delta
    { start := start
      segments := [
        ⟨tau, s * j⟩, ⟨0, 0⟩, ⟨tau, -(s * j)⟩, ⟨tc, 0⟩,
        ⟨tau, -(s * j)⟩, ⟨0, 0⟩, ⟨tau, s * j⟩] }

/-- The uniform 7-slot jerk list `(+J, 0, −J, 0, −J, 0, +J)` multiplied by the
displacement sign, zipped with a duration list. -/
def sevenSegments (J s : ℚ) (durations : List ℚ) : List Segment :=
  (durations.zip [J, 0, -J, 0, -J, 0, J]).map fun (d, j) =>
    { dur := d, jerk := s * j }

/-! ## Cases -/

/-- How a case's expected data is held to its definition. -/
inductive Defining where
  /-- The empty profile at one position. -/
  | zeroMotion
  /-- The conservative template of §3.8. -/
  | conservative
  /-- Case A with `A` reached: `V = A(t_j+t_a)`, `D = V(2t_j+t_a+t_c)`. -/
  | cruiseReached (tj ta tc : ℚ)
  /-- Case A triangular: `V = Jt_r²`, `D = 2Vt_r + Vt_c`. -/
  | cruiseTriangular (tr tc : ℚ)
  /-- Case B: `v_p = A(t_j+t_a)`, `D = v_p²/A + v_p t_j`. -/
  | peakNoCruise (tj ta vp : ℚ)
  /-- Case C: `D = 2Jt_r³`. -/
  | triangular (tr : ℚ)
  /-- A general stop-move-start case with rational triangular brake witnesses. -/
  | general (tr0 tr1 : ℚ)
deriving Repr

/-- One accepted ground-truth case. -/
structure Case where
  name : String
  /-- `conservative`, `optimal` or `general`. -/
  mode : String
  /-- `zero_motion`, `conservative`, `cruise`, `peak_no_cruise`, `triangular`, `general`. -/
  kind : String
  threshold : Bool
  limits : Limits
  start : State
  goal : State
  segments : List Segment
  defining : Defining
  /-- Whether both endpoints are rest states (`v = a = 0`). -/
  restEnds : Bool := true
deriving Repr

/-- Build an optimal case from a positive-displacement shape: the sign of `q1 - q0`
multiplies every jerk. The start is a rest state. -/
def optimalCase (name kind : String) (threshold : Bool) (lim : Limits)
    (q0 q1 : ℚ) (durations : List ℚ) (defining : Defining) : Case :=
  { name := name
    mode := "optimal"
    kind := kind
    threshold := threshold
    limits := lim
    start := ⟨q0, 0, 0⟩
    goal := ⟨q1, 0, 0⟩
    segments := sevenSegments lim.jmax (signOf (q1 - q0)) durations
    defining := defining }

/-- Case A, `A` reached, with cruise. -/
def caseACruise : Case :=
  let A : ℚ := 4
  let J : ℚ := 2
  let ta : ℚ := 5 / 4
  let tc : ℚ := 1
  let tj := A / J
  let V := A * (tj + ta)
  let D := V * (2 * tj + ta + tc)
  optimalCase "optimal_case_a_full_cruise" "cruise" false (limitsOf V A J) 0 D
    [tj, ta, tj, tc, tj, ta, tj] (.cruiseReached tj ta tc)

/-- Case A with a triangular acceleration ramp and a cruise: `V = Jt_r² < A²/J`. -/
def caseATriangular : Case :=
  let A : ℚ := 2
  let J : ℚ := 4
  let tr : ℚ := 1 / 4
  let tc : ℚ := 1 / 2
  let V := J * tr ^ 2
  let D := 2 * V * tr + V * tc
  optimalCase "optimal_case_a_triangular_cruise" "cruise" false (limitsOf V A J) 0 D
    [tr, 0, tr, tc, tr, 0, tr] (.cruiseTriangular tr tc)

/-- Case B, peak velocity without cruise. `neg` mirrors the case. -/
def caseB (name : String) (A J ta V : ℚ) (q0 : ℚ) (neg : Bool) : Case :=
  let tj := A / J
  let vp := A * (tj + ta)
  let D := vp ^ 2 / A + vp * tj
  let q1 := if neg then q0 - D else q0 + D
  optimalCase name "peak_no_cruise" false (limitsOf V A J) q0 q1
    [tj, ta, tj, 0, tj, ta, tj] (.peakNoCruise tj ta vp)

/-- Case C, pure triangular, no cruise. -/
def caseC (name : String) (A J V tr : ℚ) (q0 : ℚ) : Case :=
  let D := 2 * J * tr ^ 3
  optimalCase name "triangular" false (limitsOf V A J) q0 (q0 + D)
    [tr, 0, tr, 0, tr, 0, tr] (.triangular tr)

/-- Case D: zero displacement, the empty profile. -/
def caseZeroMotion : Case :=
  { name := "optimal_zero_motion"
    mode := "optimal"
    kind := "zero_motion"
    threshold := false
    limits := limitsOf 3 2 4
    start := ⟨5 / 2, 0, 0⟩
    goal := ⟨5 / 2, 0, 0⟩
    segments := []
    defining := .zeroMotion }

/-- The `V = v_A` threshold: `A = 2`, `J = 4`, `V = 1`, `D = 1`, all dyadic. -/
def caseThresholdVeqVA : Case :=
  optimalCase "optimal_v_eq_va_threshold" "cruise" true (limitsOf 1 2 4) 0 1
    [1 / 2, 0, 1 / 2, 0, 1 / 2, 0, 1 / 2] (.cruiseReached (1 / 2) 0 0)

/-- The `D = D_full(V)` boundary: cruise duration zero. -/
def caseThresholdAB : Case :=
  optimalCase "optimal_a_boundary_no_cruise" "cruise" true (limitsOf 3 2 4) 0 6
    [1 / 2, 1, 1 / 2, 0, 1 / 2, 1, 1 / 2] (.cruiseReached (1 / 2) 1 0)

/-- The `D = 2A³/J²` boundary: Case B with `t_a = 0`. -/
def caseThresholdBC : Case :=
  optimalCase "optimal_bc_boundary_peak" "peak_no_cruise" true (limitsOf 3 2 4) 0 1
    [1 / 2, 0, 1 / 2, 0, 1 / 2, 0, 1 / 2] (.peakNoCruise (1 / 2) 0 1)

/-- A conservative case: the template applied to `q0 → q1`. -/
def conservativeCase (name : String) (q0 q1 : ℚ) (lim : Limits) : Case :=
  let p := planConservative q0 q1 lim
  { name := name
    mode := "conservative"
    kind := "conservative"
    threshold := false
    limits := lim
    start := p.start
    goal := p.endState
    segments := p.segments
    defining := .conservative }

/-- A general stop-move-start case with rational triangular brakes:
`v₀ = v₁ = Jt_r² = 1/4`, `J = 4`, `t_r = 1/4`, so both brakes are exact, and the
conservative middle displacement is `1`. -/
def caseGeneral : Case :=
  let lim := limitsOf 3 2 4
  let J : ℚ := 4
  let tr : ℚ := 1 / 4
  let q0 : ℚ := 0
  let q1 : ℚ := 9 / 8
  let v := J * tr ^ 2
  let stop : List Segment := [{ dur := tr, jerk := -J }, { dur := tr, jerk := J }]
  let startSegs : List Segment := [{ dur := tr, jerk := J }, { dur := tr, jerk := -J }]
  let mid := planConservative (q0 + J * tr ^ 3) (q1 - J * tr ^ 3) lim
  { name := "general_accept_stop_move_start"
    mode := "general"
    kind := "general"
    threshold := false
    limits := lim
    start := ⟨q0, v, 0⟩
    goal := ⟨q1, v, 0⟩
    segments := stop ++ mid.segments ++ startSegs
    defining := .general tr tr
    restEnds := false }

/-- The accepted cases. All four M1 kinds, both displacement signs, the exact case
boundaries, and one general stop-move-start move. -/
def cases : List Case := [
  caseZeroMotion,
  caseACruise,
  caseATriangular,
  caseB "optimal_case_b_peak_no_cruise" 2 4 (1 / 2) 3 0 false,
  caseB "optimal_case_b_negative" 2 4 (1 / 2) 3 0 true,
  caseC "optimal_case_c_triangular" 4 4 (9 / 4) (1 / 2) 0,
  caseThresholdVeqVA,
  caseThresholdAB,
  caseThresholdBC,
  conservativeCase "conservative_cruise" 0 3 (limitsOf 3 2 4),
  conservativeCase "conservative_triangular" 0 (1 / 2) (limitsOf 3 2 4),
  caseGeneral]

/-! ## Stretch cases -/

/-- A stretch of an accepted case by a rational factor `k ≥ 1`. -/
structure StretchCase where
  name : String
  sourceCase : String
  factor : ℚ
deriving Repr

def stretchCases : List StretchCase := [
  { name := "stretch_conservative_cruise_by_two"
    sourceCase := "conservative_cruise"
    factor := 2 },
  { name := "stretch_conservative_triangular_by_three_halves"
    sourceCase := "conservative_triangular"
    factor := 3 / 2 }]

def findCase (name : String) : Option Case :=
  cases.find? fun c => c.name == name

/-! ## Sync cases -/

/-- One joint of a sync case: a rest-to-rest conservative move. -/
structure JointSpec where
  limits : Limits
  q0 : ℚ
  q1 : ℚ
deriving Repr

/-- A group of joints synchronised to a common duration. -/
structure SyncCase where
  name : String
  joints : List JointSpec
deriving Repr

/-- The pre-stretch profile of a joint. -/
def JointSpec.profile (j : JointSpec) : Profile :=
  planConservative j.q0 j.q1 j.limits

/-- `synchronize`'s common duration: the maximum total time. -/
def syncTimeOf (js : List JointSpec) : ℚ :=
  js.foldl (fun acc j => qmax acc j.profile.totalTime) 0

/-- `synchronize` on one joint: a zero-duration profile becomes a constant hold of the
common duration; otherwise the joint is stretched by `T / totalTime`. -/
def syncProfile (T : ℚ) (p : Profile) : Profile :=
  if p.totalTime = 0 then
    { start := { q := p.start.q, v := 0, a := 0 }, segments := [{ dur := T, jerk := 0 }] }
  else
    p.stretch (T / p.totalTime)

def syncCases : List SyncCase := [
  { name := "sync_two_joint_one_stationary"
    joints := [
      { limits := limitsOf 3 2 4, q0 := 0, q1 := 3 },
      { limits := limitsOf 2 1 1, q0 := 1, q1 := 1 }] },
  { name := "sync_six_joint_one_stationary"
    joints := [
      { limits := limitsOf 3 2 4, q0 := 0, q1 := 3 },
      { limits := limitsOf 3 2 4, q0 := 0, q1 := 1 / 2 },
      { limits := limitsOf 3 2 4, q0 := 2, q1 := 0 },
      { limits := limitsOf 5 1 1, q0 := 0, q1 := 1 },
      { limits := limitsOf 3 2 4, q0 := 0, q1 := 1 / 8 },
      { limits := limitsOf 3 2 4, q0 := 7, q1 := 7 }] },
  { name := "sync_all_stationary"
    joints := [
      { limits := limitsOf 3 2 4, q0 := 1, q1 := 1 },
      { limits := limitsOf 3 2 4, q0 := -2, q1 := -2 }] }]

/-! ## Reject cases -/

/-- One input the general planner must reject. -/
structure RejectCase where
  name : String
  limits : Limits
  start : State
  target : State
  expectedError : String
deriving Repr

/-- Reverse velocity, keep position and acceleration. -/
def rev (s : State) : State := ⟨s.q, -s.v, s.a⟩

/-- `|a| ≤ A`, `|v| ≤ V`, and the fastest legal acceleration-removal ramp stays in the
velocity band. -/
def stopFeasible (s : State) (lim : Limits) : Bool :=
  decide (qabs s.a ≤ lim.amax) && decide (qabs s.v ≤ lim.vmax) &&
    decide (qabs (s.v + s.a * qabs s.a / (2 * lim.jmax)) ≤ lim.vmax)

/-- The exact viability predicate of the stop-move-start decomposition. -/
def viable (s0 s1 : State) (lim : Limits) : Bool :=
  stopFeasible s0 lim && stopFeasible (rev s1) lim

/-- Non-finite inputs are not represented as JSON sentinels; property tests cover them.
The two `infeasible` cases fail the initial and the target half of `Viable`
respectively. -/
def rejectCases : List RejectCase := [
  { name := "reject_start_ramp_raises_velocity"
    limits := limitsOf 3 2 4
    start := ⟨0, 3, 2⟩
    target := ⟨1, 0, 0⟩
    expectedError := "infeasible" },
  { name := "reject_target_ramp_raises_velocity"
    limits := limitsOf 3 2 4
    start := ⟨0, 0, 0⟩
    target := ⟨1, -3, 2⟩
    expectedError := "infeasible" },
  { name := "reject_zero_vmax"
    limits := limitsOf 0 2 4
    start := ⟨0, 0, 0⟩
    target := ⟨1, 0, 0⟩
    expectedError := "non_positive_limit" },
  { name := "reject_negative_jmax"
    limits := limitsOf 3 2 (-1)
    start := ⟨0, 0, 0⟩
    target := ⟨1, 0, 0⟩
    expectedError := "non_positive_limit" }]

/-! ## Exact maxima

The acceleration is linear on a segment, so its extrema are at the endpoints; the jerk is
constant; the velocity is quadratic, so its extrema are the endpoints or the vertex
`τ* = -a₀/j` when it lies strictly inside the segment. -/

/-- Maximum `|v|` on a segment. -/
def Segment.maxSpeed (s : Segment) (st : State) : ℚ :=
  let m := qmax (qabs st.v) (qabs (s.exit st).v)
  if s.jerk = 0 then m
  else
    let tau := -st.a / s.jerk
    if 0 < tau ∧ tau < s.dur then qmax m (qabs (s.stateAt st tau).v) else m

/-- The exact `(max_speed, max_accel, max_jerk)` of a profile. -/
def Profile.maxima (p : Profile) : ℚ × ℚ × ℚ :=
  let rec go (st : State) (ms ma mj : ℚ) : List Segment → ℚ × ℚ × ℚ
    | [] => (ms, ma, mj)
    | s :: ss =>
        let ex := s.exit st
        go ex (qmax ms (s.maxSpeed st)) (qmax ma (qmax (qabs st.a) (qabs ex.a)))
          (qmax mj (qabs s.jerk)) ss
  go p.start 0 0 0 p.segments

def maxSpeedOf (p : Profile) : ℚ := p.maxima.1
def maxAccelOf (p : Profile) : ℚ := p.maxima.2.1
def maxJerkOf (p : Profile) : ℚ := p.maxima.2.2

/-- Every phase boundary plus one midpoint per positive-duration phase. -/
def sampleTimes (p : Profile) : List ℚ :=
  let rec go (t : ℚ) : List Segment → List ℚ
    | [] => [t]
    | s :: ss =>
        if s.dur = 0 then go (t + s.dur) ss
        else t :: (t + s.dur / 2) :: go (t + s.dur) ss
  go 0 p.segments

/-- Membership in a rational list. -/
def memQ (x : ℚ) : List ℚ → Bool
  | [] => false
  | y :: ys => decide (x = y) || memQ x ys

/-- Insertion sort of a rational list. -/
def insertQ (x : ℚ) : List ℚ → List ℚ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertQ x ys

def sortQ (xs : List ℚ) : List ℚ := xs.foldr (fun x acc => insertQ x acc) []

/-- Remove consecutive duplicates. -/
def dedupQ : List ℚ → List ℚ
  | [] => []
  | x :: ys =>
      match dedupQ ys with
      | [] => [x]
      | z :: zs => if x = z then z :: zs else x :: z :: zs

def sortedDedup (xs : List ℚ) : List ℚ := dedupQ (sortQ xs)

/-! ## Checks -/

def check (ok : Bool) (message : String) : List String :=
  if ok then [] else [message]

def limitsFailures (lim : Limits) : List String :=
  check (decide (0 < lim.vmax)) "v_max is not positive"
    ++ check (decide (0 < lim.amax)) "a_max is not positive"
    ++ check (decide (0 < lim.jmax)) "j_max is not positive"

/-- Per-segment checks: nonnegative duration, jerk bound, exit velocity/acceleration
bounds, and a constant acceleration sign. -/
def segmentsFailures (lim : Limits) (i : Nat) (st : State) : List Segment → List String
  | [] => []
  | s :: ss =>
      let ex := s.exit st
      check (decide (0 ≤ s.dur)) s!"segment {i}: negative duration"
        ++ check (decide (qabs s.jerk ≤ lim.jmax)) s!"segment {i}: jerk exceeds j_max"
        ++ check (decide (qabs ex.v ≤ lim.vmax)) s!"segment {i}: exit speed exceeds v_max"
        ++ check (decide (qabs ex.a ≤ lim.amax)) s!"segment {i}: exit acceleration exceeds a_max"
        ++ check (decide (0 ≤ st.a * ex.a))
            s!"segment {i}: acceleration changes sign inside the segment"
        ++ segmentsFailures lim (i + 1) ex ss

/-- The fold's phase starts match the emitted list, and advancing each segment reaches
the next entry. -/
def phaseStartFailures (p : Profile) : List String :=
  let rec go (i : Nat) (st : State) : List Segment → List String
    | [] => []
    | s :: ss =>
        check (decide (p.phaseStarts[i]? = some st)) s!"phase start {i} does not match the fold"
          ++ go (i + 1) (s.exit st) ss
  go 0 p.start p.segments

/-- Evaluation at every cumulative boundary returns the advanced state (the later
segment at an internal boundary, the end state at `T`). -/
def boundaryFailures (p : Profile) : List String :=
  let rec go (i : Nat) (t : ℚ) (st : State) : List Segment → List String
    | [] => []
    | s :: ss =>
        let ex := s.exit st
        let next := t + s.dur
        check (decide (p.eval next = ex)) s!"boundary {i + 1}: eval does not return the advanced state"
          ++ go (i + 1) next ex ss
  check (decide (p.eval 0 = p.start)) "boundary 0: eval does not return the start state"
    ++ go 0 0 p.start p.segments

/-- The sample list covers every boundary and midpoint and lies in `[0, T]`. -/
def sampleCoverageFailures (p : Profile) : List String :=
  let ts := sampleTimes p
  let cum := p.cumulativeTimes
  let mids := (cum.zip p.segments).filterMap fun (t, s) =>
    if s.dur = 0 then none else some (t + s.dur / 2)
  let missing := (cum ++ mids).filter fun t => !memQ t ts
  check missing.isEmpty "samples miss a phase boundary or a midpoint"
    ++ check (ts.all fun t => decide (0 ≤ t) && decide (t ≤ p.totalTime))
        "a sample lies outside [0, total_time]"

def maximaFailures (p : Profile) (lim : Limits) : List String :=
  check (decide (maxSpeedOf p ≤ lim.vmax)) "max_speed exceeds v_max"
    ++ check (decide (maxAccelOf p ≤ lim.amax)) "max_accel exceeds a_max"
    ++ check (decide (maxJerkOf p ≤ lim.jmax)) "max_jerk exceeds j_max"

/-- Feasibility: start bounds, per-segment endpoint bounds, phase-start identities,
boundary evaluation, sample coverage and the exact maxima. -/
def profileFailures (p : Profile) (lim : Limits) : List String :=
  check (decide (qabs p.start.v ≤ lim.vmax)) "profile start speed exceeds v_max"
    ++ check (decide (qabs p.start.a ≤ lim.amax)) "profile start acceleration exceeds a_max"
    ++ segmentsFailures lim 0 p.start p.segments
    ++ phaseStartFailures p
    ++ boundaryFailures p
    ++ sampleCoverageFailures p
    ++ maximaFailures p lim

/-- The case-defining equation, re-derived from the rational shape. -/
def definingFailures (c : Case) : List String :=
  let lim := c.limits
  let A := lim.amax
  let J := lim.jmax
  let V := lim.vmax
  let delta := c.goal.q - c.start.q
  let D := qabs delta
  let s := signOf delta
  match c.defining with
  | .zeroMotion =>
      check (decide (c.segments = [])) "zero motion: segments are not empty"
        ++ check (decide (c.start = c.goal)) "zero motion: start and end differ"
        ++ check (decide (c.kind = "zero_motion")) "zero motion: kind is not zero_motion"
        ++ check (decide (c.mode = "optimal")) "zero motion: mode is not optimal"
  | .conservative =>
      let expected := planConservative c.start.q c.goal.q lim
      let tau := qmin 1 (qmin (A / J) (V / J))
      let dmin := 2 * J * tau ^ 3
      let j := if D ≥ dmin then J else D / (2 * tau ^ 3)
      let tc := if D ≥ dmin then (D - dmin) / (J * tau ^ 2) else 0
      check (decide (D = 2 * j * tau ^ 3 + j * tau ^ 2 * tc))
          "conservative: the case displacement does not match the §3.8 template"
        ++ check (decide ((D < dmin ∨ j = J) ∧ (D ≥ dmin ∨ tc = 0)))
            "conservative: the template branch selection is wrong"
        ++ check (decide (c.segments = sevenSegments j s [tau, 0, tau, tc, tau, 0, tau]))
            "conservative: the segments do not match the §3.8 template"
        ++ check (decide (c.mode = "conservative")) "conservative: mode is not conservative"
        ++ check (decide (c.kind = "conservative")) "conservative: kind is not conservative"
        ++ check (decide (expected.segments = c.segments))
            "conservative: emitted segments do not match the §3.8 template"
        ++ check (decide (expected.endState = c.goal))
            "conservative: emitted end does not match the §3.8 template"
        ++ check (decide (c.start.q ≠ c.goal.q)) "conservative: zero displacement is zero_motion"
  | .cruiseReached tj ta tc =>
      let tj' := A / J
      let V' := A * (tj' + ta)
      let D' := V' * (2 * tj' + ta + tc)
      check (decide (tj = tj')) "A: t_j is not A/J"
        ++ check (decide (V = V')) "A: V is not A(t_j+t_a)"
        ++ check (decide (V ≥ A ^ 2 / J)) "A: the acceleration limit is not reached"
        ++ check (decide (D = D')) "A: D is not V(2t_j+t_a+t_c)"
        ++ check (decide (0 ≤ ta ∧ 0 ≤ tc)) "A: a duration is negative"
        ++ check (decide (c.segments = sevenSegments J s [tj, ta, tj, tc, tj, ta, tj]))
            "A: the 7-slot segment pattern is wrong"
        ++ check (decide (c.kind = "cruise")) "A: kind is not cruise"
        ++ check (decide (c.mode = "optimal")) "A: mode is not optimal"
  | .cruiseTriangular tr tc =>
      let D' := 2 * V * tr + V * tc
      check (decide (V = J * tr ^ 2)) "A': V is not J t_r^2"
        ++ check (decide (V < A ^ 2 / J)) "A': V is not below v_A"
        ++ check (decide (D = D')) "A': D is not 2V t_r + V t_c"
        ++ check (decide (0 ≤ tc)) "A': the cruise duration is negative"
        ++ check (decide (c.segments = sevenSegments J s [tr, 0, tr, tc, tr, 0, tr]))
            "A': the 7-slot segment pattern is wrong"
        ++ check (decide (c.kind = "cruise")) "A': kind is not cruise"
        ++ check (decide (c.mode = "optimal")) "A': mode is not optimal"
  | .peakNoCruise tj ta vp =>
      let tj' := A / J
      let D' := vp ^ 2 / A + vp * tj'
      check (decide (tj = tj')) "B: t_j is not A/J"
        ++ check (decide (vp = A * (tj' + ta))) "B: v_p is not A(t_j+t_a)"
        ++ check (decide (V ≥ A ^ 2 / J)) "B: V is below v_A"
        ++ check (decide (vp < V)) "B: v_p is not below V"
        ++ check (decide (D = D')) "B: D is not v_p^2/A + v_p t_j"
        ++ check (decide (D < V * (tj' + V / A))) "B: D is not below D_full(V)"
        ++ check (decide (D ≥ 2 * A ^ 3 / J ^ 2)) "B: D is below 2A^3/J^2"
        ++ check (decide (0 ≤ ta)) "B: t_a is negative"
        ++ check (decide (c.segments = sevenSegments J s [tj, ta, tj, 0, tj, ta, tj]))
            "B: the 7-slot segment pattern is wrong"
        ++ check (decide (c.kind = "peak_no_cruise")) "B: kind is not peak_no_cruise"
        ++ check (decide (c.mode = "optimal")) "B: mode is not optimal"
  | .triangular tr =>
      let D' := 2 * J * tr ^ 3
      let branch : Bool :=
        if V ≥ A ^ 2 / J then
          decide (D < V * (A / J + V / A)) && decide (¬ (D ≥ 2 * A ^ 3 / J ^ 2))
        else
          decide (D ^ 2 * J < 4 * V ^ 3)
      check (decide (D = D')) "C: D is not 2J t_r^3"
        ++ check (decide (0 < tr)) "C: t_r is not positive"
        ++ check branch "C: the case is not in the triangular branch"
        ++ check (decide (c.segments = sevenSegments J s [tr, 0, tr, 0, tr, 0, tr]))
            "C: the 7-slot segment pattern is wrong"
        ++ check (decide (c.kind = "triangular")) "C: kind is not triangular"
        ++ check (decide (c.mode = "optimal")) "C: mode is not optimal"
  | .general tr0 tr1 =>
      let v0 := J * tr0 ^ 2
      let v1 := J * tr1 ^ 2
      let stopSegs : List Segment := [{ dur := tr0, jerk := -J }, { dur := tr0, jerk := J }]
      let startSegs : List Segment := [{ dur := tr1, jerk := J }, { dur := tr1, jerk := -J }]
      let stopEndQ := c.start.q + J * tr0 ^ 3
      let startStartQ := c.goal.q - J * tr1 ^ 3
      let mid := planConservative stopEndQ startStartQ lim
      check (decide (0 < v0)) "general: the stop brake velocity is not positive"
        ++ check (decide (0 < v1)) "general: the start brake velocity is not positive"
        ++ check (decide (c.start.v = v0)) "general: the start velocity is not J t_r0^2"
        ++ check (decide (c.goal.v = v1)) "general: the end velocity is not J t_r1^2"
        ++ check (decide (c.start.a = 0 ∧ c.goal.a = 0))
            "general: an endpoint acceleration is not zero"
        ++ check (decide (v0 < A ^ 2 / J)) "general: the stop brake is not triangular"
        ++ check (decide (v1 < A ^ 2 / J)) "general: the start brake is not triangular"
        ++ check (viable c.start c.goal lim) "general: the state is not viable"
        ++ check (decide (c.segments = stopSegs ++ mid.segments ++ startSegs))
            "general: the segments are not stop ++ conservative middle ++ start"
        ++ check (decide (c.kind = "general")) "general: kind is not general"
        ++ check (decide (c.mode = "general")) "general: mode is not general"

/-- Boundary cases must sit on an exact case-selection boundary. -/
def thresholdFailures (c : Case) : List String :=
  if c.threshold then
    let A := c.limits.amax
    let J := c.limits.jmax
    match c.defining with
    | .cruiseReached tj ta tc =>
        check (decide (c.limits.vmax = A ^ 2 / J ∨ tc = 0 ∨
            c.limits.vmax * (2 * tj + ta) = qabs (c.goal.q - c.start.q)))
          "threshold cruise case is not on an exact case boundary"
    | .peakNoCruise _ _ _ =>
        check (decide (qabs (c.goal.q - c.start.q) = 2 * A ^ 3 / J ^ 2))
          "threshold peak case is not on the B/C boundary"
    | _ => []
  else []

/-- All checks for one accepted case. -/
def caseFailures (c : Case) : List String :=
  let p : Profile := { start := c.start, segments := c.segments }
  limitsFailures c.limits
    ++ check (decide (p.start = c.start)) "profile start does not match the case start"
    ++ check (decide (p.endState = c.goal)) "profile end does not match the case end"
    ++ (if c.restEnds then
          check (decide (c.start.v = 0 ∧ c.start.a = 0)) "profile start is not at rest"
            ++ check (decide (p.endState.v = 0 ∧ p.endState.a = 0)) "profile end is not at rest"
        else [])
    ++ profileFailures p c.limits
    ++ definingFailures c
    ++ thresholdFailures c

/-- All checks for one stretch case, including the `stateAt_stretch` relation. -/
def stretchCaseFailures (sc : StretchCase) : List String :=
  match findCase sc.sourceCase with
  | none => [s!"source case '{sc.sourceCase}' not found"]
  | some src =>
      let source : Profile := { start := src.start, segments := src.segments }
      let p := source.stretch sc.factor
      let k := sc.factor
      check (decide (1 ≤ k)) "stretch factor is below one"
        ++ check (decide (p.totalTime = k * source.totalTime))
            "stretched total time is not k times the source total time"
        ++ check (decide (p.start.q = source.start.q)) "stretch changed the position"
        ++ check (decide (p.start.v = source.start.v / k)) "stretched start velocity is not v/k"
        ++ check (decide (p.start.a = source.start.a / (k * k)))
            "stretched start acceleration is not a/k^2"
        ++ check (decide (p.endState.q = source.endState.q)) "stretch changed the end position"
        ++ check (decide (p.segments.map (fun s => s.dur) =
              source.segments.map (fun s => s.dur * k)))
            "stretched durations are not scaled by k"
        ++ check (decide (p.segments.map (fun s => s.jerk) =
              source.segments.map (fun s => s.jerk / (k * k * k))))
            "stretched jerks are not divided by k^3"
        ++ profileFailures p src.limits
        ++ (sampleTimes source).flatMap fun t =>
            let want := source.eval t
            let got := p.eval (k * t)
            check (decide (got.q = want.q)) "stretch state relation fails in position"
              ++ check (decide (got.v = want.v / k)) "stretch state relation fails in velocity"
              ++ check (decide (got.a = want.a / (k * k)))
                  "stretch state relation fails in acceleration"

/-- All checks for one sync case. -/
def syncCaseFailures (sc : SyncCase) : List String :=
  let T := syncTimeOf sc.joints
  check (decide (sc.joints.length = 2 ∨ sc.joints.length = 6))
      "expected two or six joints"
    ++ check (decide (0 ≤ T)) "negative sync time"
    ++ sc.joints.flatMap fun j =>
        let src := j.profile
        let syn := syncProfile T src
        limitsFailures j.limits
          ++ check (decide (src.start.v = 0 ∧ src.start.a = 0 ∧
                src.endState.v = 0 ∧ src.endState.a = 0))
              "joint source profile is not rest-to-rest"
          ++ check (decide (syn.totalTime = T)) "synchronized joint has the wrong total time"
          ++ profileFailures syn j.limits
          ++ (if src.totalTime = 0 then
                check (decide (syn.segments = [{ dur := T, jerk := 0 }]))
                    "zero-motion joint is not a constant hold"
                  ++ check (decide (syn.start.q = src.start.q))
                      "zero-motion hold moved the position"
              else
                let k := T / src.totalTime
                check (decide (1 ≤ k)) "synchronized scale is below one"
                  ++ check (decide (syn.segments.map (fun s => s.dur) =
                        src.segments.map (fun s => s.dur * k)))
                      "synchronized durations are not scaled"
                  ++ check (decide (syn.segments.map (fun s => s.jerk) =
                        src.segments.map (fun s => s.jerk / (k * k * k))))
                      "synchronized jerks are not scaled"
                  ++ (sampleTimes src).flatMap fun t =>
                      let want := src.eval t
                      let got := syn.eval (k * t)
                      check (decide (got.q = want.q)) "sync state relation fails in position"
                        ++ check (decide (got.v = want.v / k))
                            "sync state relation fails in velocity"
                        ++ check (decide (got.a = want.a / (k * k)))
                            "sync state relation fails in acceleration")

/-- All checks for one reject case. -/
def rejectCaseFailures (r : RejectCase) : List String :=
  match r.expectedError with
  | "infeasible" =>
      limitsFailures r.limits
        ++ check (!(stopFeasible r.start r.limits && stopFeasible (rev r.target) r.limits))
            "expected Infeasible but the state is Viable"
  | "non_positive_limit" =>
      check (decide (r.limits.vmax ≤ 0 ∨ r.limits.amax ≤ 0 ∨ r.limits.jmax ≤ 0))
        "expected NonPositiveLimit but every limit is positive"
  | _ => [s!"unknown expected_error '{r.expectedError}'"]

def memS (x : String) (xs : List String) : Bool := xs.any fun y => x == y

def duplicateFailures (xs : List String) : List String :=
  let rec go (seen : List String) : List String → List String
    | [] => []
    | x :: rest =>
        (if memS x seen then [s!"duplicate case name '{x}'"] else [])
          ++ go (x :: seen) rest
  go [] xs

def kindCheck (k : String) : List String :=
  check (cases.any fun c => c.kind == k) s!"no case with kind '{k}'"

/-- Document-level invariants: unique names, resolvable stretch sources, two or six sync
joints, and every `PlanKind` represented. -/
def documentFailures : List String :=
  duplicateFailures (cases.map (fun c => c.name) ++ stretchCases.map (fun s => s.name)
      ++ syncCases.map (fun s => s.name) ++ rejectCases.map (fun r => r.name))
    ++ (stretchCases.flatMap fun sc =>
        check (decide (1 ≤ sc.factor)) s!"{sc.name}: stretch factor below one"
          ++ check (cases.any fun c => c.name == sc.sourceCase)
              s!"{sc.name}: source case not found")
    ++ (syncCases.flatMap fun sc =>
        check (decide (sc.joints.length = 2 ∨ sc.joints.length = 6))
          s!"{sc.name}: expected two or six joints")
    ++ kindCheck "zero_motion"
    ++ kindCheck "conservative"
    ++ kindCheck "cruise"
    ++ kindCheck "peak_no_cruise"
    ++ kindCheck "triangular"
    ++ kindCheck "general"

/-- Every failure in the document, with the case name prefixed. -/
def allFailures : List String :=
  (cases.flatMap fun c => (caseFailures c).map fun f => s!"{c.name}: {f}")
    ++ (stretchCases.flatMap fun sc => (stretchCaseFailures sc).map fun f => s!"{sc.name}: {f}")
    ++ (syncCases.flatMap fun sc => (syncCaseFailures sc).map fun f => s!"{sc.name}: {f}")
    ++ (rejectCases.flatMap fun r => (rejectCaseFailures r).map fun f => s!"{r.name}: {f}")
    ++ documentFailures

/-! ## Serialization -/

/-- Render a rational exactly: `3` for integers, `-3/5` otherwise. `ℚ` is normalised with
a positive denominator, so this form is unambiguous. -/
def ratStr (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

def ratJson (q : ℚ) : Json := .str (ratStr q)

def stateJson (s : State) : Json :=
  .mkObj [("q", ratJson s.q), ("v", ratJson s.v), ("a", ratJson s.a)]

def segmentJson (s : Segment) : Json :=
  .mkObj [("duration", ratJson s.dur), ("jerk", ratJson s.jerk)]

def segmentsJson (ss : List Segment) : Json :=
  .arr (ss.map segmentJson).toArray

def statesJson (ss : List State) : Json :=
  .arr (ss.map stateJson).toArray

def limitsJson (l : Limits) : Json :=
  .mkObj [("v_max", ratJson l.vmax), ("a_max", ratJson l.amax), ("j_max", ratJson l.jmax)]

def sampleJson (p : Profile) (t : ℚ) : Json :=
  let st := p.eval t
  .mkObj [("t", ratJson t), ("q", ratJson st.q), ("v", ratJson st.v), ("a", ratJson st.a)]

/-- The expected block of an accepted (or stretched) profile: total time, segments,
phase starts, exact maxima and samples at every boundary plus a midpoint. -/
def profileExpectedJson (p : Profile) : Json :=
  .mkObj [
    ("total_time", ratJson p.totalTime),
    ("segments", segmentsJson p.segments),
    ("phase_starts", statesJson p.phaseStarts),
    ("max_speed", ratJson (maxSpeedOf p)),
    ("max_accel", ratJson (maxAccelOf p)),
    ("max_jerk", ratJson (maxJerkOf p)),
    ("samples", .arr ((sampleTimes p).map (sampleJson p)).toArray)]

def caseJson (c : Case) : Json :=
  let p : Profile := { start := c.start, segments := c.segments }
  .mkObj [
    ("name", .str c.name),
    ("mode", .str c.mode),
    ("kind", .str c.kind),
    ("threshold", .bool c.threshold),
    ("limits", limitsJson c.limits),
    ("start", stateJson c.start),
    ("end", stateJson c.goal),
    ("expected", profileExpectedJson p)]

def stretchCaseJson (sc : StretchCase) : Json :=
  match findCase sc.sourceCase with
  | none => .null
  | some src =>
      let source : Profile := { start := src.start, segments := src.segments }
      let p := source.stretch sc.factor
      .mkObj [
        ("name", .str sc.name),
        ("source_case", .str sc.sourceCase),
        ("factor", ratJson sc.factor),
        ("start", stateJson p.start),
        ("end", stateJson p.endState),
        ("expected", profileExpectedJson p)]

def jointInputJson (j : JointSpec) : Json :=
  let p := j.profile
  .mkObj [
    ("limits", limitsJson j.limits),
    ("start", stateJson p.start),
    ("end", stateJson p.endState),
    ("pre_stretch_total_time", ratJson p.totalTime),
    ("pre_stretch_segments", segmentsJson p.segments),
    ("pre_stretch_phase_starts", statesJson p.phaseStarts)]

def scaleJson (T : ℚ) (p : Profile) : Json :=
  if p.totalTime = 0 then .null else ratJson (T / p.totalTime)

def syncCaseJson (sc : SyncCase) : Json :=
  let T := syncTimeOf sc.joints
  let ps := sc.joints.map fun j => syncProfile T j.profile
  let times := sortedDedup (ps.flatMap sampleTimes)
  .mkObj [
    ("name", .str sc.name),
    ("joints", .arr (sc.joints.map jointInputJson).toArray),
    ("expected", .mkObj [
      ("sync_time", ratJson T),
      ("scales", .arr ((sc.joints.map fun j => scaleJson T j.profile).toArray)),
      ("synchronized_segments", .arr (ps.map fun p => segmentsJson p.segments).toArray),
      ("phase_starts", .arr (ps.map fun p => statesJson p.phaseStarts).toArray),
      ("max_speed", .arr (ps.map fun p => ratJson (maxSpeedOf p)).toArray),
      ("max_accel", .arr (ps.map fun p => ratJson (maxAccelOf p)).toArray),
      ("max_jerk", .arr (ps.map fun p => ratJson (maxJerkOf p)).toArray),
      ("samples", .arr (times.map fun t =>
        .mkObj [("t", ratJson t),
          ("joints", .arr (ps.map fun p => stateJson (p.eval t)).toArray)]).toArray)])]

def rejectCaseJson (r : RejectCase) : Json :=
  .mkObj [
    ("name", .str r.name),
    ("limits", limitsJson r.limits),
    ("start", stateJson r.start),
    ("target", stateJson r.target),
    ("expected_error", .str r.expectedError)]

/-- The document. Every motion numeral is an exact integer or `"n/d"` string;
`schema_version` is a JSON integer, as in the other generators. -/
def document : Json := .mkObj [
  ("schema_version", (1 : Json)),
  ("source", .str "lean/Motion.lean, evaluated by lean/MotionTestData.lean over the rationals"),
  ("conventions", .str "q in radians, v rad/s, a rad/s^2, jerk rad/s^3, t in seconds. \
A profile is a start State, an end State and a list of {duration, jerk} segments; \
phase_starts are the entry state of each segment, one per segment, derived by advancing \
(the end state is not repeated). samples cover every phase boundary and one midpoint per \
positive-duration phase. Every motion numeral is an exact integer or \"n/d\" string, never \
a JSON number; schema_version is a JSON integer. max_speed/max_accel/max_jerk are exact \
maxima over the whole profile. mode is conservative/optimal/general; kind is the snake_case \
PlanKind. stretch_cases scale a source profile by a rational factor k >= 1: durations x k, \
jerks / k^3, start velocity / k, start acceleration / k^2. sync_cases synchronize \
rest-to-rest conservative profiles to the maximum total time; scales is null for a \
zero-total-time joint, which becomes a constant hold of sync_time. Reject cases name the \
expected PlanError variant; non-finite inputs are covered by property tests, not JSON \
sentinels."),
  ("tolerances", .mkObj [("relative", .str "1/1000000000000"),
    ("absolute", .str "1/1000000000000")]),
  ("cases", .arr (cases.map caseJson).toArray),
  ("stretch_cases", .arr (stretchCases.map stretchCaseJson).toArray),
  ("sync_cases", .arr (syncCases.map syncCaseJson).toArray),
  ("reject_cases", .arr (rejectCases.map rejectCaseJson).toArray)]

end MotionTestData

open MotionTestData

/-- Entry point: check every case, then write the JSON. Takes the output path as its only
argument, defaulting to `../test_data/motion_profiles.json` (relative to `lean/`, which is
where `lake exe` is run from). Exits non-zero without writing anything if a case fails its
checks. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "../test_data/motion_profiles.json"
  let failures := allFailures
  unless failures.isEmpty do
    IO.eprintln "refusing to write test data: a case failed its checks"
    for f in failures do
      IO.eprintln s!"  {f}"
    return 1
  if let some dir := (System.FilePath.mk path).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path (Json.pretty document ++ "\n")
  IO.println s!"wrote {cases.length} cases, {stretchCases.length} stretch cases, {syncCases.length} sync cases, {rejectCases.length} reject cases to {path}"
  return 0
