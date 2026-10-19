# What is proved, what is tested, and what is neither

This document states the boundary of the Rust port's verification, and why the boundary
falls where it does. It is the counterpart of `mathematics.md`'s *What the specification
proves* section: that section says what the Lean covers and what it deliberately does
not; this one says what that means for the Rust.

## The starting point

`lean/` is a **specification**, not an implementation. `Kinematics`, `Zyz`, `Atan2` and
`InverseKinematics` all open `noncomputable section` and work over `ℝ`. `TorqueWrench`
and `Dynamics` are stated over an arbitrary `CommRing α`. There are no `sorry`s, no
`axiom`s, no `@[export]` and no FFI surface.

So the question is not "how do we port the proofs" — they are not portable — but "what
does a proof about `ℝ` tell us about `f64` code". The honest answer is: it tells us
**which property the code must satisfy**, and for the rational part of the mathematics it
hands us **vectors to check that property against**. That is a strong form of validation
and it is what this port is built on. It is not a proof about the floating-point code, and
nothing here pretends otherwise.

## Paths that were considered and rejected

### Lean → Rust FFI

Blocked twice over, either blocker fatal:

**There is nothing computable to link.** `ℝ` in Mathlib is a quotient of Cauchy sequences
and has no runtime representation, so Lean's code generator refuses to compile `fk`,
`solutions`, `Real.atan2` and the rest. `#eval` on them is an elaboration error, not a slow
call. The `.lake/build/ir/*.c` files are a red herring: Lean emits IR per module, and a
module containing `noncomputable` definitions still emits IR for its computable scaffolding
and its proofs.

**There is no export surface.** No `@[export]` appears anywhere in the tree, and there is
no `.so`, `.a`, `.dll` or `.lib` under `.lake/build` — the only linked artefact is
`force_torque_test_data.exe`.

The one computable part is `TorqueWrench` and `Dynamics`, which is exactly why
`ForceTorqueTestData.lean` can specialise them to `ℚ` and run. Even there, linking would
mean shipping the Lean runtime and Mathlib to call about thirty small functions and
receive exact rationals — where running `lake exe` and reading JSON gives the same numbers
with none of it. That is the pattern this repository already uses.

### Rust → Lean extraction (Aeneas/Charon)

This is the direction that would prove something about the *actual* Rust source, and it is
unavailable for a hard reason: **Charon rejects `f32`/`f64` at translation time** with
"Floats are not supported yet", even when floats appear only in an unused function
signature. Aeneas's published limitations list integers and naturals only; `f64` is named as
a future goal. The entire Rust kinematics is `f64`.

The deeper problem would survive even if floats landed tomorrow. Aeneas translates Rust into
a model whose scalars are **bitvectors**. Connecting that to `lean/`'s `ℝ` specification
requires proving that the `f64` computation *approximates* the real-number chain — a
rounding-error analysis. That is a different and much harder theorem than anything currently
in the tree. Extraction alone never supplies that bridge.

### Proving the Rust in Rust

Verus has no floating-point support. Flux is a refinement-type checker and is not a fit.
Kani can check panic-freedom, index bounds and overflow, and can treat floats as bit
patterns — but it cannot establish that a tolerance threshold is *correct*. It is used
here for exactly the part it is good at, and no more.

### FFI over a `ℚ` restatement

If the kinematics were restated over `ℚ` the first blocker above would evaporate: a
rational development is computable and can carry `@[export]`. This moves the FFI route from
*impossible* to *merely inadvisable* — you would ship the Lean runtime and Mathlib to
obtain numbers `lake exe` → JSON already provides, and you would still have no proof about
the `f64` results, only a verified oracle running beside them.

It also cannot be done for the part that matters most. `atan2`, `arccos` and — by Niven's
theorem — `cos` and `sin` of a rational degree measure are irrational outside a handful of
values, so **the closed-form solver cannot be restated over `ℚ` as an angle-valued
function**. That is arithmetic, not engineering.

## What was built instead

### The polynomial layer is exact, and is checked exactly

Every use the forward chain makes of an angle is through its cosine and sine — which is
what `dh_congr` and `fk_congr` say. Supplying those as data makes the whole forward chain a
polynomial, and a polynomial evaluates over any commutative ring. Since every alpha in the
supported arm's fixed twist pattern is a quarter turn, whose cosine and sine are `0` and `1`
exactly, the entire chain evaluates over `ℚ` with no rounding at all.

This is expressed in the type system rather than in a convention. `robot-kinematics` splits
its arithmetic across two traits:

- `Field` — the polynomial layer. The forward chain, the wrench algebra and the dynamics
  live here, and all of them run unchanged over an exact rational type.
- `Scalar: Field` — adds `sqrt`, `sin`, `cos`, `atan2`, `acos`. This is where Rust and the
  real-number specification genuinely part company, and it is deliberately a small,
  nameable set of functions.

The same split is what `TorqueWrench.lean` and `Dynamics.lean` already exploit: being
polynomial is why they are stated over a `CommRing` and why they have exact ground truth
today.

So `lean/KinematicsTestData.lean` and the existing `ForceTorqueTestData.lean` emit vectors
over `ℚ`, and the Rust is held to them with `==` — no tolerance, and a disagreement is a
real disagreement rather than floating-point drift. `test_force_torque.py` already enforced
that rule from the Python side, including failing loudly on finding a JSON number where a
numeral string belongs; `robot-golden`'s `numeral` module is its Rust counterpart.

### The transcendental layer is tested against the theorems

The parts that are not polynomial cannot be checked against vectors, because their values
are irrational. They are covered instead by restating each Lean theorem as an executable
property of the Rust, named after the theorem so `docs/lean-rust-map.md` and the test names
line up:

- `fk_of_mem_solutions` — every candidate the solver returns reproduces the target pose
  within a declared tolerance.
- `exists_solution_angles_eq` — for a non-degenerate commanded configuration, some returned
  candidate carries that configuration's own branch labels and every angle equal modulo a
  full turn. The modulo-2π comparison is exact even in `f64`, so only the branch labels and
  the recovery need checking, not a float value.
- `solutions_ne_nil`, `length_solutions_le_eight`, `solutions_eq_nil_of_not_reachable` —
  properties of the candidate list rather than of any angle in it.
- `recoveredContactWrench_measuredWrench`, `inertialWrench_transport`, `gravityWrench_add`
  and the rest — exact over the rationals, so checked with `==`.

### The exact-decision layer is checked against Lean

Lean decides degeneracy with exact predicates: `r ≠ 0`, membership in `Set.Icc (-1) 1`,
`sin θ5 ≠ 0`. `f64` cannot, so every tolerance-bearing decision is confined to one
trigonometry-free module, `branch.rs`, which turns a handful of scalars into a branch plan.

Most predicates in that module are exactly rational: `hypot(x,y) = 0` holds exactly when
both are zero, so the wrist-singularity test needs no square root at all, and `r = 0` and
the fold-back condition are direct comparisons.

**The reachability band is not.** `elbowCosine` involves `q² + h²`, and with
`q = σ·r − a₁` that expands to `ρ − 2σ·a₁·r + a₁² + h²`, where `ρ = x₄² + y₄²` is rational
but `r = √ρ` is not. So the band test is a comparison in the quadratic extension
**ℚ(√ρ)**, not in ℚ. It is still exact and still decidable — carry `(rational part,
radical coefficient, ρ)` and compare `α + β√ρ` against a bound by isolating the radical and
squaring with sign care — but the radical has to be carried, and an earlier draft of this
document claimed otherwise.

`lean/BranchDecisionQ.lean` restates that layer accordingly — leaving the `ℝ` development
unmodified — so the Rust branch plan is compared `==` against branch plans Lean computed
exactly, rather than against thresholds documented as standing in for Lean's predicates.

That is the layer where the exact-predicate/float-tolerance gap actually bites, and it is
the layer where the comparison is strongest.

### Precision separation — designed, not built

The intent is to re-run the property suite at ~200 bits, so that a property failing at
`f64` but holding at high precision is identifiable as a rounding artefact and one failing
at both is an algorithmic mistake. **This is not built, and the obstacle is a decision made
earlier in this port rather than an oversight.**

`Scalar` is sealed to `f64` and `f32` inside `robot-kinematics`, on the reasoning that a
fourth instantiation nobody exercises weakens the argument about which ones the suite
covers. That seal also stops a test crate from supplying a high-precision scalar, and
`solutions`/`solve` need `Scalar` because they take square roots and read angles. `Field`
is open, which is why the exact `Ratio` corpus works, but the rational type has no
transcendentals and so cannot stand in here.

Two ways to unblock it, neither taken: implement the high-precision type *inside*
`robot-kinematics` behind a test-only feature, keeping the seal; or open the seal and
accept that `Scalar` means "a real number at some precision" by convention rather than by
construction. The first preserves the invariant and costs a dependency — the mature option
is GMP-backed, which is awkward on Windows; the second is two lines and gives the invariant
up.

What production does is unaffected either way. **Production is plain `f64` and nothing
else** — the port has to be adaptable to a real-time control loop, which means ordinary
floating-point arithmetic with predictable codegen. Generic code monomorphised at `f64` is
exactly that, so the trait costs nothing at runtime; it is not a licence to do arithmetic
in any other type on a control path.

## The boundary, stated plainly

Not proved, and not claimed:

- **`f64` ≠ `ℝ`.** Every theorem above is about real numbers. The Rust approximates them.
  The tolerances in `solve` are where that approximation is made explicit, and each one
  cites the Lean predicate it stands in for.
- **The numeric solvers are out of scope in Lean too.** `inverse_kinematics_position` and
  `inverse_kinematics_position_preserving_roll_yaw` are damped least squares over a
  Jacobian, with convergence tolerances; `mathematics.md` excludes them, and so does this
  port unless they are needed.
- **Joint limits are the caller's business.** Neither `mathematics.md` nor Lean nor
  `kinematics.py` carries any. They belong in a caller-supplied constraint layer, not in
  the solver.
- **There is no arm dynamics to verify.** `Dynamics.lean` is single-rigid-body Newton–Euler
  for the payload distal to the sensor. There is no mass matrix, no Jacobian, no joint
  torque model, and `robot_parameters.json` carries no masses or inertias. Anything in that
  direction is new mathematics with no specification behind it.
- **FloatSpec is the eventual path to error bounds.** The Flocq port to Lean 4 makes
  relative-error bounds on floating-point kernels provable in principle. It would mean
  re-expressing the float kernels in Lean and proving the bounds there — a research-grade
  effort, out of proportion to the risk it would retire, and not attempted here.

## Motion control

`lean/Motion/` is the specification of the jerk-limited motion layer; `crates/robot-motion`
is the implementation. The part of the mathematics that is polynomial — `State`,
`Segment`, `Profile`, evaluation, stretch, synchronization — is stated over an arbitrary
`Field` in Rust, so the exact-rational type runs the same code as production and the golden
tests compare it with `==`. The **conservative** planner is radical-free and `Field`-generic
for the same reason; its durations and jerk values are exact over `ℚ`.

The **optimal** 7-phase planner needs `sqrt`/`cbrt`, so it is `f64`-only. Its golden data is
still exact (constructed from rational durations/peaks), but the planner comparison uses the
declared `1e-12` relative/absolute tolerance. This is the same real-versus-`f64` boundary as
the rest of the port: the Lean specification is over `ℝ`, and nothing here claims a proof
about the floating-point values.

The **conservative M1-default** planner's full ladder — boundary conditions, feasibility,
`C²` smoothness, monotonicity, total-time sign, the seven-slot bound and shape — is proved in
`Motion.Plan.Conservative`. Stretching, synchronisation, the synchronised stop and the scalar
MoveJ are proved in `Motion.Sync` and `Motion.MoveJ`; their Rust counterparts are exercised by
the exact-rational sync/stretch cases and by `tests/sync.rs`. The M1-opt radical-case Lean
proofs remain staged; the Rust optimal planner is implemented and tolerance-tested.

The **general** stop–move–start planner rejects exactly the states outside its own viability
predicate (`stop_feasible` at the start and at the time-reversed target); the Lean module
proves the constructive contract (stop/start feasibility, `planGeneral` boundary,
feasibility, the exact `isSome ↔ Viable` statement and the 15-segment bound). That is not a
global infeasibility certificate: a direct profile that never passes through rest can exist
outside it, and the arbitrary-profile necessity half (`stopFeasible_necessary`) is a named
gap. The tracker/supervisor tests are a headless plant model, not a theorem about a
physical robot; the kinematic error growth under a position clamp and a monotone reference
is proved in `Motion.Supervisor` (`stall_error_grows` and the finite-time crossing
corollary), but the saturation-dependent stall decision remains a simulation property.

The `lin` (Cartesian straight-line) mode has a Lean vocabulary but no Lean theorem.
`Motion.Linear` defines `LinearPath`, `LinCommand`, `SampledTrajectory`,
`SampledSolutions`, the four sampled checks (`SamplesAreSolutions`, `SamplesOnPath`,
`BranchContinuous`, `WithinSampledLimits`) and `LinPlan`/`HasLinPlan`. `HasLinPlan` is a
definition; nothing asserts it for a command. The Rust counterpart is now implemented:
`robot_motion::linear` carries the vocabulary and the checks, and `robot-app`'s
`motion_linear` module adds the numerical time law. Certification samples the path,
solves each pose with the app's tolerance-widened closed-form solver (`solve`,
`Tolerances::python()`), rejects a branch/winding step or an FK miss, and derives
conservative scalar limits from finite-difference `M1/M2/M3` bounds; the resulting S-curve
is re-sampled in time and checked again. The exact `solutions` function is not used at a
singular pose: an RPY round trip can move the pose by an ulp, and the unfiltered exact
candidates can then jump between wrist splits. The guarantee is over the sample grid and
the S-curve's analytic inequalities, not continuous time, and the Lean module still proves
nothing about it. M5's `cartesian_path_feasible` remains the separate conditional
certificate and is not claimed here.

What is deliberately not attempted: arm dynamics and torque limits (the repository has no
mass matrix or torque model), true time-optimal path parameterization, position-limit
enforcement in the planner, and a tracking-error bound for `f64`. The M5 Cartesian mode is a
conditional feasibility certificate whose path derivative bounds are sampled, not proved.
`Motion.Linear` does not narrow that gap.

## Summary

| Layer | Checked against | Strength |
| --- | --- | --- |
| Forward chain, wrench algebra, dynamics | Lean-generated exact rational vectors | `==`, no tolerance |
| Branch and degeneracy decisions | Lean-generated exact branch plans | `==`, no tolerance |
| Angles (`atan2`, `arccos`, `sin`, `cos`) | Restated Lean theorems as properties | Tolerance, but the theorem names the property |
| Panic-freedom, index bounds, overflow | Kani over the fixed-capacity buffers | Bounded model check |
| Rounding versus algorithmic error | Same suite at ~200 bits | **Not built** — blocked by the sealed `Scalar` |
| `f64` equals `ℝ` | — | Not attempted, and not attemptable today |
