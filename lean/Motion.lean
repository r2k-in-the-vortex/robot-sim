module

public import Motion.Basic
public import Motion.Glue
public import Motion.Smooth
public import Motion.Transforms
public import Motion.Compose
public import Motion.Plan.Conservative
public import Motion.General
public import Motion.MoveJ
public import Motion.Linear
public import Motion.Sync
public import Motion.Supervisor

/-!
# Motion

Jerk-limited motion control: cubic profiles, feasibility, the conservative rational
planner, general boundary conditions, stretching, synchronization, the scalar MoveJ,
the definitions-only sampled `lin` vocabulary (`Motion.Linear`), the supervisor's
kinematic lemma and the composition bound.

`Motion.Linear` states no theorem: the `lin` feasibility decision is the numerical,
sampled check of `docs/motion_control.md` §5.6, and M5 remains future work.

The optimal 7-phase planner is implemented and golden-tested in Rust; its Lean proofs
are staged (`docs/motion_control.md` §4.7). Importing `Motion` is the public entry point.
-/

@[expose] public section

namespace Motion

end Motion
