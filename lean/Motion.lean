module

public import Motion.Basic
public import Motion.Glue
public import Motion.Smooth
public import Motion.Transforms
public import Motion.Compose
public import Motion.Plan.Conservative
public import Motion.General
public import Motion.MoveJ
public import Motion.Sync
public import Motion.Supervisor

/-!
# Motion

Jerk-limited motion control: cubic profiles, feasibility, the conservative rational
planner, general boundary conditions, stretching, synchronization, the scalar MoveJ,
the supervisor's kinematic lemma and the composition bound.

The optimal 7-phase planner is implemented and golden-tested in Rust; its Lean proofs
are staged (`docs/motion_control.md` §4.7). Importing `Motion` is the public entry point.
-/

@[expose] public section

namespace Motion

end Motion
