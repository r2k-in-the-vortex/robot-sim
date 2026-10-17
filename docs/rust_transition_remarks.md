# The Rust transition: remarks and record

This is the record of moving the simulator from Python to Rust: what was built, what was
decided, what was measured, and what is still open. It is written for whoever picks this up
next, so it says where the bodies are buried rather than only what works.

Companion documents, both in this directory:

- [`verification.md`](verification.md) — what is proved, what is tested, and what is
  neither, with the reasoning for each boundary.
- [`lean-rust-map.md`](lean-rust-map.md) — the Lean definition and theorem correspondence,
  function by function, with a blank in the Test column meaning a gap that has been noticed
  rather than hidden.

## Why the port

Three reasons, in descending order of importance.

**The endgame is real-time robot control.** The kinematics is not only a viewer's engine;
it has to be adaptable into a control loop. That constrains the core hard — plain `f64`, no
heap allocation, no panics, fixed-size buffers, deterministic results — and it is the
constraint the whole architecture is shaped around. The 3D application is the development
and demonstration surface for that core, not the point of it.

**The 3D view was a software rasteriser.** `matplotlib`'s `mplot3d` drawing seven binary
STLs totalling ~20 MB and ~425k triangles as `Poly3DCollection` patches, with per-face
colour arrays computed in Python. A GPU renderer is a large and immediate win.

**The force/torque model had no implementation anywhere.** `test_force_torque.py` said so
outright: "the transforms themselves are not implemented in Python yet (`kinematics.py` has
no sensor frame)". The 29 exact-rational cases in `test_data/force_torque_frames.json` were
golden data waiting for an implementation. Rust is where that landed.

## What exists now

Seven crates, ~18,900 lines, plus 1,625 lines of new Lean.

| Crate | Contents |
| --- | --- |
| `robot-kinematics` | DH transforms, forward chain, closed-form inverse solver |
| `robot-dynamics` | Wrench frame algebra, gravity and inertia compensation |
| `robot-model` | Parameter types and `robot_parameters.json` persistence |
| `robot-app` | Bevy + egui desktop application |
| `robot-golden` | Exact rational arithmetic and the Lean numeral format, for tests |
| `xtask` | `cargo xtask gen-golden` / `check-golden` |
| — | `lean/KinematicsTestData.lean`, `lean/BranchDecisionQ.lean`: two new generators |

The Python is **unchanged and still passing**. It is the reference for behaviour and a
frozen regression oracle, not a thing being deleted.

## Architecture decisions worth knowing

### `Pose` is a rotation and a translation, not a 4x4

`lean/Kinematics.lean`'s `Pose` is `{R : Matrix (Fin 3) (Fin 3) ℝ, p : Fin 3 → ℝ}`, and the
Rust mirrors it. `Pose.toMatrix4` proves the two views carry the same data, so the
homogeneous matrix `mathematics.md` writes out can be built at the end rather than carried
through the algebra. The same reasoning runs through the whole port: Lean's types are the
Rust's types, and function names are the Lean names in snake case, so the correspondence is
greppable rather than a matter of memory.

### The `Field`/`Scalar` split is the load-bearing decision

This is the one to understand before changing anything.

Lean states the specification over `ℝ`. The Rust states it over two traits:

- **`Field`** — the four operations, nothing else. Every use the forward chain makes of an
  angle is through its cosine and sine (`dh_congr`, `fk_congr`), so once those are supplied
  as *data* — the `CosSin` type — the whole forward chain is a polynomial in them. A
  polynomial evaluates over any commutative ring, so this layer runs unchanged over the
  exact rationals the Lean generators emit.
- **`Scalar: Field`** — adds `sqrt`, `sin`, `cos`, `atan2`, `acos`. This is where Rust and
  the real-number specification genuinely part company, and it is deliberately a small,
  nameable set of functions.

The point is not abstraction for its own sake. It is that the boundary between "exactly
checkable" and "approximately checkable" is **in the type system**, so it cannot drift.
`tests/exact_ring.rs` evaluates the same `fk_cs` the application calls over an exact
rational type, with `RᵀR = I` holding on the nose.

Production instantiates `f64` and nothing else, so every call monomorphises to a plain
floating-point instruction. The genericity costs nothing at runtime.

### The solver is two functions, and which half a theorem is about matters

```rust
// Lean's `solutions` verbatim: total, tolerance-free, NO pose filter.
// `fk_of_mem_solutions`, `exists_solution_angles_eq`, `solutions_ne_nil` and
// `length_solutions_le_eight` are about THIS function.
pub fn solutions<S: Scalar>(g: &Geometry<S>, target: &Pose<S>, out: &mut SolutionSet<S>);

// The `kinematics.py`-compatible layer: widened predicates, the flat wrist
// candidate at the singularity, and the FK pose filter. The app calls only this.
pub fn solve<S: Scalar>(g, target, &Tolerances, out: &mut SolutionSet<S>);
```

Lean and `kinematics.py` differ deliberately in three ways, spelled out at
`InverseKinematics.lean:31`: Lean has no tolerances, no pose filter, and at the wrist
singularity returns only the `θ4 = 0` flat pair where Python also offers the mirrored one.
Merging the two would have meant the theorems describe "the solver, roughly". Splitting them
means `fk_of_mem_solutions` is a statement about a named Rust function, and the Python
compatibility is an explicit layer that declares every threshold it adds.

### The fixed-capacity candidate buffer is a proof paying for itself

`SolutionSet` holds at most eight candidates in an array and sets an overflow flag rather
than growing or panicking, because `length_solutions_le_eight` is a *theorem*. That is what
makes the control path allocation-free, and — being a control loop — a divergence from the
specification must not bring the process down.

The corollary is instructive: the bound applies to `solutions`, but Python's singularity
handling appends candidates before filtering, so `solve` can legitimately offer more than
eight. There is a test pinning that.

## How the Lean formulation is actually used

**The Lean is a specification, not an implementation.** `Kinematics`, `Zyz`, `Atan2` and
`InverseKinematics` are all `noncomputable` over `ℝ`; nothing in them is executable.
`TorqueWrench` and `Dynamics` are stated over an arbitrary `CommRing α`, so they *are*
evaluable. There are no `sorry`s, no `axiom`s, no `@[export]`, no FFI surface.

Three things follow, and each is used:

1. **Where the mathematics is polynomial, Lean generates exact vectors and Rust compares
   with `==`.** No tolerance anywhere, so a disagreement is a real disagreement rather than
   floating-point drift. This covers the forward chain, the wrench algebra and the dynamics.
2. **Where it is transcendental, each theorem becomes an executable property.** The
   statement says what the code must satisfy; the test checks that it does.
3. **Where a decision is a comparison, Lean decides it exactly and Rust is compared against
   the result.** See below.

### Why a proof cannot simply be moved across

Worth recording, because it is the first thing anyone asks.

- **Lean → Rust FFI is blocked twice over.** There is nothing computable to link (`ℝ` in
  Mathlib is a quotient of Cauchy sequences with no runtime representation, so the code
  generator refuses to compile `fk`, `solutions` or `Real.atan2` at all — the
  `.lake/build/ir/*.c` files are a red herring, being per-module IR for the computable
  scaffolding and the proofs). And there is no export surface: no `@[export]` anywhere, no
  `.so`/`.a`/`.dll` under `.lake/build`.
- **Rust → Lean extraction (Aeneas/Charon) is unavailable.** Charon rejects `f32`/`f64` at
  translation time with "Floats are not supported yet", even when floats appear only in an
  unused signature. The entire Rust kinematics is `f64`.
- **And it would not be enough even so.** Aeneas models Rust scalars as *bitvectors*, so
  connecting that to the `ℝ` specification requires proving the `f64` computation
  approximates the real-number chain — a rounding-error analysis, which is a different and
  much harder theorem than anything in the tree. Extraction never supplies that bridge.
- **A `ℚ` restatement would help, and not enough.** It would make the rational subset
  computable and exportable, moving FFI from impossible to merely inadvisable. But the
  closed-form solver **cannot** be restated over `ℚ` as an angle-valued function: `atan2`,
  `arccos` and — by Niven's theorem — `cos` and `sin` of a rational degree measure are
  irrational outside a handful of values. That is arithmetic, not engineering.

So the transfer mechanism is **theorems as executable properties**, plus exact vectors where
the mathematics permits. That is strong validation. It is not a proof about the `f64` code,
and nothing here pretends otherwise.

### The exact-decision layer, and a correction

Lean decides degeneracy with exact predicates; `f64` cannot. Every tolerance-bearing
decision is therefore confined to one trigonometry-free module (`branch.rs`) which turns a
handful of scalars into a `BranchPlan`. Each threshold is a named field of `Tolerances`
carrying a comment naming the Lean predicate it stands in for, and no other float comparison
in the crate is tolerance-bearing.

An early claim in planning — that every predicate reduces to a rational comparison — was
**too strong**, and the correction is worth recording because it is easy to repeat. Most do:
`hypot(x,y) = 0` holds exactly when both are zero, so the wrist-singularity test needs no
square root at all. But the reachability band does not. `elbowCosine` expands to

```
ρ − 2σ·a₁·r + a₁² + h²     with ρ = x₄² + y₄² rational and r = √ρ
```

so the band test lives in the quadratic extension **ℚ(√ρ)**. `lean/BranchDecisionQ.lean`
carries the radical and splits on its coefficient's sign; the corpus includes the band edges
at both ends, a hair either side, ρ = 0, and a non-square radius. The ℝ development is
untouched — the mirror is a restatement that imports `InverseKinematics` and defines nothing
in it.

This layer found no disagreements. Its direct yield is confidence, not a bug. But its
self-check — refuse to write on failure, then re-derive the band the long way through
`elbowCosine` — caught three transcription errors of the generator's own at the upper edge.

## Measured results

Everything below was re-run after the last edit, with the agents stopped.

| Gate | Result |
| --- | --- |
| `cargo test --workspace` | 318 passed, 0 failed |
| Python suite | 46 passed, unchanged |
| `cargo clippy --workspace --all-targets -- -D warnings` | clean |
| `cargo fmt --all --check` | clean |
| `cd lean && lake build` | Build completed successfully (2250 jobs) |
| `cargo xtask check-golden` | exit 0, all three corpora regenerated byte-identically |
| `cargo build -p robot-kinematics --no-default-features --features libm` | clean |
| Application launch | Vulkan on an RTX A1000, window created, no errors |

Two checks were *falsification* tests rather than green runs, because a passing suite proves
nothing on its own:

- Perturbing one numeral in `force_torque_frames.json` fails exactly the right test, and
  restoring it returns the file byte-clean.
- The Lean generators refuse to write on a failed self-check. Demonstrated live: fed a
  deliberately false claim, `kinematics_test_data` printed "refusing to write test data: a
  case failed its checks", exited 1, and created no file.

## Where the Rust deliberately differs from the Python

Each of these is intentional, visible, and recorded in place.

| Change | Reason |
| --- | --- |
| **Mesh scale `0.1`** | `simulator.py` applies no scale factor at all, so the meshes (millimetres, spanning hundreds) never actually lined up with the DH table (tens) |
| **Gizmo checkbox labels** | In the Python the labels are off by one — the box labelled *J1* toggles the *base* gizmo. The render side is right and the labels are wrong |
| **Save/Load open a chooser** | The Python writes beside the script; a compiled binary has no script directory |
| **LF not CRLF on write** | Python's `write_text` is text mode and translates on Windows; the Rust writes the bytes Python's `json.dumps` would have produced |
| **`Copy XYZ` raises on an invalid table** | The Python cannot fail there, since its `forward_kinematics` accepts any table |
| **Pose jogs keep a joint's winding** | The Python stores the solver's angles as they come, wrapped into `(-180°, 180°]` (`_apply_joint_solution`'s `math.degrees`, `simulator.py:343-353`), so a J6 held at 400° comes back at 40° and the arm spins a whole turn. The Rust places the chosen candidate beside the angles the arm holds, and the readout and clipboard name the turns it carries |

The JSON itself is **byte-identical** to `json.dumps(data, indent=2) + "\n"`, verified with
`cmp` rather than asserted: 2216 bytes each way. Runtime joint angles are *structurally*
unsaveable, because `Document` has no field for them.

### The solver's divergences from `kinematics.py`

Three are documented in the Lean. A **fourth** was found by measurement and is documented in
`ik.rs` and pinned by a test, not smoothed over: at the fold-back target — wrist centre
exactly on the frame-1 origin, `elbowCosine = -1` exactly — Python returns 12 candidates and
`solve` returns 8 with `overflowed()` set. The cause is rounding at a measure-zero target:
the two implementations conjugate the target by expressions that round differently, so their
splits of joints 4 and 6 land apart and the pose check keeps a different one.

A finding in the other direction: the *inner* band edge can never be widened by tolerance,
because `hypot ≥ 0` and `|L₁ − L₂| ≥ 0` together mean the cosine cannot undershoot −1. So
Python's `-1 - 1e-7` window admits nothing the exact test rejects.

## Gotchas found the hard way

**Six of the seven shipped STLs begin with the ASCII bytes `solid ` and are binary.** A
`starts_with("solid")` sniff gets them exactly backwards. The only reliable discriminator is
the size: a binary STL is precisely `84 + 50n` bytes with `n` at offset 80. The loader
classifies by size alone and forces the binary path by clobbering six header bytes on an
in-memory copy — safe because `stl_io`'s binary reader reads the 80-byte header only to
discard it.

**`.gitattributes` pinning `test_data/*.json` to LF is load-bearing, not cosmetic.** The
drift gate asserts `git diff --exit-code`, and on a Windows checkout with `core.autocrlf`
the regenerated file comes back CRLF — all 822 lines differ where the bytes agree.

**Lean's `θ : Fin 6 → ℝ` is 0-based.** `θ 4` is the *fifth* joint, `mathematics.md`'s θ5. So
`NonDegenerate`'s `sin (θ 4) ≠ 0` is the joint-5 singularity, and
`wristRotation (θ 3) (θ 4) (θ 5)` is joints 4, 5, 6. The Rust array is 0-based to match, but
every comment has to say which numbering it means.

**`fk_R_orth` and `fk_R_det` are in `InverseKinematics.lean`, not `Kinematics.lean`.** An
agent searched only the latter and wrote "these do not exist" into a file header. Worth
knowing because the planning notes repeated the error from a summary rather than the source.

**The shipped table has a 90° static theta offset on joint 2**, so "zero runtime angles" is
not the zero angle vector. Any port assuming zero offsets computes a different pose.

**The 3D mesh and the DH table were never at the same scale.** `robot_parameters.json` also
ships with every mesh path empty, so nothing loads at startup in either implementation.
"0 mesh(es) configured" is correct reference behaviour, not a bug.

**Bevy-specific, for whoever touches the app:** `EguiPrimaryContextPass` is not a schedule in
Bevy 0.20 — bevy_egui runs it from `PostUpdate` inside `EguiPostUpdateSet::EndPass`, which
forces the camera/overlay system ordering. Two cameras were mandatory rather than stylistic,
because egui derives its `screen_rect` from the primary context camera's physical viewport
and scissors the egui pass to it. And `ATTRIBUTE_COLOR` is used verbatim as linear
`base_color`, so sRGB face colours must be converted in `to_mesh` or every face washes out.

## Open, with honest status

1. **The ~200-bit differential layer is not built, and the obstacle is an earlier decision
   in this port.** `Scalar` is sealed to `f64`/`f32` inside `robot-kinematics`, on the
   reasoning that an unexercised fourth instantiation weakens the argument about which ones
   the suite covers — and that seal is exactly what stops a test crate supplying a
   high-precision scalar, which `solutions`/`solve` would need. Two ways out: implement the
   type *inside* the crate behind a test-only feature, keeping the seal but needing a
   GMP-backed dependency (awkward on Windows); or open the seal, which is two lines and
   gives the invariant up. Neither is done.

2. **CI has never run.** It is written — three jobs, the golden-drift gate folded into the
   Lean job so the 90-minute Mathlib cache is not paid twice, Bevy's Linux system
   dependencies listed — but nothing has been pushed, so it is unverified. This is the one
   deliverable that could not be checked.

3. **The two numeric solvers are absent.** `inverse_kinematics_position` and
   `inverse_kinematics_position_preserving_roll_yaw` are damped least squares over a
   Jacobian; `mathematics.md` excludes them from the specification and so does the port. The
   app never used them. Nothing needs them today.

4. **Joint limits are the caller's business.** Neither the specification, the Lean, nor the
   Python carries any. They belong in a caller-supplied constraint layer, not in the solver.

5. **There is no arm dynamics to verify.** `Dynamics.lean` is single-rigid-body Newton–Euler
   for the payload distal to the sensor — no mass matrix, no Jacobian, no joint torques, and
   `robot_parameters.json` carries no masses or inertias. Anything in that direction is new
   mathematics with no specification behind it, and should be its own decision.

6. **The README's UI prose still describes the Python.** The four visible differences are
   documented in a section of their own, and the Jogging and Copy XYZ paragraphs now name the
   Rust's winding annotation as well; the rest is inherited and is accurate for the Python. It
   would be better rewritten against the Rust once someone has driven the interface by hand —
   the agent that built it could not exercise dialogs or the clipboard headlessly, so those
   two are the parts with the least evidence behind them. The winding annotation has since
   been driven by hand — J6 jogged to 400°, a one-unit X jog, the front readout and the
   clipboard read back — so that path at least now has evidence behind it; the dialogs still
   have none.

## If you are picking this up

Start with `docs/verification.md`. It explains what each kind of check in this repository is
worth, which is the thing that is easiest to get wrong about a port like this — the suites
look uniform and they are not: some compare exact rationals with `==`, some restate theorems
as properties with declared tolerances, and one of them is a bounded model check. Treating
them as interchangeable would give a false impression of the whole.

Then `docs/lean-rust-map.md` to find the Lean counterpart of anything you are about to
change. If you add a theorem, add its row and its test. If you cannot, leave the row blank —
the blanks are the useful part.
