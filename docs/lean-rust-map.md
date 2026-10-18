# Lean to Rust, definition by definition

The Lean development under `lean/` is the specification; the Rust under `crates/` is an
implementation of it. This file is the map between them, and it is the artefact to read
when asking whether the Rust still says what the Lean says.

Two rules keep it honest:

- **Function names mirror the Lean names**, so a correspondence is greppable rather than
  a matter of memory. Rust is `snake_case`; Lean is `camelCase`. Nothing else changes.
- **Every theorem gets a named Rust test**, or a row here saying why it does not. A blank
  in the *Test* column is a gap that has been noticed, not one that has been hidden.

`docs/verification.md` explains what kind of confidence each column is worth.

## Types

| Lean | Rust | Notes |
| --- | --- | --- |
| `Kinematics.Pose` (`{R, p}`) | `robot_kinematics::Pose` (`{r, p}`) | A rotation and a translation, not a 4x4 — `Pose.toMatrix4` proves the views agree, so `to_matrix4` can be built at the end |
| `Matrix (Fin 3) (Fin 3) α` | `robot_kinematics::Mat3` | Row-major; `at(i, j)` is Lean's `M i j` |
| `Fin 3 → α` | `robot_kinematics::Vec3` | |
| `Kinematics.Geometry` | `robot_kinematics::Geometry` | Lean's `linkOne_pos`/`linkTwo_pos` proof fields become the check in `Geometry::new` |
| `Fin 6 → ℝ` | `robot_kinematics::Angles` | **Lean's `θ` is 0-based**: `θ 4` is the fifth joint, `mathematics.md`'s θ5 |
| `InverseKinematics.Solution` | `robot_kinematics::Solution` | `shoulder`/`elbow` are `ℤ` in Lean, `i8` in Rust; no wrist label, because Lean records none |
| `TorqueWrench.Wrench`, `.Twist` | `robot_dynamics::{Wrench, Twist}` | |
| `TorqueWrench.Rotation` | `robot_dynamics::Rotation` | Bundles orthogonality *and* determinant one: the round trips need the first, `mulVec_cross` needs the second |
| `Dynamics.MassProperties` | `robot_dynamics::MassProperties` | Carries inertia symmetry, which `dot_mulVec_self` needs |

`Scalar`/`Field` have no Lean counterpart: they are the port's way of expressing which
half of the mathematics is polynomial. See `docs/verification.md`.

## `Kinematics.lean` → `robot-kinematics`

| Lean | Rust | Test |
| --- | --- | --- |
| `dh` | `Pose::dh` / `Pose::dh_cs` | `dh_matrix_matches_the_written_out_form` |
| `dhP` | `Pose::dh_translation_cs` | covered by the above |
| `Pose.mul` | `Pose::mul` (`Mul`) | `composition_matches_the_homogeneous_product` |
| `Pose.toMatrix4` | `Pose::to_matrix4` | `the_homogeneous_matrix_is_exact`, `the_homogeneous_matrices_match_the_lean_matrix4` |
| `joint` | `joint_transforms_cs` | `zero_pose_matches_the_documented_frame_origins`, `the_documented_zero_pose_matches_the_simulator` |
| `armPose` / `wristPose` / `fk` | `arm_pose_cs` / `wrist_pose_cs` / `fk_cs` | `fk_matches_the_lean_pose` |
| `carrierPose` | `carrier_pose_cs` | `carrier_pose_matches_the_lean_tower` |
| `armRotation` | `arm_rotation_cs` | `the_forward_rotation_factorises_through_frame_three` |
| `wristRotation` | `wrist_rotation_cs` | `the_forward_rotation_factorises_through_frame_three` |
| `wristCenter` | `wrist_center` | `wrist_center_matches_the_lean_wrist_center`, `the_wrist_centre_is_exact_and_at_the_fourth_frame` |
| `planarQ` / `planarH` | `PlanarTarget::{q, h}` | covered by the branch and IK suites |
| `elbowCosine` | `elbow_cosine` | covered by the branch and IK suites |
| `toMatrix4_mul` | — | `composition_matches_the_homogeneous_product` |
| `dh_congr` | — | `the_chain_reads_only_the_pairs` (the pairs *are* the input, so this is structural) |
| `fk_congr` | — | `the_forward_kinematics_is_invariant_under_a_full_turn` |
| `carrierPose_succ` / `_six` / `_four_p` | — | `the_sixth_carrier_pose_is_the_forward_kinematics`, `the_fourth_carrier_pose_is_the_wrist_center` |
| `fk_R` | — | `the_forward_rotation_factorises_through_frame_three` |
| `rotX_orth` / `rotY_orth` / `rotZ_orth` / `mul_orth` / `armRotation_orth` | — | `every_rotation_the_chain_produces_is_a_rotation` (checked by `rotation_is_a_rotation`, not by a proof) |
| `fk_R_orth` / `fk_R_det` | — | `every_rotation_the_chain_produces_is_a_rotation`. **Both live in `InverseKinematics.lean`, not `Kinematics.lean`** |

`dh_congr` and `fk_congr` have no Rust counterpart to test because the Rust never forms
an angle in the first place: `CosSin` is the input type, so "the chain depends on the
angle only through its cosine and sine" is true by construction rather than by proof.

## `TorqueWrench.lean`, `Dynamics.lean` → `robot-dynamics`

Every one of these is polynomial, so every test below compares exactly over `Ratio` with
`==`. `crates/robot-dynamics/tests/theorems.rs` names each test after its theorem.

| Lean | Rust |
| --- | --- |
| `tipToSensor` | `tip_to_sensor` |
| `sensorToTip` | `sensor_to_tip` |
| `sensorTwistToTip` | `sensor_twist_to_tip`, `sensor_twist_to_tip_velocity` |
| `tipTwistToSensor` | `tip_twist_to_sensor` |
| `virtualWork` | `virtual_work` |
| `tipToSensor_comp` / `sensorTwistToTip_comp` | `tip_to_sensor_comp`, `sensor_twist_to_tip_comp` |
| `mulVec_cross` | `mul_vec_cross` — where `det = 1` earns its place |
| `det_rotate` | `det_rotate` |
| `comAccel` | `com_accel` |
| `inertialWrench` | `inertial_wrench` |
| `gravityWrench` | `gravity_wrench` |
| `firstMoment` / `originInertia` | `first_moment`, `origin_inertia`, `parallel_axis_inertia` |
| `spatialInertialWrench` / `spatialGravityWrench` | `spatial_inertial_wrench`, `spatial_gravity_wrench` |
| `tipMassToSensor` / `sensorMassToTip` | `tip_mass_to_sensor`, `sensor_mass_to_tip` |
| `sensorAccelToTip` / `tipAccelToSensor` | `sensor_accel_to_tip`, `tip_accel_to_sensor` |
| `measuredWrench` | `measured_wrench` |
| `recoveredContactWrench` | `recovered_contact_wrench` |

| Theorem | Test |
| --- | --- |
| `virtualWork_invariant` | `virtual_work_invariant` |
| `sensorToTip_tipToSensor` / `tipToSensor_sensorToTip` | same names |
| `sensorTwistToTip_tipTwistToSensor` / `tipTwistToSensor_sensorTwistToTip` | same names |
| `mulVec_cross`, `transpose_mulVec_cross`, `rotation_cross_transpose` | same names |
| `mulVec_dot_product`, `cross_dot_product_eq_det`, `det_rotate` | same names |
| `tipToSensor_comp`, `sensorTwistToTip_comp` | same names |
| `sensorAccelToTip_comp`, `sensorMassToTip_comp` | same names |
| `comAccel_transport`, `inertialWrench_transport`, `gravityWrench_transport` | same names |
| `dot_mulVec_self` | `dot_mul_vec_self` |
| `virtualWork_inertialWrench`, `virtualWork_gravityWrench` | same names |
| `inertialWrench_origin_form`, `gravityWrench_firstMoment` | same names |
| `spatialInertialWrench_add`, `spatialGravityWrench_add`, `inertialWrench_add`, `gravityWrench_add` | same names |
| `measuredWrench_static`, `measuredWrench_at_rest` | same names |
| `recoveredContactWrench_measuredWrench`, `recoveredContactWrench_at_rest` | same names |

Not given separate tests, deliberately: the proof-support ring lemmas (`add_cross`,
`cross_add`, `smul_cross`, `cross_smul`, `cross_neg`, `sub_cross`, `cross_sub`,
`dot_eq_dotProduct`, `cross_eq_crossProduct`, `dotProduct_basisVec`,
`add_sub_sub_add_cancel`). They are internal steps of the proofs above rather than laws
of the model. `virtualWork_invariant_real` is the `ℝ` instantiation of
`virtualWork_invariant`; the rational instance is what the test evaluates.

## `Zyz.lean`, `Atan2.lean`, `InverseKinematics.lean` → `robot-kinematics`

The solver splits in two, and which half a theorem is about matters:

- **`solutions`** is Lean's `solutions` verbatim — total, tolerance-free, no pose filter.
  `fk_of_mem_solutions`, `exists_solution_angles_eq`, `solutions_ne_nil` and
  `length_solutions_le_eight` are all about *this* function.
- **`solve`** is the `kinematics.py`-compatible layer over it: widened predicates, the flat
  wrist candidate at the singularity, and the forward-kinematics pose filter. The app calls
  only this one.

| Lean | Rust |
| --- | --- |
| `solutions` | `ik::solutions` |
| `candidateAngles` | `ik::solve` (shared branch construction) |
| `shoulderAngle`, `planarTargetQ/H`, `elbowCosine`, `elbowAngle`, `elbowTheta2/3` | `branch::BranchPlan`, `ik::solutions` |
| `elbowBranches` | `branch::ElbowBranches` — all-or-nothing, so `+1`-only is unrepresentable |
| `wristSine`, `wristCosine`, `wristIsSingular` | `branch::WristPlan`, `zyz::hypot_third_column`, `zyz::cosine_third_entry` |
| `wristReadTheta4/6`, `wristReadTheta6Flat` | `zyz::read_theta4/5/6`, `zyz::read_theta6_flat` |
| `NonDegenerate` | `branch::Degeneracy` |
| `RealAtan2.hypot`, `.atan2`, `.wrap` | `Scalar::hypot`, `Scalar::atan2`, `units::wrap_angle` |
| `Real.Angle` equality (modulo a full turn) | `units::wrap_angle` on the difference — the *canonical* representative of each angle; `units::nearest_representative` moves between the members the equality identifies and `units::turn_index` names how many turns apart they are |
| `RealAtan2.nearestRepresentative` | `units::nearest_representative`, and `Solution::representative_near` for the lift from one angle to a whole configuration. **Argument order differs**: Lean is `(r a)` = (reference, angle), Rust `(angle, reference)` |
| `RealAtan2.turnIndex` | `units::turn_index` (`ℤ` in Lean, `i32` in Rust; the saturating cast on a non-finite angle has no Lean counterpart, where every real has a winding) |

| Theorem | Test |
| --- | --- |
| `fk_of_mem_solutions` | `fk_of_mem_solutions_on_commanded_configurations`, `degenerate_targets_are_still_sound`, `the_rotation_hypothesis_is_load_bearing` |
| `exists_solution_angles_eq` | `exists_solution_angles_eq_on_a_grid`, `the_recovery_is_not_vacuous`, and one `the_*_clause_is_load_bearing` per clause of `NonDegenerate` |
| `solutions_ne_nil` | `solutions_ne_nil_for_every_configuration` |
| `length_solutions_le_eight` | `length_solutions_le_eight_for_arbitrary_targets` |
| `solutions_eq_nil_of_not_reachable` | same name, plus `the_orthogonality_hypothesis_is_load_bearing` |
| `exists_fk_eq_of_solutions_ne_nil` | same name |
| `exists_solution_sin_five_eq_zero` | `exists_solution_sin_five_eq_zero_at_the_reconstruction` |
| `wristRotation_reconstruct`, `_mirror`, `_flat` | `zyz::reconstruct*` and their unit tests |
| `wristRotation_hypot_third_column` | `zyz::hypot_third_column` unit test |
| `wristRotation_read_theta4/5/6_coe_angle` | `zyz::read_theta*` unit tests |
| `wristRotation_zero_middle`, `_pi_middle` | `the_flat_branch_holds_joint_four_at_zero` |
| the exact-predicate layer | `lean_branch_plans.rs`, compared `==` against `BranchDecisionQ.lean` |
| `turnIndex_spec`, `wrap_sub_turnIndex_mem` | `units::turn_index_names_whole_turns` |
| `nearestRepresentative_sub` | `units::placement_is_the_reference_plus_the_wrapped_difference` |
| `abs_nearestRepresentative_sub_le_pi` | `units::a_placement_never_moves_further_than_a_half_turn` |
| `nearestRepresentative_sub_le` | `units::a_placement_is_the_nearest_of_all_the_whole_turn_translates`, with `a_placement_never_moves_further_than_a_half_turn` as its `k = ±1` corollary |
| `nearestRepresentative_coe_angle` | no Rust counterpart to test: `Real.Angle` has none — see 6 below |

Not given separate tests, deliberately: `wrap_mem_Ioc` (the range `wrap` lands in),
`exists_eq_wrap_add_int_mul_two_pi` (the decomposition the index is read off),
`abs_le_abs_add_int_mul_two_pi` and `abs_wrap_le_abs_add_int_mul_two_pi` (the nearest
representative is the least of its whole-turn translates). They are the internal steps the
theorems above are proved from rather than separate laws of the model; the last two are
`nearestRepresentative_sub_le`'s content in the two spellings its proof passes through.

### Where this is weaker, and it is said out loud

1. **`exists_solution_sin_five_eq_zero`'s hypothesis is unreachable through `fk` in
   `f64`.** At a commanded `θ5 = 0` the recovered sine is rounding noise rather than zero,
   so the exact solver takes the read-back branch and only `solve`'s declared threshold
   reaches the flat candidate. The property is therefore exercised where it is true — the
   reconstruction layer, on a rotation whose third column *is* the z axis — and through
   `solve`. The test's doc comment says so.
2. **`exists_solution_angles_eq` is not bit-exact in `f64`**, and cannot be: it is a run of
   `atan2` and `acos` over already-rounded products. Labels are compared exactly and angles
   modulo 2π within a declared 1e-9; a 1e-3 perturbation proves the tolerance is not doing
   the solver's work.
3. **`fk_of_mem_solutions` holds for position always, and for orientation only away from
   the singularity** — at a genuinely singular target the read-back splits joints 4 and 6
   by O(1) while the position stays at ~1e-15. Encoded as a sine guard, with a non-vacuity
   assertion proving the guard excludes something.
4. **`solve` has a fourth divergence from `kinematics.py`**, beyond the three the Lean
   documents. At the fold-back target — wrist centre exactly on the frame-1 origin, so
   `elbowCosine = -1` exactly — Python returns 12 candidates and `solve` returns 8 with
   `overflowed()` set, dropping two. Cause is rounding: the two conjugate the target by
   expressions that round differently, and the splits of joints 4 and 6 land apart, so the
   pose check rejects one the other accepts. It is documented in `ik.rs` and pinned by
   `python_compat.rs` rather than papered over.
5. **The ~200-bit differential layer is not built.** `Scalar` is sealed to `f64` and `f32`
   inside `robot-kinematics`, so no test crate can supply a high-precision scalar, and
   `solutions`/`solve` need `Scalar`. `Field` is open, which is what the exact `Ratio`
   corpus uses. Unblocking it means either implementing the type inside the crate behind a
   feature or opening the seal; neither was done here.
6. **Two rows have no test that is the theorem itself.** `nearestRepresentative_coe_angle`
   is structural: `Real.Angle` has no Rust counterpart, so what the Rust has instead is the
   numerical shadow of it in
   `units::placement_is_the_reference_plus_the_wrapped_difference` — placed and solved angles
   agree to `1e-12` in what a pose can see, not exactly by construction. The pair
   `turnIndex_spec` / `wrap_sub_turnIndex_mem` is exercised at a spread of angles where the
   index is known (`units::turn_index_names_whole_turns`), not by recomputing the
   decomposition identity there, which would be an `f64` equality and would need a tolerance
   the Lean statement does not have. (`nearestRepresentative_sub_le` was the third and is no
   longer among them: `units::a_placement_is_the_nearest_of_all_the_whole_turn_translates`
   asserts `|placed − reference| ≤ |angle + 2πk − reference|` over `k ∈ [−7, 7]` directly, and
   `units::a_placement_never_moves_further_than_a_half_turn` remains the `k = ±1` corollary
   a jog actually meets.)

## Ground truth

| Generator | Data | Consumed by |
| --- | --- | --- |
| `lean/KinematicsTestData.lean` | `test_data/kinematics_frames.json` | `crates/robot-kinematics/tests/lean_ground_truth.rs` |
| `lean/ForceTorqueTestData.lean` | `test_data/force_torque_frames.json` | `crates/robot-dynamics/tests/force_torque_ground_truth.rs` |
| `lean/MotionTestData.lean` | `test_data/motion_profiles.json` | `crates/robot-motion/tests/golden_motion.rs` |

All are outside `defaultTargets`, so `lake build` stays a pure proof build. All
self-check every case by evaluation and **refuse to write on failure** — a guard that was
demonstrated live rather than assumed. `cargo xtask check-golden` regenerates them and
asserts the committed data has not drifted.

## Motion

`lean/Motion/` is the specification; `crates/robot-motion` implements it. The
polynomial layer (`State`, `Segment`, `Profile`, evaluation, stretch, synchronize) is
`Field`-generic on the Rust side, so `Profile<Ratio>` runs the same code as production and
the exact goldens compare with `==`.

| Lean | Rust | Test |
| --- | --- | --- |
| `Motion.evalFrom` / `Profile.stateAt` | `Profile::eval` | exact-rational samples in `golden_motion.rs` |
| `Motion.Feasible` / `SafeFrom` | `Profile::from_parts` validation + planner checks | property and golden tests |
| `Motion.comp_bounds` | — | `composition_bounds` (the chain rule and triangle inequality are tested through the Cartesian certificate; see the M5 map below) |
| `Motion.comp_bounds_on_feasible` | — | no direct counterpart: the supervisor applies the bound per constant-rate interval |
| `Motion.planRestConservative` | `plan_rest_conservative` | `golden_motion.rs` conservative cases (exact `Ratio`) |
| — (M1-opt Lean proofs staged; Rust only) | `plan_rest_to_rest` | `golden_motion.rs` optimal cases (tolerance) |
| `Motion.stopFeasible` / `Motion.viable` | `stop_feasible` / `viable` | reject cases and `tests/general.rs` |
| `Motion.stopProfile` / `Motion.startProfile` | `stop_profile` / `start_profile` | `golden_motion.rs` general cases (tolerance) |
| `Motion.planGeneral` | `plan_general` | `golden_motion.rs` general cases |
| `Motion.synchronize` | `synchronize` | `golden_motion.rs` sync cases (exact `Ratio`) |
| `Motion.movejScalar` | `plan_movej_scalar` | `tests/sync.rs` |
| — (the same composition with the M1-opt scalar profile; app-facing) | `plan_movej_scalar_optimal` | `tests/sync.rs` |
| `Motion.stall_error_grows` / `stall_error_crosses` | supervisor plant test | `tests/supervisor.rs` (the Rust side is a simulation; only the kinematic growth is a theorem) |

### Theorem map

**Structural layer (`Motion.Basic`, `Motion.Glue`, `Motion.Smooth`, `Motion.Transforms`)**

| Lean theorem | Meaning | Rust counterpart |
| --- | --- | --- |
| `evalFrom_zero`, `evalFrom_totalTime`, `Profile.stateAt_totalTime` | evaluation at the endpoints is the start/fold | `Profile::eval`, `Profile::end` |
| `endState_q`, `Segment.stateAt_*`, `Segment.exit_*` | closed forms for the cubic and the fold | `Segment::advance`, `Profile::phase_start` |
| `segmentSafe_bounds`, `bounds_of_safeFrom`, `jerk_bound_of_safeFrom`, `feasible_of_safeFrom` | endpoint certificates imply `Feasible` | planner validation and the golden maxima checks |
| `contDiff_piecewise_le`, `contDiff_piecewise_lt` | piecewise `C^n` gluing | — (proof layer) |
| `hasDerivAt_stateAt_q/v`, `deriv_evalFrom_q/v`, `iteratedDeriv_two_stateAt_q` | the cubic's derivatives are the state fields | `eval`'s derivative convention |
| `evalFrom_contDiff_q(_of_ne)` | a nonempty profile's position is globally `C²` | — (proof layer) |
| `evalFrom_template_v_nonneg` | the conservative template's velocity is nonnegative | monotonicity expectations in the golden tests |
| `Profile.totalTime_append`, `stateAt_append`, `feasible_append` | concatenation evaluation and feasibility | `Profile::append` |
| `Profile.stateAt_translate/mirror/stretch/reverse` | the four transforms' evaluation laws | `Profile::translate/mirror/stretch/reverse` |
| `Profile.totalTime_*`, `Profile.feasible_*` | the transforms preserve duration/feasibility under their stated hypotheses | the same Rust methods |
| `Profile.stretch_isRest`, `Profile.stretch_endState` | stretching preserves rest boundaries | `stretch` tests |

**M1-default (`Motion.Plan.Conservative`)** — all eight ladder theorems are proved, with no
`sorry`: `planRestConservative_boundary`, `_isRest`, `_feasible`, `_smooth`, `_monotone`,
`_totalTime_nonneg`, `_length_le`, `_shape`.

**M2 (`Motion.General`)**

| Lean theorem | Status |
| --- | --- |
| `stopProfile_feasible` | proved |
| `stopProfile_ends_at_rest` | proved |
| `startProfile_feasible`, `startProfile_starts_at_rest`, `startProfile_endState` | proved |
| `planGeneral_boundary`, `planGeneral_feasible`, `planGeneral_length_le` | proved |
| `planGeneral_isSome_iff` | proved (`isSome ↔ Viable`) |
| `stopFeasible_necessary` | **not formalised** — the necessity half needs a velocity-integral argument over arbitrary profiles; the constructive half and the exact `isSome_iff` above are the proved contract. This is the documented M2 gap, not a silent weakening. |

**M3 (`Motion.Sync`, `Motion.MoveJ`)**

| Lean theorem | Status |
| --- | --- |
| `hold_totalTime`, `hold_stateAt`, `hold_feasible`, `hold_isRest` | proved |
| `stretchTo_totalTime`, `stretchTo_feasible`, `stretchTo_isRest`, `stretchTo_endpoints` | proved |
| `syncTime_nonneg`, `totalTime_le_syncTime` | proved |
| `synchronize_feasible`, `synchronize_isRest`, `synchronize_totalTime`, `synchronize_endpoints`, `synchronize_rest_to_rest`, `synchronize_zero_motion`, `synchronize_all_zero` | proved |
| `synchronizedStop_totalTime`, `synchronizedStop_rest_at_Tmax`, `synchronizedStop_feasible`, `synchronizedStop_start` | proved |
| `movejScalar_boundary`, `movejScalar_boundary_of_moving`, `movejScalar_joint_boundary_of_moving`, `movejScalar_stationary`, `movejScalar_path`, `movejScalar_feasible` | proved |

`plan_movej_scalar_optimal` has no separate Lean definition. It is the same composition —
effective limits, one scalar profile, per-joint jerk scaled by `Δq_i` — with
`planRestToRest` in place of `planRestConservative`. The path, boundary and feasibility
theorems are about the composition; the optimal scalar profile itself carries the M1-opt
staging note below. The app uses the optimal entry point because the conservative
template's duration floor is about four seconds for any non-zero move.

**M4 and M5**

`Motion.Supervisor` proves `stall_error_grows` and its finite-time crossing corollary
`stall_error_crosses`; the supervisor's full decision logic (including command saturation)
is a headless simulation tested in `tests/supervisor.rs`, not a theorem. The M5 Cartesian
certifier remains a conditional construction: `Motion.comp_bounds` is proved, but the
sampled path-derivative bounds and `cartesian_path_feasible` are not implemented in Lean.

**M1-opt (staged).** The Rust `plan_rest_to_rest` (Cases A/A′/B/C, with `sqrt`/`cbrt`)
is implemented and golden-tested with the declared tolerance. The Lean proofs of the
radical cases are not part of this landing; `planRestConservative` is the verified default,
and the M1-opt gap is named in `docs/motion_control.md` §4.7.
