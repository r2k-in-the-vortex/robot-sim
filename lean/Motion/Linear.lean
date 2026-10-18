module
-- The declarations in this file are exported (`@[expose] public section`), so
-- everything their types and bodies mention has to be part of the public interface.
public import Motion.Basic
public import Kinematics
public import InverseKinematics
public import Atan2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Matrix
open scoped Matrix

noncomputable section

@[expose] public section

/-!
# Linear (Cartesian straight-line) motion: the sampled specification

This module is the Lean vocabulary of the `lin` command specified in
`docs/motion_control.md` §5.6. A `LinearPath` is the affine interpolation of the tool
position from `start.p` to `stop.p`, together with an orientation function
`rotation : ℝ → Matrix (Fin 3) (Fin 3) ℝ`. The orientation interpolation is **supplied
data**: §5.6 leaves the choice between slerp, axis-angle and any other rotation path open,
so this module requires only the two endpoint laws and that every value is a rotation.

The rest of the module is the sampled, numerical contract of §5.6. `SampledTrajectory`
stores a sample count, a positive time step and one joint configuration per sample;
`velocity`, `acceleration` and `jerk` are forward finite differences of those samples.
`SampledSolutions` pairs a trajectory with one closed-form IK candidate per sample. The
four checks are

* `SamplesAreSolutions`: each chosen candidate is a member of `Kinematics.solutions` at the
  sampled pose;
* `SamplesOnPath`: forward kinematics of each stored configuration is the sampled pose;
* `BranchContinuous`: consecutive shoulder/elbow labels agree and every wrapped joint step
  is at most `maxStep`;
* `WithinSampledLimits`: the finite-difference V/A/J samples respect the per-joint limits.

`LinPlan` conjoins them with the requirement that the path connects the command's
endpoints, and `HasLinPlan` is the existential definition of a sampled plan.

There is deliberately no theorem in this module, only definitions and predicates. In
particular, nothing here asserts that `HasLinPlan` holds for any geometry, command or
sampling tolerance. The feasibility decision is the numerical, sampled check described in
§5.6: sample the Cartesian path, solve each sample with the existing closed-form IK, reject
an unreachable sample or a branch discontinuity, and check the joint limits on the sampled
trajectory. Finite differences bound the sampled sequence, not the motion between samples.
The M5 `cartesian_path_feasible` certificate remains future work, and this module does not
claim it.
-/

namespace Motion

/-- `R` is a rotation: orthogonal and orientation-preserving. These are exactly the
rotation hypotheses of `Kinematics.fk_of_mem_solutions`. -/
def IsRotation (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  Rᵀ * R = 1 ∧ R.det = 1

/-- A Cartesian straight-line path: affine translation from `start` to `stop`, with the
orientation path supplied by the caller. The rotation interpolation is data because
`docs/motion_control.md` §5.6 deliberately leaves slerp vs axis-angle open. -/
structure LinearPath where
  start : Kinematics.Pose
  stop : Kinematics.Pose
  rotation : ℝ → Matrix (Fin 3) (Fin 3) ℝ
  rotation_zero : rotation 0 = start.R
  rotation_one : rotation 1 = stop.R
  rotation_isRotation : ∀ s : ℝ, IsRotation (rotation s)

namespace LinearPath

/-- The affine position interpolation. -/
def position (P : LinearPath) (s : ℝ) : Fin 3 → ℝ :=
  fun i => (1 - s) * P.start.p i + s * P.stop.p i

/-- The Cartesian pose at path parameter `s`. -/
def pose (P : LinearPath) (s : ℝ) : Kinematics.Pose :=
  ⟨P.rotation s, P.position s⟩

end LinearPath

/-- The command data: the two endpoint poses and the per-joint limits. -/
structure LinCommand where
  start : Kinematics.Pose
  stop : Kinematics.Pose
  limits : Fin 6 → Limits

/-- A uniformly sampled joint trajectory. Samples are indexed `k = 0, …, count - 1`;
`two_le` guarantees at least the two samples the finite differences need. -/
structure SampledTrajectory where
  count : ℕ
  two_le : 2 ≤ count
  dt : ℝ
  dt_pos : 0 < dt
  angles : ℕ → Fin 6 → ℝ

namespace SampledTrajectory

/-- Sample time `k * dt`. -/
def time (S : SampledTrajectory) (k : ℕ) : ℝ := (k : ℝ) * S.dt

/-- Path parameter of sample `k`: `k / (count - 1)`, so sample `0` is `0` and sample
`count - 1` is `1`. -/
def parameter (S : SampledTrajectory) (k : ℕ) : ℝ :=
  (k : ℝ) / ((S.count - 1 : ℕ) : ℝ)

/-- Forward finite-difference joint velocity between samples `k` and `k + 1`. -/
def velocity (S : SampledTrajectory) (k : ℕ) (i : Fin 6) : ℝ :=
  (S.angles (k + 1) i - S.angles k i) / S.dt

/-- Forward finite-difference joint acceleration. -/
def acceleration (S : SampledTrajectory) (k : ℕ) (i : Fin 6) : ℝ :=
  (S.velocity (k + 1) i - S.velocity k i) / S.dt

/-- Forward finite-difference joint jerk. -/
def jerk (S : SampledTrajectory) (k : ℕ) (i : Fin 6) : ℝ :=
  (S.acceleration (k + 1) i - S.acceleration k i) / S.dt

end SampledTrajectory

/-- Two real angles denote the same joint angle: they differ by a whole number of turns. -/
def SameAngle (a b : ℝ) : Prop := (a : Real.Angle) = (b : Real.Angle)

/-- A sampled trajectory together with one closed-form IK candidate per sample. The stored
angles are a continuous representative of the chosen candidate: they agree with it modulo a
full turn, so their raw forward differences are the commanded joint motion. -/
structure SampledSolutions where
  trajectory : SampledTrajectory
  solution : ℕ → Kinematics.Solution
  angles_eq : ∀ k (i : Fin 6), SameAngle (trajectory.angles k i) ((solution k).angles i)

/-- Every chosen candidate is in the closed form's list at the sampled pose. -/
def SamplesAreSolutions (g : Kinematics.Geometry) (path : LinearPath)
    (Sol : SampledSolutions) : Prop :=
  ∀ k, k < Sol.trajectory.count →
    Sol.solution k ∈ Kinematics.solutions g (path.pose (Sol.trajectory.parameter k))

/-- The forward kinematics of every stored sample is the sampled Cartesian pose. -/
def SamplesOnPath (g : Kinematics.Geometry) (path : LinearPath)
    (Sol : SampledSolutions) : Prop :=
  ∀ k, k < Sol.trajectory.count →
    Kinematics.fk g (Sol.trajectory.angles k) =
      path.pose (Sol.trajectory.parameter k)

/-- Consecutive samples stay on one shoulder/elbow branch, and no joint moves more than
`maxStep` (modulo a full turn) between samples. -/
def BranchContinuous (Sol : SampledSolutions) (maxStep : ℝ) : Prop :=
  ∀ k, k + 1 < Sol.trajectory.count →
    (Sol.solution (k + 1)).shoulder = (Sol.solution k).shoulder ∧
    (Sol.solution (k + 1)).elbow = (Sol.solution k).elbow ∧
    (∀ i : Fin 6,
      |RealAtan2.wrap (Sol.trajectory.angles (k + 1) i -
        Sol.trajectory.angles k i)| ≤ maxStep)

/-- The forward finite-difference velocity, acceleration and jerk samples respect the
per-joint `Limits`. The index guards select exactly the differences whose samples exist. -/
def WithinSampledLimits (lim : Fin 6 → Limits) (S : SampledTrajectory) : Prop :=
  (∀ k, k + 1 < S.count → ∀ i, |S.velocity k i| ≤ (lim i).vmax) ∧
  (∀ k, k + 2 < S.count → ∀ i, |S.acceleration k i| ≤ (lim i).amax) ∧
  (∀ k, k + 3 < S.count → ∀ i, |S.jerk k i| ≤ (lim i).jmax)

/-- The complete sampled `lin` contract: endpoint match, the four checks, and the
per-joint limits. -/
def LinPlan (g : Kinematics.Geometry) (cmd : LinCommand) (path : LinearPath)
    (maxStep : ℝ) (Sol : SampledSolutions) : Prop :=
  path.start = cmd.start ∧ path.stop = cmd.stop ∧
  SamplesAreSolutions g path Sol ∧
  SamplesOnPath g path Sol ∧
  BranchContinuous Sol maxStep ∧
  WithinSampledLimits cmd.limits Sol.trajectory

/-- A sampled `lin` plan exists. This is a definition, not an assertion: nothing in this
module states it holds for any geometry, command or sampling tolerance. -/
def HasLinPlan (g : Kinematics.Geometry) (cmd : LinCommand) (maxStep : ℝ) : Prop :=
  ∃ (path : LinearPath) (Sol : SampledSolutions), LinPlan g cmd path maxStep Sol

end Motion
