module
-- These are `public import`s because the declarations below are exported
-- (`@[expose] public section`): everything their types and bodies mention has to
-- be part of this module's public interface, or importers cannot use them.
public import Kinematics
public import Zyz
public import Atan2
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

open Matrix
open scoped Matrix
open RealAtan2

noncomputable section

@[expose] public section

/-!
# Inverse kinematics of the six-axis arm

This file is the Lean specification of `mathematics.md`'s inverse kinematics and of
`kinematics.py`'s `inverse_kinematics`: the closed-form solver written as a definition, and
the theorems that say it is correct. As in `Kinematics.lean`, angles here are **total DH
angles**, so the `theta_offset` split of `kinematics.py` never appears, and every statement
about recovered angles is modulo a full turn (`Real.Angle` equality) rather than modulo the
`(-pi, pi]` normalisation `_wrap_angle` performs.

Three deviations from `kinematics.py` are deliberate and worth naming, in the same spirit as
`Kinematics.lean`'s note on the theta-offset change of variable:

* **No tolerances.** `kinematics.py` uses `1e-7`/`1e-6` thresholds to absorb floating-point
  noise: `base_radius > tolerance`, `sine_five <= 1e-6`, the `-1-tol <= cosine <= 1+tol`
  reachability band, and a final pose check that discards any candidate whose forward
  kinematics misses the target. Over `ℝ` those become exact predicates (`r ≠ 0`,
  `sin theta5 ≠ 0`, membership in `Set.Icc (-1) 1`) and the pose check disappears, because
  the theorems below prove the candidates it would have tested are exact.
* **The pose filter is not mirrored.** A candidate is constructed and returned; nothing
  filters it. `fk_of_mem_solutions` is the statement that this changes nothing in exact
  arithmetic.
* **At the wrist singularity** the solver returns only the candidates that hold joint 4 at
  zero. See `wristIsSingular`, `wristTheta4` and `wristReadTheta6Flat`.

The correctness of the solver is therefore two halves. Soundness is `fk_of_mem_solutions`: every
candidate the list contains reproduces the pose it was computed from, exactly, and for any pose
whose rotation is a rotation. Completeness is `exists_solution_angles_eq`: a commanded
configuration outside the degenerate cases `NonDegenerate` names comes back among the candidates
with its own branch labels and with every angle equal modulo a full turn; the one degenerate case
that still comes back is the wrist singularity, where `exists_solution_sin_five_eq_zero` pins the
fourth joint at zero and returns the flat wrist. Around the two halves sit the coverage statements,
`solutions_ne_nil`, `length_solutions_le_eight` and `solutions_eq_nil_of_not_reachable`, which
describe the list rather than an angle in it - never empty on a pose the arm can reach, never longer
than the eight candidates the branch families generate, and empty exactly on the poses nothing
reaches.
-/

namespace Kinematics

/-! ## Candidate solutions -/

/-- One candidate the closed form returns: the six total DH angles, plus the branch labels
`kinematics.py` reports on `InverseKinematicsSolution`. The label `shoulder` is the sign
`sigma` that selects which side of the base axis the arm plane sits on, and `elbow` is the
sign of the second link's `psi`. -/
structure Solution where
  /-- The six total DH angles, 0-based: `angles 0` is `mathematics.md`'s `theta1`. -/
  angles : Fin 6 → ℝ
  /-- `1` or `-1`: the J1 plane orientation `sigma`. -/
  shoulder : ℤ
  /-- `1` or `-1`: the sign of the planar elbow angle `psi`. -/
  elbow : ℤ

@[ext] theorem Solution.ext {s t : Solution} (h : s.angles = t.angles)
    (hs : s.shoulder = t.shoulder) (he : s.elbow = t.elbow) : s = t := by
  cases s; cases t; simp_all

/-! ## A pose is its rotation together with its wrist centre

`kinematics.py` builds a candidate's arm angles from the *wrist centre* and its wrist angles
from the *rotation*, and never from the position directly. This lemma is what makes that
split legitimate: a pose whose rotation and wrist centre both match another's is that other
pose, because `wristCenter` already determines the position once the rotation is known.
-/

/-- A pose is recovered from its rotation and its wrist centre: `wristCenter` subtracts
`d6` along frame 6's z axis, so adding it back returns the translation. -/
theorem eq_of_R_eq_of_wristCenter_eq {g : Geometry} {T T' : Pose} (hR : T'.R = T.R)
    (hw : wristCenter g T' = wristCenter g T) : T' = T := by
  refine Pose.ext hR ?_
  -- `hw` says the two poses differ only by a term the equal rotations make equal, so
  -- adding that term back to both sides leaves the positions themselves.
  simp only [wristCenter] at hw
  rw [hR] at hw
  have h := congrArg (fun v => v + g.toolOffset • (T.R *ᵥ ![0, 0, 1])) hw
  simpa only [sub_add_cancel] using h

/-- The wrist centre's `x` component, named so the solver's formulas read like
`kinematics.py`'s `wrist_center[axis]`. -/
def wristX (g : Geometry) (T : Pose) : ℝ := wristCenter g T 0

/-- The wrist centre's `y` component. -/
def wristY (g : Geometry) (T : Pose) : ℝ := wristCenter g T 1

/-- The wrist centre's `z` component: the solver's `wrist_height` once `d1` is removed. -/
def wristZ (g : Geometry) (T : Pose) : ℝ := wristCenter g T 2

/-! ## The wrist's rotation, read off a target pose

The solver builds the wrist angles from `R_3^6` - the rotation the wrist itself has to
supply - which it obtains by undoing the arm's rotation. `Kinematics.fk_R` already records
that `R_0^6 = R_0^3 · R_3^6`, so this is the solver's side of that factorisation.
-/

/-- The wrist half of the chain is a rotation. `Kinematics` proves the arm half
(`armRotation_orth`) but not this one, and the reconstruction needs it to know that the
matrix it is decomposing is orthogonal. -/
theorem wristRotation_orth (θ4 θ5 θ6 : ℝ) :
    (wristRotation θ4 θ5 θ6)ᵀ * wristRotation θ4 θ5 θ6 = 1 := by
  simp only [wristRotation]
  exact mul_orth (mul_orth (rotZ_orth θ4) (rotY_orth (-θ5))) (rotZ_orth θ6)

/-- The whole chain's rotation is a rotation, in the `Aᵀ * A` direction `Kinematics.mul_orth`
builds. Stated for a pose that came out of `fk`, which is the only kind the solver is given. -/
theorem fk_R_orth (g : Geometry) (θ : Fin 6 → ℝ) : (fk g θ).Rᵀ * (fk g θ).R = 1 := by
  rw [fk_R]
  exact mul_orth (armRotation_orth (θ 0) (θ 1) (θ 2)) (wristRotation_orth (θ 3) (θ 4) (θ 5))

-- The elementary rotations are proper (determinant one), by direct expansion. These are
-- `@[simp]` because every determinant below is one `simp` away from them. The expansion
-- leaves `cos * cos + sin * sin = 1`, which `ring_nf` puts back into the squared form the
-- `@[simp]` Pythagorean lemma is stated in. (`;` rather than `<;>`: there is a single goal
-- here, and the `<;>` linter fires on that.)
@[simp] theorem det_rotX (α : ℝ) : (rotX α).det = 1 := by
  simp [rotX, Matrix.det_fin_three]; ring_nf; simp

@[simp] theorem det_rotY (θ : ℝ) : (rotY θ).det = 1 := by
  simp [rotY, Matrix.det_fin_three]; ring_nf; simp

@[simp] theorem det_rotZ (θ : ℝ) : (rotZ θ).det = 1 := by
  simp [rotZ, Matrix.det_fin_three]; ring_nf; simp

@[simp] theorem det_armRotation (θ1 θ2 θ3 : ℝ) : (armRotation θ1 θ2 θ3).det = 1 := by
  simp [armRotation, Matrix.det_mul]

@[simp] theorem det_wristRotation (θ4 θ5 θ6 : ℝ) : (wristRotation θ4 θ5 θ6).det = 1 := by
  simp [wristRotation, Matrix.det_mul]

/-- The chain's rotation has determinant one. Determinant one is not a consequence of
orthogonality - `Aᵀ * A = 1` only forces `det A = ±1` - so the handedness of the reconstruction
rests on this, read through `fk_R` from the two halves of the chain. -/
theorem fk_R_det (g : Geometry) (θ : Fin 6 → ℝ) : (fk g θ).R.det = 1 := by
  rw [fk_R, Matrix.det_mul, det_armRotation, det_wristRotation, one_mul]

/-- `R_3^6` as read off a target pose `T` at arm angles `θ1`, `θ2`, `θ3`: the target's
rotation with the arm's rotation divided out. -/
def relativeRotation (θ1 θ2 θ3 : ℝ) (T : Pose) : Matrix (Fin 3) (Fin 3) ℝ :=
  (armRotation θ1 θ2 θ3)ᵀ * T.R

/-- The relative rotation of a rotation is a rotation. This is the direction of
orthogonality `Kinematics.mul_orth` cannot produce - `A * Aᵀ = 1` rather than `Aᵀ * A = 1` -
which is why `Zyz.mul_transpose_eq_one_of_transpose_mul` exists. -/
theorem relativeRotation_orth {θ1 θ2 θ3 : ℝ} {T : Pose} (hT : T.Rᵀ * T.R = 1) :
    (relativeRotation θ1 θ2 θ3 T)ᵀ * relativeRotation θ1 θ2 θ3 T = 1 := by
  have hA : armRotation θ1 θ2 θ3 * (armRotation θ1 θ2 θ3)ᵀ = 1 :=
    mul_transpose_eq_one_of_transpose_mul (armRotation_orth θ1 θ2 θ3)
  -- `(Aᵀ R)ᵀ (Aᵀ R)` is `Rᵀ A Aᵀ R`, so reassociating puts `A Aᵀ` where it can collapse.
  rw [relativeRotation, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc (T.Rᵀ * armRotation θ1 θ2 θ3) (armRotation θ1 θ2 θ3)ᵀ T.R,
    Matrix.mul_assoc (T.Rᵀ) (armRotation θ1 θ2 θ3) (armRotation θ1 θ2 θ3)ᵀ, hA,
    Matrix.mul_one]
  exact hT

/-- The relative rotation inherits the chain's handedness: undoing the arm's rotation cannot
change a determinant. -/
theorem relativeRotation_det {θ1 θ2 θ3 : ℝ} {T : Pose} (hT : T.R.det = 1) :
    (relativeRotation θ1 θ2 θ3 T).det = 1 := by
  rw [relativeRotation, Matrix.det_mul, Matrix.det_transpose, det_armRotation, one_mul, hT]

/-! ## Non-degeneracy

The three poses `test_kinematics.py`'s `pose_pins_down_every_joint` refuses to assert angle
recovery for. Each is *solvable* - the closed form returns exact solutions for all of them -
but the pose does not determine every joint, so "the solver recovers the commanded angles"
is not a statement that can be made there. Stated on the commanded angles rather than on a
target pose, so that the hypotheses of the completeness theorem `exists_solution_angles_eq` name
exactly what that theorem assumes - nothing more, and nothing less:

* the wrist centre off the base axis (`a1 + q ≠ 0`, which is `r ≠ 0` - a wrist centre on the
  axis leaves the plane's azimuth, and so `theta1`, undetermined);
* not folded back onto the frame-1 origin with equal links (`L1 = L2 ∧ q = h = 0`, which
  leaves `theta2` undetermined);
* `sin theta5 ≠ 0`, since at the wrist singularity joints 4 and 6 share an axis and only
  `theta4 ± theta6` is observable - which is the one of the three the specification states
  outright, as `Zyz.wristRotation_zero_middle` / `wristRotation_pi_middle` (a joint 4 turned one
  way and a joint 6 the other give the same wrist). The other two are the derivations of
  `mathematics.md` §3 and §6, and they are why the completeness theorem `exists_solution_angles_eq`
  can claim the exclusion is exact rather than conservative: outside these three the pose does
  determine every joint, and every such configuration comes back.
-/
def NonDegenerate (g : Geometry) (θ : Fin 6 → ℝ) : Prop :=
  g.a1 + planarQ g θ ≠ 0 ∧ ¬(g.linkOne = g.linkTwo ∧ planarQ g θ = 0 ∧ planarH g θ = 0) ∧
    Real.sin (θ 4) ≠ 0

/-! ## The planar chain at an arbitrary second-link direction

`Kinematics.planarQ`/`planarH` describe the wrist centre relative to the frame-1 origin for
angles that came out of `fk`, and `planarU`/`planarV` are the same pair read relative to the
first link. The solver needs both at an arbitrary second-link direction `psi` and an
arbitrary first-link angle, since it is handed a target pose rather than a joint vector;
these are those general forms, and the `planarQ_eq_planarQAt` family records that the
specific ones are the general ones at `psi = theta 2 - pi / 2`.
-/

/-- The first link's length plus the second link's projection on it: the planar target's
radius relative to the first link. Generalises `planarU`. -/
def planarUAt (g : Geometry) (ψ : ℝ) : ℝ := g.linkOne + g.linkTwo * Real.cos ψ

/-- The second link's perpendicular offset: the planar target's height relative to the
first link. Generalises `planarV`. -/
def planarVAt (g : Geometry) (ψ : ℝ) : ℝ := g.linkTwo * Real.sin ψ

/-- The planar chain at an arbitrary first-link angle `θ₂` and second-link direction `ψ`:
the signed radial offset of the wrist centre from the frame-1 origin. Generalises
`planarQ`. -/
def planarQAt (g : Geometry) (θ₂ ψ : ℝ) : ℝ :=
  g.linkOne * Real.cos θ₂ + g.linkTwo * Real.cos (θ₂ + ψ)

/-- The vertical companion of `planarQAt`. Generalises `planarH`. -/
def planarHAt (g : Geometry) (θ₂ ψ : ℝ) : ℝ :=
  g.linkOne * Real.sin θ₂ + g.linkTwo * Real.sin (θ₂ + ψ)

@[simp] theorem planarU_eq_planarUAt (g : Geometry) (θ : Fin 6 → ℝ) :
    planarU g θ = planarUAt g (psi θ) := rfl

@[simp] theorem planarV_eq_planarVAt (g : Geometry) (θ : Fin 6 → ℝ) :
    planarV g θ = planarVAt g (psi θ) := rfl

@[simp] theorem planarQ_eq_planarQAt (g : Geometry) (θ : Fin 6 → ℝ) :
    planarQ g θ = planarQAt g (θ 1) (psi θ) := rfl

@[simp] theorem planarH_eq_planarHAt (g : Geometry) (θ : Fin 6 → ℝ) :
    planarH g θ = planarHAt g (θ 1) (psi θ) := rfl

/-- `(q, h)` in terms of `(u, v)`: the planar target seen from the first link is the target
seen from the base plane turned by the first link's angle. This is the general form of
`planarQ_eq`, and the direction the solver runs it - it is handed `(q, h)` and has to
recover the second link's direction. -/
theorem planarQAt_eq (g : Geometry) (θ₂ ψ : ℝ) :
    planarQAt g θ₂ ψ = planarUAt g ψ * Real.cos θ₂ - planarVAt g ψ * Real.sin θ₂ := by
  simp only [planarQAt, planarUAt, planarVAt, Real.cos_add]
  ring

theorem planarHAt_eq (g : Geometry) (θ₂ ψ : ℝ) :
    planarHAt g θ₂ ψ = planarUAt g ψ * Real.sin θ₂ + planarVAt g ψ * Real.cos θ₂ := by
  simp only [planarHAt, planarUAt, planarVAt, Real.sin_add]
  ring

/-- The law of cosines, read from the first link: the squared distance from the frame-1
origin to the wrist centre depends on the second link's direction only through its
cosine. It is what turns the measured distance into the elbow angle. -/
theorem planarUAt_sq_add_planarVAt_sq (g : Geometry) (ψ : ℝ) :
    planarUAt g ψ ^ 2 + planarVAt g ψ ^ 2 =
      g.linkOne ^ 2 + g.linkTwo ^ 2 + 2 * g.linkOne * g.linkTwo * Real.cos ψ := by
  simp only [planarUAt, planarVAt]
  nlinarith [Real.sin_sq_add_cos_sq ψ]

/-- The same identity whenever a candidate `psi` was chosen by its cosine, which is exactly
how the solver picks it: `psi = ± arccos c` enters the distance only through `c`. -/
theorem planarUAt_sq_add_planarVAt_sq_of_cos_eq (g : Geometry) {ψ c : ℝ}
    (h : Real.cos ψ = c) :
    planarUAt g ψ ^ 2 + planarVAt g ψ ^ 2 =
      g.linkOne ^ 2 + g.linkTwo ^ 2 + 2 * g.linkOne * g.linkTwo * c := by
  rw [planarUAt_sq_add_planarVAt_sq, h]

/-- The law of cosines at a configuration that produced the pose: the squared distance from
the frame-1 origin to the wrist centre depends on the second link's direction only through
its cosine. This is what makes the elbow angle recoverable from a target pose alone. -/
theorem planar_law_of_cosines (g : Geometry) (θ : Fin 6 → ℝ) :
    planarQ g θ ^ 2 + planarH g θ ^ 2 =
      g.linkOne ^ 2 + g.linkTwo ^ 2 + 2 * g.linkOne * g.linkTwo * Real.cos (psi θ) := by
  rw [planarQ_sq_add_planarH_sq, planarU_eq_planarUAt, planarV_eq_planarVAt,
    planarUAt_sq_add_planarVAt_sq]

/-- The solver's elbow cosine at a planar target `(q, h)`: the law of cosines read backwards,
which is where the elbow angle comes from once the distance to the wrist centre is known.

`kinematics.py` writes this with `distance = math.hypot(q, h)` and squares it. Over `ℝ` that
square is `q ^ 2 + h ^ 2`, and taking the unsquared form here keeps the square root out of
the elbow step entirely - the solver's only square root is the radial one in
`shoulderRadius`. -/
def elbowCosine (g : Geometry) (q h : ℝ) : ℝ :=
  (q ^ 2 + h ^ 2 - g.linkOne ^ 2 - g.linkTwo ^ 2) / (2 * g.linkOne * g.linkTwo)

/-- The elbow cosine at a configuration's own planar target is the cosine of that
configuration's second-link direction `psi`: the law of cosines, divided through by the same
non-vanishing factor `elbowCosine` multiplies by. This is the identity the completeness half
reads backwards - from a commanded configuration's pose to the direction the elbow step
recovered. -/
theorem elbowCosine_of_planar (g : Geometry) (θ : Fin 6 → ℝ) :
    elbowCosine g (planarQ g θ) (planarH g θ) = Real.cos (psi θ) := by
  have hpos : (0 : ℝ) < 2 * g.linkOne * g.linkTwo := by
    nlinarith [g.linkOne_pos, g.linkTwo_pos]
  rw [elbowCosine, planar_law_of_cosines]
  rw [show g.linkOne ^ 2 + g.linkTwo ^ 2 + 2 * g.linkOne * g.linkTwo * Real.cos (psi θ) -
      g.linkOne ^ 2 - g.linkTwo ^ 2 = (2 * g.linkOne * g.linkTwo) * Real.cos (psi θ) by
    ring]
  exact mul_div_cancel_left₀ _ (ne_of_gt hpos)

/-- The elbow cosine at a configuration that produced the pose is the cosine of that
configuration's second-link direction, so it always lies inside the reachability band: the
branch matching the commanded angles is never rejected by the band test. -/
theorem elbowCosine_mem_Icc (g : Geometry) (θ : Fin 6 → ℝ) :
    elbowCosine g (planarQ g θ) (planarH g θ) ∈ Set.Icc (-1) 1 := by
  rw [elbowCosine_of_planar]
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-! ## The closed form

Every branch function below is the corresponding line of `kinematics.py`'s
`inverse_kinematics`, in the same order, with the target pose `T` standing in for the
pair `(target_position, target_rotation)` it reads. The angle arithmetic is on *total* DH
angles, so nothing is wrapped and no static offset is subtracted.
-/

/-- The radial distance from the base axis to the wrist centre: `math.hypot` of its first two
components. This is the solver's `base_radius`, and it is the only square root in the
closed form. -/
def shoulderRadius (g : Geometry) (T : Pose) : ℝ := hypot (wristX g T) (wristY g T)

/-- The first joint's total angle at shoulder branch `sigma`: the azimuth of the wrist centre,
or its antipode when `sigma = -1`, which puts the arm plane on the other side of the base
axis.

`kinematics.py` writes the antipode as `_wrap_angle(base_azimuth + pi)`; `atan2 (-y) (-x)` is
the same angle written without a normalisation step, and `Zyz`-free `RealAtan2` proves the two
agree modulo a full turn (`RealAtan2.atan2_neg_coe_angle`).

At `r = 0` the azimuth is undefined and position alone cannot determine this joint; the pose
is still reachable, so the plane is anchored at zero (or at `pi`, its antipode) and the
solutions that come out are exact regardless. -/
def shoulderAngle (g : Geometry) (T : Pose) (σ : ℤ) : ℝ :=
  if shoulderRadius g T = 0 then (if σ = 1 then 0 else Real.pi)
  else atan2 (σ * wristY g T) (σ * wristX g T)

/-- The planar target's radial component: the wrist centre's distance from the base axis,
signed by the shoulder branch and measured from the frame-1 origin rather than the base
axis. This is `kinematics.py`'s `radial_target`. -/
def planarTargetQ (g : Geometry) (T : Pose) (σ : ℤ) : ℝ := σ * shoulderRadius g T - g.a1

/-- The planar target's vertical component, measured from the frame-1 origin. This is
`kinematics.py`'s `wrist_height`. -/
def planarTargetH (g : Geometry) (T : Pose) : ℝ := wristZ g T - g.d1

/-- The second link's direction for elbow branch `epsilon`: `± arccos c` with `c` the elbow
cosine. The branch that is generated only when `c` lies in the reachability band `[-1, 1]`,
so `Real.cos_arccos` applies to it as it stands. -/
def elbowAngle (g : Geometry) (T : Pose) (σ ε : ℤ) : ℝ :=
  ε * Real.arccos (elbowCosine g (planarTargetQ g T σ) (planarTargetH g T))

/-- The second joint's total angle: the direction of the planar target less the direction of
the second link, since the target is the second link seen from the first. This is
`kinematics.py`'s `total_theta2`. -/
def elbowTheta2 (g : Geometry) (T : Pose) (σ ε : ℤ) : ℝ :=
  atan2 (planarTargetH g T) (planarTargetQ g T σ) -
    atan2 (planarVAt g (elbowAngle g T σ ε)) (planarUAt g (elbowAngle g T σ ε))

/-- The third joint's total angle. The second link points along `psi` in the plane, and
`alpha3 = 90` degrees makes that direction `theta2 + theta3 - pi/2`, so `theta3 = psi + pi/2`
- the same `quarter` twist `Kinematics.psi` inverts. This is `kinematics.py`'s
`total_theta3`. -/
def elbowTheta3 (g : Geometry) (T : Pose) (σ ε : ℤ) : ℝ := elbowAngle g T σ ε + quarter

/-- The arm's rotation at a candidate's first three joints. -/
def armRotationAt (g : Geometry) (T : Pose) (σ ε : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  armRotation (shoulderAngle g T σ) (elbowTheta2 g T σ ε) (elbowTheta3 g T σ ε)

/-- `R_3^6` at a candidate's arm angles: the rotation the wrist has to supply. This is
`kinematics.py`'s `relative_rotation`. -/
def relativeRotationAt (g : Geometry) (T : Pose) (σ ε : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  relativeRotation (shoulderAngle g T σ) (elbowTheta2 g T σ ε) (elbowTheta3 g T σ ε) T

/-- The magnitude of the wrist's middle angle: the length of the first two entries of
`R_3^6`'s third column, which is `|sin theta5|`. This is `kinematics.py`'s `sine_five`, and
it is read from the rotation rather than through `arccos` for the reason its comment gives:
near `theta5 = 0` the `arccos` of a rounded `cos theta5` stalls, and the `d6` offset
magnifies the stall into a position error. -/
def wristSine (g : Geometry) (T : Pose) (σ ε : ℤ) : ℝ :=
  hypot (relativeRotationAt g T σ ε 0 2) (relativeRotationAt g T σ ε 1 2)

/-- The wrist's middle angle's cosine: the `(3,3)` entry of `R_3^6`. -/
def wristCosine (g : Geometry) (T : Pose) (σ ε : ℤ) : ℝ := relativeRotationAt g T σ ε 2 2

/-- Whether this arm branch sits at the wrist singularity, where joints 4 and 6 share an axis
and only their sum (or difference) is observable.

An `abbrev` rather than a `def`: it is a definitional layer over an equation, and the `if`s
below need the `Decidable` instance of the equation itself, not of the wrapper. -/
abbrev wristIsSingular (g : Geometry) (T : Pose) (σ ε : ℤ) : Prop :=
  wristSine g T σ ε = 0

/-- Joint 4's direction as read off `R_3^6`: the `atan2` pair of the third column's first two
entries.

Naming the read keeps the entry arithmetic inside a definition. Unfolding it inside a proof
would leave `M i j` on a partially unfolded matrix, which `rw` cannot re-typecheck at its
reduced transparency - so the proofs rewrite this name and let the reconstruction theorems'
own entry forms match by definitional equality. -/
def wristReadTheta4 (Q : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := atan2 (Q 1 2) (Q 0 2)

/-- Joint 6's direction as read off `R_3^6`: the `atan2` pair of the third row's last two
entries. -/
def wristReadTheta6 (Q : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := atan2 (Q 2 1) (-(Q 2 0))

/-- Joint 6's direction at the wrist singularity: read off the rotation with the middle one
taken out, which is `kinematics.py`'s `flattened` product. -/
def wristReadTheta6Flat (Q : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  atan2 ((rotY (atan2 0 (Q 2 2)) * Q) 1 0) ((rotY (atan2 0 (Q 2 2)) * Q) 0 0)

/-- The fourth joint's total angle. Off the singularity it is the direction of joint 4, read
off `R_3^6`, shifted by `pi` on the mirrored branch; at the singularity it is pinned to zero,
which is the split `kinematics.py` falls back on there.

**This is where the Lean solver deliberately differs from `kinematics.py`.** Python appends
both the mirrored pair *and* the `theta4 = 0` pair near the singularity and lets its pose
check discard whichever does not reproduce the target; over `ℝ` the mirrored pair there is
not merely inaccurate but wrong (`wristRotation` of it is a different rotation), so a solver
without a pose check must not construct it. The candidates returned are the same ones
Python's check keeps. -/
def wristTheta4 (g : Geometry) (T : Pose) (σ ε wb : ℤ) : ℝ :=
  if wristIsSingular g T σ ε then 0
  else wristReadTheta4 (relativeRotationAt g T σ ε) + (if wb < 0 then 0 else Real.pi)

/-- The fifth joint's total angle: `± atan2 (sin theta5) (cos theta5)`, the two signs being
the two wrist branches. At the singularity both signs are still generated, and they are the
two splits of the unobservable `theta4 ± theta6`. -/
def wristTheta5 (g : Geometry) (T : Pose) (σ ε wb : ℤ) : ℝ :=
  wb * atan2 (wristSine g T σ ε) (wristCosine g T σ ε)

/-- The sixth joint's total angle. Off the singularity it is joint 6's direction read off
`R_3^6`, shifted by `pi` with joint 4 on the mirrored branch; at the singularity it is read
off the rotation with the middle one taken out.

The flattening uses `atan2 0 (cos theta5)` rather than `wb * atan2 0 (cos theta5)`: at the
singularity that angle is `0` or `pi`, and `rotY` cannot tell `pi` from `-pi`, so the two
agree. Taking the sign out keeps the branching in one place, `wristTheta5`. -/
def wristTheta6 (g : Geometry) (T : Pose) (σ ε wb : ℤ) : ℝ :=
  if wristIsSingular g T σ ε then wristReadTheta6Flat (relativeRotationAt g T σ ε)
  else wristReadTheta6 (relativeRotationAt g T σ ε) + (if wb < 0 then 0 else Real.pi)

/-- The six total angles of the candidate on branches `(sigma, epsilon, wrist)`.

Naming the vector keeps the three families of branches apart: the first three slots depend
only on `(sigma, epsilon)`, the last three only on `(sigma, epsilon, wrist)`, and no proof
ever has to index a `Fin 6` literal. -/
def candidateAngles (g : Geometry) (T : Pose) (σ ε wb : ℤ) : Fin 6 → ℝ :=
  ![shoulderAngle g T σ, elbowTheta2 g T σ ε, elbowTheta3 g T σ ε,
    wristTheta4 g T σ ε wb, wristTheta5 g T σ ε wb, wristTheta6 g T σ ε wb]

/-- The elbow branches that are generated for a shoulder branch: both, unless this shoulder
branch's planar target is out of reach, in which case none is.

`kinematics.py` computes `distance = hypot q h` and tests `-1 - tolerance ≤ c ≤ 1 + tolerance`,
clamping into the band before the `acos`. Over `ℝ` the tolerance is dropped and the band test
is exact, so the clamp has nothing left to do. -/
def elbowBranches (g : Geometry) (T : Pose) (σ : ℤ) : List ℤ :=
  if elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1 then [1, -1]
  else []

/-- The closed-form solver: every candidate `kinematics.py`'s `inverse_kinematics` computes,
in its generation order - shoulder `+1` then `-1`, elbow `+1` then `-1`, wrist `+1` then
`-1` - and filtered exactly as its pose check would filter it in exact arithmetic.

A `List` of labels rather than a `List` of `Solution`s built by nested `if`s: membership then
goes through `List.mem_flatMap`, and each `if` is discharged once, locally, where it is
needed. -/
def solutions (g : Geometry) (T : Pose) : List Solution :=
  ([1, -1] : List ℤ).flatMap fun σ =>
    (elbowBranches g T σ).flatMap fun ε =>
      ([1, -1] : List ℤ).map fun wb =>
        { angles := candidateAngles g T σ ε wb, shoulder := σ, elbow := ε }

/-! ## What the branch formulas compute

Two facts, one per half of the arm: the shoulder branch lands the wrist centre in the plane
its angle names, and the elbow branch lands the planar chain exactly on the target `(q, h)`.
Together they are the position half of soundness; the orientation half is the ZYZ
reconstruction in `Zyz`.
-/

/-- The elbow angle's cosine is the elbow cosine: the branch was generated only inside the
reachability band, so `Real.cos_arccos` applies, and `±` does not survive a cosine. -/
theorem cos_elbowAngle (g : Geometry) (T : Pose) (σ ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hc : elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1) :
    Real.cos (elbowAngle g T σ ε) =
      elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) := by
  rcases hε with rfl | rfl
  · simp only [elbowAngle, Int.cast_one, one_mul]
    exact Real.cos_arccos hc.1 hc.2
  · simp only [elbowAngle, Int.cast_neg, Int.cast_one, neg_mul, one_mul, Real.cos_neg]
    exact Real.cos_arccos hc.1 hc.2

/-- The shoulder branch puts the wrist centre in the plane its angle names: multiplying the
branch's `a1 + q` by the angle's cosine and sine returns the wrist centre's first two
components.

At `r = 0` the wrist centre is on the base axis, so both components vanish and the factor
`sigma * r` does too - which is why the degenerate case needs no separate treatment beyond
the vanishing of `hypot`. -/
theorem shoulderAngle_cos_sin (g : Geometry) (T : Pose) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (g.a1 + planarTargetQ g T σ) * Real.cos (shoulderAngle g T σ) = wristX g T ∧
    (g.a1 + planarTargetQ g T σ) * Real.sin (shoulderAngle g T σ) = wristY g T := by
  have hσr : g.a1 + planarTargetQ g T σ = (σ : ℝ) * shoulderRadius g T := by
    simp only [planarTargetQ]; ring
  by_cases hr : shoulderRadius g T = 0
  · -- The wrist centre sits on the base axis: `hypot = 0` forces both components to vanish,
      -- and the branch factor `sigma * r` vanishes with them.
    have hsq : wristX g T ^ 2 + wristY g T ^ 2 = 0 := by
      have h2 := congrArg (fun v : ℝ => v ^ 2) hr
      rw [shoulderRadius, hypot_sq] at h2
      simpa using h2
    have hx : wristX g T = 0 := by nlinarith [sq_nonneg (wristX g T), sq_nonneg (wristY g T)]
    have hy : wristY g T = 0 := by nlinarith [sq_nonneg (wristX g T), sq_nonneg (wristY g T)]
    have hangle : shoulderAngle g T σ = (if σ = 1 then 0 else Real.pi) := by
      simp only [shoulderAngle]
      exact ite_eq_left hr
    rcases hσ with rfl | rfl <;>
      · constructor <;> simp [hangle, hσr, hr, hx, hy]
  · -- Otherwise the branch is an `atan2` pair, whose arguments do not both vanish.
    have hσ0 : (σ : ℝ) ≠ 0 := by rcases hσ with rfl | rfl <;> simp
    have hσ1 : (σ : ℝ) * σ = 1 := by rcases hσ with rfl | rfl <;> simp
    -- The sign as a real, so that later rewrites stay ordinary rewrites: substituting the
    -- integer directly would have to eliminate a hypothesis that mentions the coercion.
    have hσR : (σ : ℝ) = 1 ∨ (σ : ℝ) = -1 := by rcases hσ with rfl | rfl <;> simp
    have hne : ((σ : ℝ) * wristX g T, (σ : ℝ) * wristY g T) ≠ (0, 0) := by
      intro h
      -- Read the two components off the pair equality. (`rintro ⟨h1, h2⟩` would have to
      -- `cases` the equality, which fails on the coerced `sigma`.)
      have h1 : (σ : ℝ) * wristX g T = 0 := congrArg Prod.fst h
      have h2 : (σ : ℝ) * wristY g T = 0 := congrArg Prod.snd h
      -- Both components vanishing would put `hypot` at zero, which `hr` forbids.
      have hx : wristX g T = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hσ0
        · exact h
      have hy : wristY g T = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h hσ0
        · exact h
      exact hr (by simp [shoulderRadius, hypot, hx, hy])
    have hrad : hypot ((σ : ℝ) * wristX g T) ((σ : ℝ) * wristY g T) = shoulderRadius g T := by
      rcases hσR with h | h
      · rw [h]; simp only [one_mul]; rfl
      · rw [h, neg_one_mul, neg_one_mul, hypot_neg]; rfl
    have hangle : shoulderAngle g T σ = atan2 ((σ : ℝ) * wristY g T) ((σ : ℝ) * wristX g T) := by
      simp only [shoulderAngle]
      exact ite_eq_right hr
    -- `cos` and `sin` of the branch, read off `RealAtan2`, with the branch's own radius.
    have hcos : Real.cos (shoulderAngle g T σ) = (σ : ℝ) * wristX g T / shoulderRadius g T := by
      rw [hangle, RealAtan2.cos_atan2 hne, hrad]
    have hsin : Real.sin (shoulderAngle g T σ) = (σ : ℝ) * wristY g T / shoulderRadius g T := by
      rw [hangle, RealAtan2.sin_atan2, hrad]
    -- The two `sigma` factors cancel against each other, whatever the sign is.
    have hstep : ∀ y : ℝ,
        (σ : ℝ) * shoulderRadius g T * ((σ : ℝ) * y / shoulderRadius g T) = y := by
      intro y
      calc (σ : ℝ) * shoulderRadius g T * ((σ : ℝ) * y / shoulderRadius g T)
          = ((σ : ℝ) * σ) * (shoulderRadius g T * (y / shoulderRadius g T)) := by ring
        _ = 1 * y := by rw [hσ1, mul_div_cancel₀ y hr]
        _ = y := one_mul y
    constructor
    · rw [hcos, hσr]
      exact hstep (wristX g T)
    · rw [hsin, hσr]
      exact hstep (wristY g T)

/-- The elbow branch lands the planar chain on the target: the two links, at the branch's
second-link direction and second-link angle, reach exactly `(q, h)`.

This is where `RealAtan2`'s `cos_atan2_sub_mul`/`sin_atan2_sub_mul` fire - they say that
turning the vector `(u, v)` by `atan2 h q - atan2 v u` returns `(q, h)`, which is precisely
what the `theta2` formula claims, and they need only that `(q, h)` and `(u, v)` have the same
length. That length is the law of cosines: `u ^ 2 + v ^ 2` is `L1 ^ 2 + L2 ^ 2 + 2 L1 L2 cos
psi`, and `cos psi` is the elbow cosine by construction. -/
theorem planarTarget_eq (g : Geometry) (T : Pose) (σ ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hc : elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1) :
    planarQAt g (elbowTheta2 g T σ ε) (elbowAngle g T σ ε) = planarTargetQ g T σ ∧
    planarHAt g (elbowTheta2 g T σ ε) (elbowAngle g T σ ε) = planarTargetH g T := by
  have hL : (2 : ℝ) * g.linkOne * g.linkTwo ≠ 0 := by
    have := g.linkOne_pos; have := g.linkTwo_pos; nlinarith
  have hcos := cos_elbowAngle g T σ ε hε hc
  -- The two planar vectors have the same length, which is all the `atan2` subtraction needs.
  have hlen : planarTargetQ g T σ ^ 2 + planarTargetH g T ^ 2 =
      planarUAt g (elbowAngle g T σ ε) ^ 2 + planarVAt g (elbowAngle g T σ ε) ^ 2 := by
    rw [planarUAt_sq_add_planarVAt_sq_of_cos_eq g hcos]
    have hkey : (2 : ℝ) * g.linkOne * g.linkTwo *
        elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) =
        planarTargetQ g T σ ^ 2 + planarTargetH g T ^ 2 - g.linkOne ^ 2 - g.linkTwo ^ 2 := by
      rw [elbowCosine, mul_div_cancel₀ _ hL]
    rw [hkey]; ring
  have hcos_sub := cos_atan2_sub_mul (q := planarTargetQ g T σ) (h := planarTargetH g T)
    (u := planarUAt g (elbowAngle g T σ ε)) (v := planarVAt g (elbowAngle g T σ ε)) hlen
  have hsin_sub := sin_atan2_sub_mul (q := planarTargetQ g T σ) (h := planarTargetH g T)
    (u := planarUAt g (elbowAngle g T σ ε)) (v := planarVAt g (elbowAngle g T σ ε)) hlen
  constructor
  · rw [planarQAt_eq, elbowTheta2, mul_comm (planarUAt g (elbowAngle g T σ ε)),
      mul_comm (planarVAt g (elbowAngle g T σ ε))]
    exact hcos_sub
  · rw [planarHAt_eq, elbowTheta2, mul_comm (planarUAt g (elbowAngle g T σ ε)),
      mul_comm (planarVAt g (elbowAngle g T σ ε))]
    exact hsin_sub

-- One lemma per slot of `candidateAngles`, so that a proof rewrites a single component
-- rather than unfolding a six-element literal against a `Fin.mk` index. `Kinematics` does
-- the same for its joint vectors and its `dhP`.
@[simp] theorem candidateAngles_zero (g : Geometry) (T : Pose) (σ ε wb : ℤ) :
    candidateAngles g T σ ε wb 0 = shoulderAngle g T σ := rfl

@[simp] theorem candidateAngles_one (g : Geometry) (T : Pose) (σ ε wb : ℤ) :
    candidateAngles g T σ ε wb 1 = elbowTheta2 g T σ ε := rfl

@[simp] theorem candidateAngles_two (g : Geometry) (T : Pose) (σ ε wb : ℤ) :
    candidateAngles g T σ ε wb 2 = elbowTheta3 g T σ ε := rfl

@[simp] theorem candidateAngles_three (g : Geometry) (T : Pose) (σ ε wb : ℤ) :
    candidateAngles g T σ ε wb 3 = wristTheta4 g T σ ε wb := rfl

@[simp] theorem candidateAngles_four (g : Geometry) (T : Pose) (σ ε wb : ℤ) :
    candidateAngles g T σ ε wb 4 = wristTheta5 g T σ ε wb := rfl

@[simp] theorem candidateAngles_five (g : Geometry) (T : Pose) (σ ε wb : ℤ) :
    candidateAngles g T σ ε wb 5 = wristTheta6 g T σ ε wb := rfl

/-- The candidate's second-link direction is the elbow branch's: the third joint's total angle
is `psi + pi/2`, and `Kinematics.psi` takes the `pi/2` back off. -/
theorem psi_candidateAngles (g : Geometry) (T : Pose) (σ ε wb : ℤ) :
    psi (candidateAngles g T σ ε wb) = elbowAngle g T σ ε := by
  simp only [psi, candidateAngles_two, elbowTheta3]
  exact add_sub_cancel_right _ _

/-- The candidate's planar target is the solver's: rewriting `planarQ`/`planarH` into their
general forms and then reading the candidate's own slots gives exactly `(q, h)`. -/
theorem planarQ_candidateAngles (g : Geometry) (T : Pose) (σ ε wb : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hc : elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1) :
    planarQ g (candidateAngles g T σ ε wb) = planarTargetQ g T σ ∧
    planarH g (candidateAngles g T σ ε wb) = planarTargetH g T := by
  have hpq := (planarTarget_eq g T σ ε hε hc).1
  have hph := (planarTarget_eq g T σ ε hε hc).2
  constructor
  · rw [planarQ_eq_planarQAt, candidateAngles_one, psi_candidateAngles, hpq]
  · rw [planarH_eq_planarHAt, candidateAngles_one, psi_candidateAngles, hph]

/-- **The position half of soundness.** A candidate's wrist centre is the target's.

It does not depend on the wrist branch at all: the wrist centre is the frame-4 origin, all
three wrist joints turn about axes through it, and `Kinematics.wristCenter_fk` already
records that the `d6` tool offset cancels against itself. So the shoulder branch's plane and
the elbow branch's planar target are the whole story. -/
theorem wristCenter_fk_candidate (g : Geometry) (T : Pose) (σ ε wb : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (hε : ε = 1 ∨ ε = -1)
    (hc : elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1) :
    wristCenter g (fk g (candidateAngles g T σ ε wb)) = wristCenter g T := by
  have hq := (planarQ_candidateAngles g T σ ε wb hε hc).1
  have hh := (planarQ_candidateAngles g T σ ε wb hε hc).2
  have hxy := shoulderAngle_cos_sin g T σ hσ
  rw [wristCenter_fk]
  funext i
  fin_cases i <;>
    simp only [candidateAngles_zero, hq, hh, planarTargetH] <;>
    -- Full `simp`, not `simp only`: the literal vector's entries sit at `Fin.mk` indices that
    -- `simp only` cannot match, and `wristX`/`wristY`/`wristZ` have to unfold on both sides.
    simp [wristX, wristY, wristZ, hxy.1, hxy.2]

/-- Membership in `elbowBranches`, unwound: an elbow branch is generated exactly when this
shoulder branch's planar target is inside the reachability band, and the only branches are
`±1`. -/
theorem mem_elbowBranches {g : Geometry} {T : Pose} {σ ε : ℤ} :
    ε ∈ elbowBranches g T σ ↔
      elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1 ∧
        (ε = 1 ∨ ε = -1) := by
  unfold elbowBranches
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Membership in `solutions`, unwound: a candidate is a shoulder branch, an elbow branch the
reachability band kept, and a wrist branch. Stated as an `↔` so that the soundness theorem
can take a candidate apart into exactly the hypotheses its branch lemmas want. -/
theorem mem_solutions {g : Geometry} {T : Pose} {s : Solution} :
    s ∈ solutions g T ↔ ∃ σ ε wb : ℤ, (σ = 1 ∨ σ = -1) ∧
      elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1 ∧
      (ε = 1 ∨ ε = -1) ∧ (wb = 1 ∨ wb = -1) ∧
      s = ⟨candidateAngles g T σ ε wb, σ, ε⟩ := by
  simp only [solutions, List.mem_flatMap, List.mem_map, mem_elbowBranches, List.mem_cons,
    List.mem_nil_iff, or_false]
  -- `simp` nests the existentials one branch family at a time; the statement hoists them.
  constructor
  · rintro ⟨σ, hσ, ε, ⟨hc, hε⟩, wb, hwb, rfl⟩
    exact ⟨σ, ε, wb, hσ, hc, hε, hwb, rfl⟩
  · rintro ⟨σ, ε, wb, hσ, hc, hε, hwb, rfl⟩
    exact ⟨σ, hσ, ε, ⟨hc, hε⟩, wb, hwb, rfl⟩

/-- `rotY` cannot tell `pi` from `-pi`: it reads its angle only through a cosine and a sine,
and the sine is what differs. At the wrist singularity the middle angle is `0` or `pi`, which
is what lets the two wrist branches share one flattening. -/
theorem rotY_neg_eq_of_sin_eq_zero (τ : ℝ) (h : Real.sin τ = 0) : rotY (-τ) = rotY τ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotY, Real.cos_neg, Real.sin_neg, h]

/-- The two wrist branches agree at the singularity: `wristRotation` negates its middle angle,
so the branch sign cancels against a `rotY` that cannot see it. -/
theorem wristRotation_zero_neg (τ θ6 : ℝ) (h : Real.sin τ = 0) :
    wristRotation 0 (-τ) θ6 = wristRotation 0 τ θ6 := by
  simp only [wristRotation, rotZ_zero, one_mul, neg_neg]
  rw [rotY_neg_eq_of_sin_eq_zero τ h]

/-- **The orientation half of soundness.** A candidate's rotation is the target's, whenever
the target's rotation is a rotation.

The candidate's wrist rotation is, by `Zyz`'s reconstruction theorems, `R_3^6` read off the
target - the very matrix the solver recovered the wrist angles from - and multiplying it by
the arm's own rotation cancels that rotation and leaves `T.R`. -/
theorem R_fk_candidate {g : Geometry} {T : Pose} (σ ε wb : ℤ)
    (hwb : wb = 1 ∨ wb = -1) (hQ : T.Rᵀ * T.R = 1) (hdet : T.R.det = 1) :
    (fk g (candidateAngles g T σ ε wb)).R = T.R := by
  have hrel_orth : (relativeRotationAt g T σ ε)ᵀ * relativeRotationAt g T σ ε = 1 := by
    rw [relativeRotationAt]
    exact relativeRotation_orth hQ
  have hrel_det : (relativeRotationAt g T σ ε).det = 1 := by
    rw [relativeRotationAt]
    exact relativeRotation_det hdet
  have hA : armRotationAt g T σ ε * (armRotationAt g T σ ε)ᵀ = 1 :=
    mul_transpose_eq_one_of_transpose_mul (armRotation_orth _ _ _)
  have hwrist : wristRotation (wristTheta4 g T σ ε wb) (wristTheta5 g T σ ε wb)
      (wristTheta6 g T σ ε wb) = relativeRotationAt g T σ ε := by
    by_cases hs : wristIsSingular g T σ ε
    · -- At the singularity only the flattened pair reconstructs `R_3^6`, and the two wrist
      -- branches differ only by the sign of an angle `rotY` cannot see.
      have hs0 : wristSine g T σ ε = 0 := hs
      have hsq : (relativeRotationAt g T σ ε 0 2) ^ 2 +
          (relativeRotationAt g T σ ε 1 2) ^ 2 = 0 := by
        have h := congrArg (fun v : ℝ => v ^ 2) hs0
        rw [wristSine, hypot_sq] at h
        simpa using h
      have h02 : relativeRotationAt g T σ ε 0 2 = 0 := by
        nlinarith [sq_nonneg (relativeRotationAt g T σ ε 0 2),
          sq_nonneg (relativeRotationAt g T σ ε 1 2)]
      have h12 : relativeRotationAt g T σ ε 1 2 = 0 := by
        nlinarith [sq_nonneg (relativeRotationAt g T σ ε 0 2),
          sq_nonneg (relativeRotationAt g T σ ε 1 2)]
      have hτ : Real.sin (atan2 0 (wristCosine g T σ ε)) = 0 := by
        rw [RealAtan2.sin_atan2]; simp
      have hflat := wristRotation_reconstruct_flat hrel_orth hrel_det h02 h12
      rcases hwb with rfl | rfl
      · simp only [wristTheta4, wristTheta5, wristTheta6, ite_eq_left hs, hs0, Int.cast_one,
          one_mul]
        simpa only [wristReadTheta4, wristReadTheta6Flat, wristSine, wristCosine] using hflat
      · simp only [wristTheta4, wristTheta5, wristTheta6, ite_eq_left hs, hs0, Int.cast_neg,
          Int.cast_one, neg_one_mul]
        rw [wristRotation_zero_neg _ _ hτ]
        simpa only [wristReadTheta4, wristReadTheta6Flat, wristSine, wristCosine] using hflat
    · -- Off the singularity the mirrored pair reconstructs it, one branch per sign.
      have hne : (relativeRotationAt g T σ ε 0 2, relativeRotationAt g T σ ε 1 2) ≠ (0, 0) := by
        intro h
        have h1 : relativeRotationAt g T σ ε 0 2 = 0 := congrArg Prod.fst h
        have h2 : relativeRotationAt g T σ ε 1 2 = 0 := congrArg Prod.snd h
        exact hs (by simp [wristIsSingular, wristSine, hypot, h1, h2])
      have hdirect := wristRotation_reconstruct hrel_orth hrel_det hne
      have hmirror := wristRotation_reconstruct_mirror hrel_orth hrel_det hne
      rcases hwb with rfl | rfl
      · simp only [wristTheta4, wristTheta5, wristTheta6, ite_eq_right hs, Int.cast_one,
          one_mul, Int.reduceLT, ite_false]
        simpa only [wristReadTheta4, wristReadTheta6, wristSine, wristCosine] using hmirror
      · simp only [wristTheta4, wristTheta5, wristTheta6, ite_eq_right hs, Int.cast_neg,
          Int.cast_one, neg_one_mul, Int.reduceLT, ite_true, add_zero]
        simpa only [wristReadTheta4, wristReadTheta6, wristSine, wristCosine] using hdirect
  rw [fk_R, candidateAngles_zero, candidateAngles_one, candidateAngles_two, candidateAngles_three,
    candidateAngles_four, candidateAngles_five, ← armRotationAt, hwrist, relativeRotationAt,
    relativeRotation, ← armRotationAt, ← Matrix.mul_assoc, hA, Matrix.one_mul]

/-- **Soundness.** Every candidate the closed form returns reproduces the target pose exactly,
for any target whose rotation is a rotation - reachable or not.

This is the theorem that makes `kinematics.py`'s final pose check redundant: over `ℝ` there is
nothing for it to reject, which is why the Lean solver does not construct the candidates it
would have rejected (see `wristTheta4`) and why it carries no tolerances.

Instantiating at `T = fk g θ` with `fk_R_orth` and `fk_R_det` gives the round trip: every
branch of the solver reproduces a pose the arm can actually reach. -/
theorem fk_of_mem_solutions {g : Geometry} {T : Pose} (hQ : T.Rᵀ * T.R = 1)
    (hdet : T.R.det = 1) : ∀ s ∈ solutions g T, fk g s.angles = T := by
  intro s hs
  obtain ⟨σ, ε, wb, hσ, hc, hε, hwb, rfl⟩ := mem_solutions.mp hs
  exact eq_of_R_eq_of_wristCenter_eq
    (R_fk_candidate σ ε wb hwb hQ hdet)
    (wristCenter_fk_candidate g T σ ε wb hσ hε hc)

/-- The round trip on a pose the arm can actually reach: every branch of the solver reproduces
`fk g θ` exactly. This is the statement `test_kinematics.py`'s `assert_pose_reproduced`
demands of the Python solver - *all* returned solutions match the pose, not just one - and it
holds here because `fk`'s own rotation is a rotation (`fk_R_orth`) with determinant one
(`fk_R_det`). -/
theorem fk_of_mem_solutions_fk (g : Geometry) (θ : Fin 6 → ℝ) :
    ∀ s ∈ solutions g (fk g θ), fk g s.angles = fk g θ :=
  fk_of_mem_solutions (fk_R_orth g θ) (fk_R_det g θ)

/-! ## The branch a configuration sits on

The closed form returns a list of candidates, one per branch, each labelled with the branch it came
from - the labels `kinematics.py` reports on `InverseKinematicsSolution`, and the ones
`test_kinematics.py`'s `test_random_fk_poses_recover_angles_and_branch_labels` recomputes from a
commanded configuration and demands among the returned solutions. Reading those labels off a
configuration, rather than off a target pose, is what lets that demand become a theorem about
`solutions`.

None of the three labels is simply the sign of a joint angle. The shoulder label is the sign of the
planar radius `a1 + planarQ` - the wrist centre projected onto the direction joint 1 points in,
which is what tells the two shoulder branches apart, rather than the azimuth that `shoulderAngle`
recovers on either of them; `planarTargetQ_fk_shoulderBranch` below is the statement that this
label turns the solver's planar target back into the configuration's own `planarQ`. The elbow label
is the sign of `sin psi`, the second link's direction in that plane, with `Kinematics.psi = theta2
- pi/2` taking the quarter turn `alpha3 = 90` imposes out of the way. The wrist label is the sign
`wristTheta5` multiplies its `atan2` by - the sign the middle wrist angle was recovered with, and
the one the read-backs of `Zyz` compare their own half-turn decisions against.

Where the signed quantity vanishes, both labels describe the configuration: `fk_of_mem_solutions`
holds on either, and each definition below settles the tie the way the branch test that consumes it
needs - the elbow takes the `+1` label a straight elbow reads back with on
`RealAtan2.arccos_cos_coe_angle_of_nonneg`, while the shoulder and the wrist take `-1`. A
completeness statement names whichever branch these definitions picked, so the convention itself
never has to be argued about. -/

/-- The shoulder branch a configuration sits on: `1` when the wrist centre's planar radius
`a1 + planarQ` is positive, `-1` otherwise. This is the `sigma` label of the solver's shoulder
family - the one that turns `planarTargetQ = sigma * shoulderRadius - a1` into the configuration's
own `planarQ` - and it is the sign `mem_solutions` asks for when a candidate is taken apart.

The tie at `a1 + planarQ = 0` goes to `-1`. There the wrist centre sits on the base axis, so the
first joint has no azimuth to be read off and both labels describe the same reachable pose;
`planarTargetQ` is `-a1` either way, since it multiplies the vanishing `shoulderRadius`. -/
def shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ) : ℤ :=
  if 0 < g.a1 + planarQ g θ then 1 else -1

/-- The elbow branch a configuration sits on: the sign of `sin psi`, which is `+1` when it
vanishes, so a straight elbow is reported on the `+1` branch.

This is the `epsilon` of `elbowAngle = epsilon * arccos c`, hence the sign `RealAtan2`'s
`arccos_cos_coe_angle_of_nonneg` and `arccos_cos_coe_angle_of_nonpos` read the elbow's direction
back with. A straight elbow satisfies both of those hypotheses at once, which is why the tie can be
settled either way and is settled this way: the branch that the nonnegative-sine round trip covers
is the one the definitions name.

The sign is taken of `planarVAt g (psi θ)`, the solver's own perpendicular offset of the second
link - the `v` of the `atan2 (planarVAt ..) (planarUAt ..)` pair the elbow step forms - rather
than of `sin psi` directly. `elbowBranch_spec` records that the two signs agree, `linkTwo_pos`
being what carries one to the other, so the geometry parameter is what the label is read off
rather than decoration. -/
def elbowBranch (g : Geometry) (θ : Fin 6 → ℝ) : ℤ :=
  if 0 ≤ planarVAt g (psi θ) then 1 else -1

/-- The wrist branch a configuration sits on: the sign of the middle wrist angle's sine
`sin (θ 4)`. This is the `wb` of `wristTheta5 = wb * atan2 (wristSine) (wristCosine)`, and the
branch on which `wristTheta4` and `wristTheta6` add their half turn - the mirror the rotation's
other `atan2` branch corresponds to.

It is read off `sin (θ 4)` of the commanded configuration rather than off the sign of an angle the
solver recovered, because `sin (θ 4)` is the quantity the wrist rotation's entries determine:
`Zyz`'s read-backs express `wristSine` as `|sin (θ 4)|`, so this is the label that makes the
solver's `atan2` pair come out the way the pose's rotation says. The tie at `sin (θ 4) = 0` goes to
`-1`, the branch that does *not* add the half turn, matching the singular branch of `wristTheta5`,
where the angle negated is `0` or `pi` and a half turn is its own negative modulo a full turn. -/
def wristBranch (θ : Fin 6 → ℝ) : ℤ := if 0 < Real.sin (θ 4) then 1 else -1

/-- The shoulder label is one of the two the solver generates. -/
theorem shoulderBranch_eq_one_or_neg_one (g : Geometry) (θ : Fin 6 → ℝ) :
    shoulderBranch g θ = 1 ∨ shoulderBranch g θ = -1 := by
  unfold shoulderBranch
  split_ifs <;> simp

/-- The elbow label is one of the two the solver generates. -/
theorem elbowBranch_eq_one_or_neg_one (g : Geometry) (θ : Fin 6 → ℝ) :
    elbowBranch g θ = 1 ∨ elbowBranch g θ = -1 := by
  unfold elbowBranch
  split_ifs <;> simp

/-- **What the elbow label means.** The branch is `+1` exactly when `sin psi` is nonnegative and
`-1` exactly when it is nonpositive - the pair of hypotheses `RealAtan2`'s two `arccos` round
trips need, and the reason two elbow labels exist at all: between them they name every direction
the second link can point in, a straight elbow being the one direction that both cover.

Both signs are read off `planarVAt g (psi θ) = linkTwo * sin psi`, so they agree with the sign of
`sin psi` itself, the positive factor `linkTwo` carrying one to the other. -/
theorem elbowBranch_spec (g : Geometry) (θ : Fin 6 → ℝ) :
    (elbowBranch g θ = 1 ∧ 0 ≤ Real.sin (psi θ)) ∨
      (elbowBranch g θ = -1 ∧ Real.sin (psi θ) ≤ 0) := by
  unfold elbowBranch planarVAt
  split_ifs with h
  · exact Or.inl ⟨rfl, nonneg_of_mul_nonneg_right h g.linkTwo_pos⟩
  · have hneg : g.linkTwo * Real.sin (psi θ) < 0 := not_le.mp h
    exact Or.inr ⟨rfl, le_of_lt (by nlinarith [g.linkTwo_pos])⟩

/-- The wrist label is one of the two the solver generates, for any configuration at all - the
wrist family is generated unconditionally, singularity included. -/
theorem wristBranch_eq_one_or_neg_one (θ : Fin 6 → ℝ) :
    wristBranch θ = 1 ∨ wristBranch θ = -1 := by
  unfold wristBranch
  split_ifs <;> simp

/-! ## What a configuration's own pose says about its branches

`wristCenter_fk` places a configuration's wrist centre in the plane joint 1 has swung to. Read
through the solver's own accessors, it says the three things the completeness theorem needs: the
planar radius `shoulderRadius` is `|a1 + planarQ|` - which is what makes `shoulderBranch` the
branch whose planar target is the configuration's own `(planarQ, planarH)` - the vertical
component `planarTargetH` is `planarH` outright, and the first two components are the radius times
the cosine and sine of `theta 1`, which is the factor the shoulder-angle read-back cancels. -/

/-- The wrist centre's `x` component at a configuration's own pose. -/
theorem wristX_fk (g : Geometry) (θ : Fin 6 → ℝ) :
    wristX g (fk g θ) = (g.a1 + planarQ g θ) * Real.cos (θ 0) := by
  -- Full `simp`, not `simp only`: the literal vector's entries sit at `Fin.mk` indices that
  -- `simp only` cannot match, and `wristX` has to unfold to reach `wristCenter`.
  simp [wristX, wristCenter_fk]

/-- The wrist centre's `y` component at a configuration's own pose. -/
theorem wristY_fk (g : Geometry) (θ : Fin 6 → ℝ) :
    wristY g (fk g θ) = (g.a1 + planarQ g θ) * Real.sin (θ 0) := by
  simp [wristY, wristCenter_fk]

/-- The wrist centre's `z` component at a configuration's own pose: the base height plus the
planar height. -/
theorem wristZ_fk (g : Geometry) (θ : Fin 6 → ℝ) :
    wristZ g (fk g θ) = g.d1 + planarH g θ := by
  simp [wristZ, wristCenter_fk]

/-- **The radial distance a configuration's own pose reports.** `shoulderRadius` is the `hypot` of
the radius times a `(cos, sin)` pair, which `RealAtan2.hypot_mul_cos_sin` evaluates to the absolute
value of that radius. The absolute value is what `shoulderBranch` - the sign of `a1 + planarQ` -
undoes, which is the whole reason the branch is defined on the radius rather than on the wrist
centre's azimuth. -/
theorem shoulderRadius_fk (g : Geometry) (θ : Fin 6 → ℝ) :
    shoulderRadius g (fk g θ) = |g.a1 + planarQ g θ| := by
  rw [shoulderRadius, wristX_fk, wristY_fk]
  exact hypot_mul_cos_sin _ _

/-- The solver's planar target height at a configuration's own pose is that configuration's
`planarH`: both are the wrist centre's `z` component less `d1`. -/
theorem planarTargetH_fk (g : Geometry) (θ : Fin 6 → ℝ) :
    planarTargetH g (fk g θ) = planarH g θ := by
  rw [planarTargetH, wristZ_fk]
  ring

/-- **The shoulder branch recovers the planar target.** On the branch the configuration sits on,
the solver's signed planar target is the configuration's own `planarQ`: `shoulderBranch` carries
exactly the sign that undoes the absolute value `shoulderRadius_fk` leaves behind. This is the
rewrite that puts the completeness band test on the configuration's own `(planarQ, planarH)`.

No non-vanishing hypothesis is needed: at `a1 + planarQ = 0` the branch is `-1` and `planarTargetQ`
is `-a1`, which is `planarQ` again. -/
theorem planarTargetQ_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ) :
    planarTargetQ g (fk g θ) (shoulderBranch g θ) = planarQ g θ := by
  rw [planarTargetQ, shoulderRadius_fk, shoulderBranch]
  split_ifs with h
  · rw [abs_of_pos h]
    ring
  · rw [abs_of_nonpos (not_lt.mp h)]
    ring

/-- **The shoulder branch's own radius is the configuration's.** The factor the shoulder-angle
read-back multiplies out is `a1 + planarTargetQ`, and on the configuration's own branch that factor
is the configuration's own `a1 + planarQ` - the quantity the read-back cancels against the wrist
centre's components, non-zero exactly when `NonDegenerate`'s first clause says so.

No hypothesis is needed, tie included: at `a1 + planarQ = 0` the branch is `-1`, the radius
vanishes with the factor, and both sides are the same `0`. -/
theorem a1_add_planarTargetQ_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ) :
    g.a1 + planarTargetQ g (fk g θ) (shoulderBranch g θ) = g.a1 + planarQ g θ := by
  rw [planarTargetQ, shoulderRadius_fk, shoulderBranch]
  split_ifs with hpos
  · rw [abs_of_pos hpos]
    ring
  · rw [abs_of_nonpos (not_lt.mp hpos)]
    ring

/-! ## Coverage of the closed form

Statements about the list the solver returns rather than about the angles in it: the list is never
empty on a pose the arm can reach, never longer than the eight candidates the three branch families
can produce, and empty exactly when no configuration reaches the pose. With `fk_of_mem_solutions`
these are the two halves of `kinematics.py`'s final pose check as theorems - no returned candidate
is ever discarded, and no candidate a check would have kept is ever missing. -/

/-- **Coverage.** The solver returns at least one candidate for the pose a configuration produces:
the branches that configuration sits on are always among the generated ones, because the elbow
branch's law-of-cosines value always lies inside the reachability band (`elbowCosine_mem_Icc`), the
shoulder label is always one of the two, and every elbow branch is given both wrist labels.

No non-degeneracy hypothesis appears, and none is needed: the statement is about the list being
non-empty, and degenerate configurations are perfectly solvable - they merely fail to pin every
joint down, which is a statement about a recovered angle rather than about the list. -/
theorem solutions_ne_nil (g : Geometry) (θ : Fin 6 → ℝ) : solutions g (fk g θ) ≠ [] := by
  -- The witness is the configuration's own shoulder label with any elbow and wrist labels: the
  -- band test it has to pass is `elbowCosine_mem_Icc` at the planar target the shoulder branch
  -- recovers, which is the configuration's own `(planarQ, planarH)`.
  refine List.ne_nil_of_mem (l := solutions g (fk g θ))
    (a := ⟨candidateAngles g (fk g θ) (shoulderBranch g θ) 1 1, shoulderBranch g θ, 1⟩) ?_
  rw [mem_solutions]
  exact ⟨shoulderBranch g θ, 1, 1, shoulderBranch_eq_one_or_neg_one g θ,
    by rw [planarTargetQ_fk_shoulderBranch, planarTargetH_fk]; exact elbowCosine_mem_Icc g θ,
    Or.inl rfl, Or.inl rfl, rfl⟩

/-- One shoulder branch's elbow family has at most the two labels `±1`: the reachability band
either keeps both or keeps neither. -/
theorem length_elbowBranches_le_two (g : Geometry) (T : Pose) (σ : ℤ) :
    (elbowBranches g T σ).length ≤ 2 := by
  unfold elbowBranches
  split_ifs <;> simp

/-- **The length estimate `solutions` runs on.** A `flatMap`'s length is at most the input's length
times a uniform bound on the families', because each family contributes its own length and there is
one family per input element. -/
theorem length_flatMap_le_mul {α β : Type} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ n) : (l.flatMap f).length ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons a t ih =>
    -- One family's bound plus the rest's, which is one more element's worth of `n`.
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    calc (f a).length + (t.flatMap f).length
        ≤ n + t.length * n := Nat.add_le_add (h a (List.mem_cons_self ..))
          (ih fun b hb => h b (List.mem_cons_of_mem a hb))
      _ = (t.length + 1) * n := by ring

/-- **The solver returns at most eight candidates**: two shoulder branches, each with at most two
elbow branches, each of those with one candidate per wrist branch. The bound is the shape of
`solutions` and nothing about the pose, so it holds for any target at all. -/
theorem length_solutions_le_eight (g : Geometry) (T : Pose) : (solutions g T).length ≤ 8 := by
  -- One elbow family with both wrist labels: two candidates, at most.
  have h4 : ∀ σ : ℤ, ((elbowBranches g T σ).flatMap fun ε => ([1, -1] : List ℤ).map fun wb =>
      ({ angles := candidateAngles g T σ ε wb, shoulder := σ, elbow := ε } : Solution)).length
        ≤ 4 := by
    intro σ
    calc ((elbowBranches g T σ).flatMap fun ε => ([1, -1] : List ℤ).map fun wb =>
          ({ angles := candidateAngles g T σ ε wb, shoulder := σ, elbow := ε } : Solution)).length
        ≤ (elbowBranches g T σ).length * 2 := length_flatMap_le_mul _ _ 2 fun _ _ => by simp
      _ ≤ 2 * 2 := Nat.mul_le_mul_right 2 (length_elbowBranches_le_two g T σ)
      _ ≤ 4 := by norm_num
  simp only [solutions]
  calc (([1, -1] : List ℤ).flatMap fun σ => (elbowBranches g T σ).flatMap fun ε =>
        ([1, -1] : List ℤ).map fun wb =>
          ({ angles := candidateAngles g T σ ε wb, shoulder := σ, elbow := ε } : Solution)).length
      ≤ ([1, -1] : List ℤ).length * 4 := length_flatMap_le_mul _ _ 4 fun σ _ => h4 σ
    _ ≤ 8 := by simp

/-- **Rejection, as a theorem.** If the solver returned nothing for a pose then nothing the arm can
do reaches that pose, because every candidate it does return reproduces the pose
(`fk_of_mem_solutions`). This is the half of `kinematics.py`'s final pose check that discards an
unreachable target and returns `()`; here the empty list *is* the statement that there is nothing
to reach `T` with.

The rotation hypotheses are the standing qualification of this theorem and of `fk_of_mem_solutions`:
a target whose `R` is not a rotation is not a pose the arm can strike at all - `fk`'s rotation
always is one (`fk_R_orth`, `fk_R_det`) - while the solver, which reads the target's entries without
testing them, would still build candidates from it. For a genuine pose no filter is needed
anywhere, because `fk_of_mem_solutions` is exact. -/
theorem exists_fk_eq_of_solutions_ne_nil {g : Geometry} {T : Pose} (hQ : T.Rᵀ * T.R = 1)
    (hdet : T.R.det = 1) (h : solutions g T ≠ []) : ∃ θ : Fin 6 → ℝ, fk g θ = T := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil (solutions g T) h
  exact ⟨s.angles, fk_of_mem_solutions hQ hdet s hs⟩

/-- The converse of coverage: a pose no configuration reaches is a pose the solver returns nothing
for. Stated with an explicit `∀ θ, fk g θ ≠ T` rather than as "not reachable" so that the
hypothesis is exactly `kinematics.py`'s situation, where the check ran through every candidate and
found none - and so that the theorem needs no way of quantifying over the arm's reachable set.

The rotation hypotheses are load-bearing, not hygiene, and they are why the claim is about poses:
`solutions` reads a target only through its wrist centre, which sees `R` through its third column
alone, so a target whose `R` is not a rotation at all still passes the band test and comes back
with candidates - while no `θ` reproduces it, `fk`'s rotation being orthogonal of determinant one
(`fk_R_orth`, `fk_R_det`). `kinematics.py` discards those candidates in its pose check; over `ℝ`
there is no filter to discard them with, so the statement is made for the targets a pose can name,
where soundness is exact and the filter has nothing left to do. -/
theorem solutions_eq_nil_of_not_reachable {g : Geometry} {T : Pose} (hQ : T.Rᵀ * T.R = 1)
    (hdet : T.R.det = 1) (h : ∀ θ : Fin 6 → ℝ, fk g θ ≠ T) : solutions g T = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro s hs
  exact h s.angles (fk_of_mem_solutions hQ hdet s hs)

/-! ## The fold-back case, and non-vacuity

`NonDegenerate`'s second clause is the one case in which a reachable pose does not determine the
second joint: the two links equal and the wrist centre back on the frame-1 origin, so the plane is
folded double and `theta2` and `theta3` trade off against each other. The lemma below is the reason
that clause can be stated without mentioning `linkOne = linkTwo` as a separate assumption, and
`exists_nonDegenerate` is the witness that the completeness theorem built on it has something to
say. -/

/-- **The fold-back condition needs no `linkOne = linkTwo` hypothesis**: `planarQ = planarH = 0`
forces it. The two links' `(u, v)` sum vanishes, so the second link's sine vanishes (`linkTwo` is
positive) and its cosine is `±1`; the `+1` case would need `linkOne = -linkTwo`, which the two
positivity hypotheses forbid, leaving `linkOne = linkTwo`.

This is what makes `NonDegenerate`'s second clause the same condition as the degenerate case the
test suite describes - the two links equal *and* the hand folded back onto the frame-1 origin - and
it is the shape a completeness proof uses the clause in: a vanishing planar target pairs the
second link with the first, and then the inverse of the fold, the law of cosines, hands back
`cos psi = -1`. -/
theorem linkOne_eq_linkTwo_of_planar_eq_zero (g : Geometry) (θ : Fin 6 → ℝ)
    (hq : planarQ g θ = 0) (hh : planarH g θ = 0) : g.linkOne = g.linkTwo := by
  -- The law of cosines makes `(u, v)` the zero vector, so each of its components vanishes.
  have hsq : planarU g θ ^ 2 + planarV g θ ^ 2 = 0 := by
    rw [← planarQ_sq_add_planarH_sq, hq, hh]
    ring
  have hu : planarU g θ = 0 := by
    nlinarith [sq_nonneg (planarU g θ), sq_nonneg (planarV g θ)]
  have hv : planarV g θ = 0 := by
    nlinarith [sq_nonneg (planarU g θ), sq_nonneg (planarV g θ)]
  rw [planarU] at hu
  rw [planarV] at hv
  -- A vanishing second-link sine forces its cosine to `±1`, and the two signs are the two
  -- possibilities for the fold: linking the same way (`L1 = L2`) or the opposite way, which
  -- positivity rules out.
  have hsin : Real.sin (psi θ) = 0 := (mul_eq_zero.mp hv).resolve_left (ne_of_gt g.linkTwo_pos)
  have hcos : Real.cos (psi θ) = 1 ∨ Real.cos (psi θ) = -1 := by
    have h := Real.sin_sq_add_cos_sq (psi θ)
    rw [hsin] at h
    exact sq_eq_one_iff.mp (by simpa using h)
  rcases hcos with hc | hc
  · rw [hc, mul_one] at hu
    linarith [g.linkOne_pos, g.linkTwo_pos]
  · rw [hc, mul_neg_one] at hu
    linarith

/-- **Non-vacuity.** The completeness theorem below is not a statement about nothing: at the
geometry `robot_parameters.json` ships and the configuration that stands the arm straight out -
every joint at zero or at the quarter turn - all three clauses of `NonDegenerate` hold. The planar
radius is `10 + 40 + 40 = 90`, the planar target is `q = 80`, `h = 0`, so the second clause is not
met even though the two links are equal, and `theta4 = pi/2` is well away from the wrist
singularity. -/
theorem exists_nonDegenerate : ∃ (g : Geometry) (θ : Fin 6 → ℝ), NonDegenerate g θ := by
  refine ⟨⟨10, 40, 40, 40, 10, by norm_num, by norm_num⟩, ![0, 0, quarter, 0, quarter, 0], ?_⟩
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [planarQ, planarH, psi, quarter]

/-! ## Completeness

Soundness says every candidate the closed form returns reproduces the pose it came from. This
section is the other half: a commanded configuration outside `NonDegenerate`'s degenerate cases
comes back among the candidates, carrying the branch labels it sits on and all six of its angles
modulo a full turn.

The shape of the argument is one lemma per slot of `candidateAngles`. Slots 0, 2 and 4 are read-backs
the solver's own entry lemmas already state - `shoulderAngle_cos_sin` and `RealAtan2`'s two `arccos`
round trips for the arm, `Zyz`'s `wristRotation_read_theta5_coe_angle` for the wrist - whereas slots
1, 3 and 5 are the `atan2` pairs those entries are read off, and each needs the pair the solver forms
to be the pair the commanded angle turns the target into: `RealAtan2.atan2_rotate_coe_angle` for the
elbow, and the read-backs' own half turn for the two outer wrist joints.
`exists_solution_angles_eq` assembles the six. -/

/-- **The elbow angle at a configuration's own branch points the way the configuration does.** The
`arccos` round trip returns the second link's direction `psi` rather than its mirror exactly when the
label picks the matching one of `RealAtan2`'s two round trips, which is what `elbowBranch_spec`
records: the branch is `+1` on a nonnegative `sin psi` and `-1` on a nonpositive one.

This is the pair of hypotheses everything downstream of the elbow step needs - the angle read-back in
`elbowTheta3_fk_shoulderBranch` and the length and rotation identities of the second slot - and the
reason the elbow label is read off `sin psi` rather than off anything about the target. -/
theorem elbowAngle_cos_sin (g : Geometry) (θ : Fin 6 → ℝ) :
    Real.cos (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) = Real.cos (psi θ) ∧
      Real.sin (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) = Real.sin (psi θ) := by
  -- The branch's own band value is the configuration's `cos psi`, by the elbow branch's
  -- law-of-cosines identity at `(planarQ, planarH)`.
  have hc : elbowCosine g (planarTargetQ g (fk g θ) (shoulderBranch g θ)) (planarTargetH g (fk g θ))
      = Real.cos (psi θ) := by
    rw [planarTargetQ_fk_shoulderBranch, planarTargetH_fk]
    exact elbowCosine_of_planar g θ
  rcases elbowBranch_spec g θ with ⟨hε, hsin⟩ | ⟨hε, hsin⟩
  · -- A nonnegative `sin psi`: the `+1` branch is exactly the round trip that keeps the sign.
    have hangle : ((elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) : ℝ) : Real.Angle)
        = (Real.arccos (Real.cos (psi θ)) : Real.Angle) := by
      rw [elbowAngle, hε, hc, Int.cast_one, one_mul]
    have hround := arccos_cos_coe_angle_of_nonneg (ψ := psi θ) hsin
    exact ⟨cos_of_angle_eq (hangle.trans hround), sin_of_angle_eq (hangle.trans hround)⟩
  · -- A nonpositive `sin psi`: the `-1` branch negates, and negation is the mirror the round trip
    -- for that sign reads back.
    have hangle : ((elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) : ℝ) : Real.Angle)
        = (-Real.arccos (Real.cos (psi θ)) : Real.Angle) := by
      rw [elbowAngle, hε, hc, Int.cast_neg, Int.cast_one, neg_mul, one_mul, Real.Angle.coe_neg]
    have hround := arccos_cos_coe_angle_of_nonpos (ψ := psi θ) hsin
    exact ⟨cos_of_angle_eq (hangle.trans hround), sin_of_angle_eq (hangle.trans hround)⟩

/-- **Slot 0 of a candidate is the commanded angle.** The shoulder branch's cosine and sine, times
the branch's planar radius, are the wrist centre's first two components; `shoulderBranch` is what
makes that radius the configuration's own `a1 + planarQ`
(`a1_add_planarTargetQ_fk_shoulderBranch`), and the wrist centre of `fk` is that same radius times
the pair of `theta 1` (`wristX_fk`, `wristY_fk`). Cancelling the radius - the non-vanishing factor
`NonDegenerate`'s first clause names - leaves the two `(cos, sin)` pairs equal, and two equal pairs
are one angle modulo a full turn (`angle_eq_of_cos_eq_of_sin_eq`). -/
theorem shoulderAngle_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ)
    (h : g.a1 + planarQ g θ ≠ 0) :
    (shoulderAngle g (fk g θ) (shoulderBranch g θ) : Real.Angle) = (θ 0 : Real.Angle) := by
  have hcs := shoulderAngle_cos_sin g (fk g θ) (shoulderBranch g θ)
    (shoulderBranch_eq_one_or_neg_one g θ)
  rw [a1_add_planarTargetQ_fk_shoulderBranch g θ, wristX_fk, wristY_fk] at hcs
  refine angle_eq_of_cos_eq_of_sin_eq ?_ ?_
  · exact mul_left_cancel₀ h hcs.1
  · exact mul_left_cancel₀ h hcs.2

/-- **Slot 1 of a candidate is the commanded angle.** The elbow step is `atan2 h q - atan2 v u` at
the branch's own `(u, v)`, and `RealAtan2.atan2_rotate_coe_angle` says that difference is the angle
turning `(u, v)` into `(q, h)` - the hypotheses it needs being that the two pairs have the same
length, which is the law of cosines read at `cos (elbowAngle ..) = cos psi` on one side and at
`(planarQ, planarH)` on the other, and that `(u, v)` does not vanish, which is exactly the case
`hfold` excludes: `linkOne_eq_linkTwo_of_planar_eq_zero` turns a vanishing pair into the fold-back's
three equations. `planarQAt_eq`/`planarHAt_eq` put the branch's pair and
`theta 1` on the right-hand side of the two rotation equations.

The hypothesis is the arm half's fold clause alone, not the whole of `NonDegenerate`: neither the
shoulder radius nor the wrist angle enters the elbow slot, and stating the clause by itself is what
lets the wrist-singularity theorem `exists_solution_sin_five_eq_zero` reuse this lemma where
`sin (theta 4) ≠ 0` is exactly what is being denied. -/
theorem elbowTheta2_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ)
    (hfold : ¬(g.linkOne = g.linkTwo ∧ planarQ g θ = 0 ∧ planarH g θ = 0)) :
    (elbowTheta2 g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) : Real.Angle) =
      (θ 1 : Real.Angle) := by
  have hQ := planarTargetQ_fk_shoulderBranch g θ
  have hH := planarTargetH_fk g θ
  have hcs := elbowAngle_cos_sin g θ
  -- The solver's own `(u, v)` at the recovered elbow angle is the configuration's.
  have hu : planarUAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ))
      = planarUAt g (psi θ) := by
    simp only [planarUAt, hcs.1]
  have hv : planarVAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ))
      = planarVAt g (psi θ) := by
    simp only [planarVAt, hcs.2]
  -- The two pairs have the same length: the law of cosines, read from either end.
  have hlen : planarTargetQ g (fk g θ) (shoulderBranch g θ) ^ 2 + planarTargetH g (fk g θ) ^ 2 =
      planarUAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) ^ 2 +
        planarVAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) ^ 2 := by
    rw [hQ, hH, planar_law_of_cosines g θ, ← planarUAt_sq_add_planarVAt_sq_of_cos_eq g hcs.1]
  -- The rotation identities: the configuration's planar target is its own `(u, v)` turned by
  -- `theta 1`, which is the pair's own definition read as `planarQAt`/`planarHAt`.
  have hrotc : planarTargetQ g (fk g θ) (shoulderBranch g θ) =
      planarUAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) * Real.cos (θ 1) -
        planarVAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) *
          Real.sin (θ 1) := by
    rw [hQ, planarQ_eq_planarQAt, planarQAt_eq, ← hu, ← hv]
  have hrots : planarTargetH g (fk g θ) =
      planarUAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) * Real.sin (θ 1) +
        planarVAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) *
          Real.cos (θ 1) := by
    rw [hH, planarH_eq_planarHAt, planarHAt_eq, ← hu, ← hv]
  -- A vanishing `(u, v)` would put the wrist centre on the frame-1 origin, which is the
  -- fold-back `NonDegenerate` rules out.
  have hne : (planarUAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)),
      planarVAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ))) ≠ (0, 0) := by
    intro h0
    have hu0 : planarUAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) = 0 := by
      simpa using congrArg Prod.fst h0
    have hv0 : planarVAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)) = 0 := by
      simpa using congrArg Prod.snd h0
    have hsq : planarQ g θ ^ 2 + planarH g θ ^ 2 = 0 := by
      rw [← hQ, ← hH, hlen, hu0, hv0]
      norm_num
    have hq : planarQ g θ = 0 := by
      nlinarith [sq_nonneg (planarQ g θ), sq_nonneg (planarH g θ)]
    have hh : planarH g θ = 0 := by
      nlinarith [sq_nonneg (planarQ g θ), sq_nonneg (planarH g θ)]
    exact hfold ⟨linkOne_eq_linkTwo_of_planar_eq_zero g θ hq hh, hq, hh⟩
  rw [elbowTheta2, Real.Angle.coe_sub,
    atan2_rotate_coe_angle (q := planarTargetQ g (fk g θ) (shoulderBranch g θ))
      (h := planarTargetH g (fk g θ))
      (u := planarUAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)))
      (v := planarVAt g (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)))
      (θ := θ 1) hne hlen hrotc hrots,
    add_sub_cancel_right]

/-- **Slot 2 of a candidate is the commanded angle.** The third joint's total angle is the elbow
angle plus the quarter turn `alpha3 = 90` imposes, so this is `elbowAngle_cos_sin` read back through
`angle_eq_of_cos_eq_of_sin_eq` and put through `Real.Angle.coe_add` - `Kinematics.psi` is defined as
`theta 2 - pi/2` for exactly this cancellation. -/
theorem elbowTheta3_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ) :
    (elbowTheta3 g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) : Real.Angle) =
      (θ 2 : Real.Angle) := by
  have hcs := elbowAngle_cos_sin g θ
  have hang : (elbowAngle g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) : Real.Angle)
      = (psi θ : Real.Angle) := angle_eq_of_cos_eq_of_sin_eq hcs.1 hcs.2
  have hpsi : psi θ + quarter = θ 2 := by
    simp only [psi]
    ring
  rw [elbowTheta3, Real.Angle.coe_add, hang, ← Real.Angle.coe_add, hpsi]

/-- **The relative rotation at a configuration's own branches is the commanded wrist rotation.**
`relativeRotation` factors the arm's rotation out of a pose by its transpose, and `fk`'s rotation is
the arm's rotation times the wrist's (`fk_R`); with slots 0 to 2 on their commanded angles
(`armRotation_congr`, which is where the arm's angles are allowed to differ by full turns) the factor
is the one `fk` built, and its orthogonality (`armRotation_orth`) cancels the transpose against it.
Everything the last three slots need about the pose is in this one equation. -/
theorem relativeRotationAt_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ)
    (h0 : (shoulderAngle g (fk g θ) (shoulderBranch g θ) : Real.Angle) = (θ 0 : Real.Angle))
    (h1 : (elbowTheta2 g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) : Real.Angle) =
      (θ 1 : Real.Angle))
    (h2 : (elbowTheta3 g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) : Real.Angle) =
      (θ 2 : Real.Angle)) :
    relativeRotationAt g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) =
      wristRotation (θ 3) (θ 4) (θ 5) := by
  have hA : armRotationAt g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)
      = armRotation (θ 0) (θ 1) (θ 2) := armRotation_congr h0 h1 h2
  rw [relativeRotationAt, relativeRotation, ← armRotationAt, hA, fk_R, ← Matrix.mul_assoc,
    armRotation_orth (θ 0) (θ 1) (θ 2), Matrix.one_mul]

/-- **A non-degenerate configuration is off the wrist singularity**, so the solver reads its last
three joints off the rotation rather than off the flattened branch `wristTheta4`/`wristTheta6` fall
back to. `Zyz`'s `wristRotation_hypot_third_column` is the step: the relative rotation's `hypot` -
the solver's `wristSine` - is `|sin (theta 4)|` at the commanded angles, and `NonDegenerate`'s third
clause says that absolute value is not zero. -/
theorem not_wristIsSingular_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ)
    (h : Real.sin (θ 4) ≠ 0)
    (hrel : relativeRotationAt g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) =
      wristRotation (θ 3) (θ 4) (θ 5)) :
    ¬ wristIsSingular g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) := by
  intro hs
  -- `wristIsSingular` is the abbreviation, so the equation has to be unfolded by hand before the
  -- `wristSine` definition can be rewritten into it.
  change wristSine g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) = 0 at hs
  rw [wristSine, hrel, wristRotation_hypot_third_column] at hs
  exact h (abs_eq_zero.mp hs)

/-- **The two half turns of a wrist read-back cancel.** Reading an outer wrist angle off a
`wristRotation` adds `pi` exactly when `sin (theta 4)` is positive
(`Zyz`'s `wristRotation_read_theta4_coe_angle` and `wristRotation_read_theta6_coe_angle`), and the
solver adds `pi` exactly when `wristBranch` is `+1` - the same condition, since `wristBranch` is the
sign of that same sine. So slots 3 and 5 each add one half turn on the mirrored branch and none on
the direct one: twice the same half turn, and `pi + pi = 0` modulo a full turn
(`Real.Angle.coe_pi_add_coe_pi`). This is the arithmetic that makes those two angles come back as
themselves rather than as their mirror. -/
theorem read_shift_add_mirror_shift (θ : Fin 6 → ℝ) :
    ((if 0 < Real.sin (θ 4) then Real.pi else 0 : ℝ) : Real.Angle) +
      ((if wristBranch θ < 0 then (0 : ℝ) else Real.pi : ℝ) : Real.Angle) = 0 := by
  by_cases hpos : 0 < Real.sin (θ 4)
  · -- A positive sine is the `+1` label, which is not `-1 < 0`-negative, so both shifts fire.
    have hwb : wristBranch θ = 1 := by simp only [wristBranch, ite_eq_left hpos]
    have hnot : ¬ (wristBranch θ < 0) := by
      rw [hwb]
      norm_num
    rw [ite_eq_left hpos, ite_eq_right hnot, Real.Angle.coe_pi_add_coe_pi]
  · -- A non-positive sine is the `-1` label, which is negative, so neither shift fires.
    have hwb : wristBranch θ = -1 := by simp only [wristBranch, ite_eq_right hpos]
    have hlt : wristBranch θ < 0 := by
      rw [hwb]
      norm_num
    rw [ite_eq_right hpos, ite_eq_left hlt, Real.Angle.coe_zero, zero_add]

/-- **Slot 3 of a candidate is the commanded angle.** Off the singularity the solver's fourth joint
is the read-back of the relative rotation, shifted by the mirror's half turn; `hrel` puts the
commanded wrist rotation in place of the read-back's argument, `Zyz`'s read-back turns its `atan2`
pair into `theta 3` plus its own half turn, and `read_shift_add_mirror_shift` cancels the two.
`NonDegenerate`'s third clause is a hypothesis the read-back needs - it is stated only for
`sin beta ≠ 0` - and `not_wristIsSingular_fk_shoulderBranch` is what takes the singular branch out of
the way first. -/
theorem wristTheta4_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ) (h : Real.sin (θ 4) ≠ 0)
    (hrel : relativeRotationAt g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) =
      wristRotation (θ 3) (θ 4) (θ 5)) :
    (wristTheta4 g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) (wristBranch θ) : Real.Angle)
      = (θ 3 : Real.Angle) := by
  have hsing := not_wristIsSingular_fk_shoulderBranch g θ h hrel
  rw [wristTheta4, ite_eq_right hsing, Real.Angle.coe_add, wristReadTheta4, hrel,
    wristRotation_read_theta4_coe_angle (θ 3) (θ 4) (θ 5) h, add_assoc,
    read_shift_add_mirror_shift θ, add_zero]

/-- **Slot 4 of a candidate is the commanded angle.** The fifth joint is `wristBranch` times the
`atan2` of the relative rotation's `hypot` and its `(3,3)` entry - the `sin`/`cos` pair of the middle
wrist angle at the commanded configuration - and `Zyz`'s `wristRotation_read_theta5_coe_angle` says
that product is `theta 4` itself whenever `sin (theta 4)` is not zero, its own case split being on
the very sign the branch multiplies by. -/
theorem wristTheta5_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ) (h : Real.sin (θ 4) ≠ 0)
    (hrel : relativeRotationAt g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) =
      wristRotation (θ 3) (θ 4) (θ 5)) :
    (wristTheta5 g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) (wristBranch θ) : Real.Angle)
      = (θ 4 : Real.Angle) := by
  rw [wristTheta5, wristBranch, wristSine, wristCosine, hrel]
  exact wristRotation_read_theta5_coe_angle (θ 3) (θ 4) (θ 5) h

/-- **Slot 5 of a candidate is the commanded angle.** The sixth joint is to the rotation's third row
what the fourth is to its third column: the read-back of the `(2,1)` entry against the negated
`(2,0)` one, shifted by the mirror's half turn - and `Zyz`'s
`wristRotation_read_theta6_coe_angle` reads `theta 5` out of that pair with the same `pi` the read
of the fourth slot adds, which `read_shift_add_mirror_shift` cancels against the solver's own on
both wrist branches. -/
theorem wristTheta6_fk_shoulderBranch (g : Geometry) (θ : Fin 6 → ℝ) (h : Real.sin (θ 4) ≠ 0)
    (hrel : relativeRotationAt g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) =
      wristRotation (θ 3) (θ 4) (θ 5)) :
    (wristTheta6 g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) (wristBranch θ) : Real.Angle)
      = (θ 5 : Real.Angle) := by
  have hsing := not_wristIsSingular_fk_shoulderBranch g θ h hrel
  rw [wristTheta6, ite_eq_right hsing, Real.Angle.coe_add, wristReadTheta6, hrel,
    wristRotation_read_theta6_coe_angle (θ 3) (θ 4) (θ 5) h, add_assoc,
    read_shift_add_mirror_shift θ, add_zero]

/-- **Completeness.** A commanded configuration that is not one of the degenerate cases
`NonDegenerate` names comes back among the candidates: the solver generates one labelled with the
configuration's own shoulder and elbow branches, and that candidate's six angles are the commanded
ones modulo a full turn.

The candidate is `candidateAngles` at the configuration's three branch labels, and its membership is
`mem_solutions` with the band test discharged by `elbowCosine_mem_Icc` at the planar target the
shoulder branch recovers - which is the configuration's own `(planarQ, planarH)`. The six angle
equations are one slot lemma each, slots 3 to 5 sharing the relative-rotation equation `hrel` the
first three slots produce.

The statement is the Lean form of `test_kinematics.py`'s
`test_random_fk_poses_recover_angles_and_branch_labels`: exact branch labels, and angles equal to the
commanded ones up to the full turns `Real.Angle` quotients by - the strongest form the claim can
take, since a pose cannot tell a joint angle apart from that angle plus a full turn. -/
theorem exists_solution_angles_eq (g : Geometry) (θ : Fin 6 → ℝ) (h : NonDegenerate g θ) :
    ∃ s ∈ solutions g (fk g θ), s.shoulder = shoulderBranch g θ ∧ s.elbow = elbowBranch g θ ∧
      ∀ i, (s.angles i : Real.Angle) = (θ i : Real.Angle) := by
  -- The candidate is the configuration's own branch triple, whose two arm slots are generated
  -- unconditionally within the family and whose band test passes by `elbowCosine_mem_Icc`.
  refine ⟨⟨candidateAngles g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) (wristBranch θ),
    shoulderBranch g θ, elbowBranch g θ⟩, ?_, rfl, rfl, ?_⟩
  · rw [mem_solutions]
    exact ⟨shoulderBranch g θ, elbowBranch g θ, wristBranch θ, shoulderBranch_eq_one_or_neg_one g θ,
      by rw [planarTargetQ_fk_shoulderBranch, planarTargetH_fk]; exact elbowCosine_mem_Icc g θ,
      elbowBranch_eq_one_or_neg_one g θ, wristBranch_eq_one_or_neg_one θ, rfl⟩
  · intro i
    -- The rotation equation slots 3 to 5 read their `atan2` pairs off, from the three arm slots.
    have hrel := relativeRotationAt_fk_shoulderBranch g θ (shoulderAngle_fk_shoulderBranch g θ h.1)
      (elbowTheta2_fk_shoulderBranch g θ h.2.1) (elbowTheta3_fk_shoulderBranch g θ)
    fin_cases i
    · exact shoulderAngle_fk_shoulderBranch g θ h.1
    · exact elbowTheta2_fk_shoulderBranch g θ h.2.1
    · exact elbowTheta3_fk_shoulderBranch g θ
    · exact wristTheta4_fk_shoulderBranch g θ h.2.2 hrel
    · exact wristTheta5_fk_shoulderBranch g θ h.2.2 hrel
    · exact wristTheta6_fk_shoulderBranch g θ h.2.2 hrel

/-! ## The wrist singularity

At the wrist singularity joints 4 and 6 share an axis, so a pose cannot tell them apart and
`exists_solution_angles_eq` cannot hold there - which is why `NonDegenerate` names `sin (theta 4) ≠ 0`
as a hypothesis rather than leaving it out. The solver still has a candidate for such a
configuration, though: the one `wristTheta4` pins its fourth joint at zero for, whose middle wrist
angle collapses to flat. That is the demand `test_kinematics.py`'s
`test_wrist_singularity_is_solvable` places on the solver, and it is the one degenerate case the arm
half of `NonDegenerate` carries on its own. -/

/-- **The wrist singularity is solvable, flat.** A commanded configuration with `sin (theta 4) = 0`
still comes back among the candidates, and the one that comes back is the flat one: its fourth joint
is pinned at zero and its fifth is `wristBranch` times `atan2 0 (cos (theta 4))`, whose sine is zero
on both branches. So the returned solution is itself at the singularity, which is exactly what
`test_kinematics.py`'s `test_wrist_singularity_is_solvable` asks of the solver.

The hypotheses are the arm half of `NonDegenerate` only. That is the point of the statement: the
clause `exists_solution_angles_eq` adds on top, `sin (theta 4) ≠ 0`, is exactly the one being
denied, and the arm's own two clauses - `hr` and `hfold` - are what keep slots 0 to 2 recoverable
and the relative rotation equal to the commanded wrist rotation. Everything from there on is
`Zyz`'s `wristRotation_hypot_third_column`, which reads the solver's `wristSine` at the commanded
angles as `|sin (theta 4)| = 0`. -/
theorem exists_solution_sin_five_eq_zero (g : Geometry) (θ : Fin 6 → ℝ)
    (hr : g.a1 + planarQ g θ ≠ 0)
    (hfold : ¬(g.linkOne = g.linkTwo ∧ planarQ g θ = 0 ∧ planarH g θ = 0))
    (h5 : Real.sin (θ 4) = 0) :
    ∃ s ∈ solutions g (fk g θ), s.angles 3 = 0 ∧ Real.sin (s.angles 4) = 0 := by
  -- The candidate is the configuration's own branch triple, exactly as in
  -- `exists_solution_angles_eq`; the band test does not mention `sin (theta 4)` at all.
  have hrel := relativeRotationAt_fk_shoulderBranch g θ (shoulderAngle_fk_shoulderBranch g θ hr)
    (elbowTheta2_fk_shoulderBranch g θ hfold) (elbowTheta3_fk_shoulderBranch g θ)
  -- The candidate is singular: the relative rotation's third-column `hypot` is `|sin (theta 4)|`,
  -- and `h5` says that is zero.
  have hsine : wristSine g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) = 0 := by
    rw [wristSine, hrel, wristRotation_hypot_third_column, h5, abs_zero]
  refine ⟨⟨candidateAngles g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) (wristBranch θ),
    shoulderBranch g θ, elbowBranch g θ⟩, ?_, ?_, ?_⟩
  · rw [mem_solutions]
    exact ⟨shoulderBranch g θ, elbowBranch g θ, wristBranch θ, shoulderBranch_eq_one_or_neg_one g θ,
      by rw [planarTargetQ_fk_shoulderBranch, planarTargetH_fk]; exact elbowCosine_mem_Icc g θ,
      elbowBranch_eq_one_or_neg_one g θ, wristBranch_eq_one_or_neg_one θ, rfl⟩
  · -- Slot 3 is the flat form `wristTheta4` takes at a vanishing sine: joint 4 is pinned at zero.
    show (candidateAngles g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ) (wristBranch θ)) 3 = 0
    rw [candidateAngles_three, wristTheta4]
    exact ite_eq_left hsine
  · -- Slot 4 of the candidate is `wristTheta5`, which at a zero sine is `wb * atan2 0 (cos ..)`.
    show Real.sin (candidateAngles g (fk g θ) (shoulderBranch g θ) (elbowBranch g θ)
      (wristBranch θ) 4) = 0
    rw [candidateAngles_four, wristTheta5, hsine]
    rcases wristBranch_eq_one_or_neg_one θ with hwb | hwb
    · -- The `+1` branch leaves the `atan2` pair's sine, which is `0` by `sin_atan2`.
      rw [hwb, Int.cast_one, one_mul, RealAtan2.sin_atan2]
      simp
    · -- The `-1` branch mirrors it, and `Real.sin_neg` carries the sign out.
      rw [hwb, Int.cast_neg, Int.cast_one, neg_one_mul, Real.sin_neg, RealAtan2.sin_atan2]
      simp

end Kinematics
