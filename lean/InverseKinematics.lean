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
  zero. See `wristAngles`.
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
target pose, so the hypotheses of the completeness theorem name exactly what is assumed:

* the wrist centre off the base axis (`a1 + q ≠ 0`, which is `r ≠ 0` - a wrist centre on the
  axis leaves the plane's azimuth, and so `theta1`, undetermined);
* not folded back onto the frame-1 origin with equal links (`L1 = L2 ∧ q = h = 0`, which
  leaves `theta2` undetermined);
* `sin theta5 ≠ 0`, since at the wrist singularity joints 4 and 6 share an axis and only
  `theta4 ± theta6` is observable.
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

/-- The elbow cosine at a configuration that produced the pose is the cosine of that
configuration's second-link direction, so it always lies inside the reachability band: the
branch matching the commanded angles is never rejected by the band test. -/
theorem elbowCosine_mem_Icc (g : Geometry) (θ : Fin 6 → ℝ) :
    elbowCosine g (planarQ g θ) (planarH g θ) ∈ Set.Icc (-1) 1 := by
  have hpos : (0 : ℝ) < 2 * g.linkOne * g.linkTwo := by
    nlinarith [g.linkOne_pos, g.linkTwo_pos]
  have hc : elbowCosine g (planarQ g θ) (planarH g θ) = Real.cos (psi θ) := by
    rw [elbowCosine, planar_law_of_cosines]
    rw [show g.linkOne ^ 2 + g.linkTwo ^ 2 + 2 * g.linkOne * g.linkTwo * Real.cos (psi θ) -
        g.linkOne ^ 2 - g.linkTwo ^ 2 = (2 * g.linkOne * g.linkTwo) * Real.cos (psi θ) by
      ring]
    exact mul_div_cancel_left₀ _ (ne_of_gt hpos)
  rw [hc]
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

end Kinematics
