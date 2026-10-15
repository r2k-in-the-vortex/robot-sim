module
-- `Lean.Data.Json` itself does not re-export its `Basic`/`Printer` halves publicly, so
-- the parts whose names this file uses are imported directly.
public import Lean.Data.Json.Basic
public import Lean.Data.Json.Printer
public import Mathlib.Algebra.Field.Rat
-- ℚ's order: `Rat.instLinearOrderedField` and with it the decidable `≤`/`<` that the
-- `Bool`-valued comparisons below - which are the whole content of this file - are decided by.
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import InverseKinematics

open Lean (Json)
open Matrix
open scoped Matrix

@[expose] public section

/-!
# Exact branch plans over the rationals

The solver's control flow is a dispatch over branch labels: which shoulder branches, which
elbow branches, which wrist branches. What feeds that dispatch is a handful of scalar
comparisons, and `InverseKinematics.lean` states them exactly - `shoulderRadius g T = 0` picks
the shoulder anchor, `elbowBranches g T σ` keeps both elbow labels exactly when
`elbowCosine g (planarTargetQ g T σ) (planarTargetH g T) ∈ Set.Icc (-1) 1`, `wristIsSingular`
is `wristSine g T σ ε = 0`, and `NonDegenerate`'s second clause is the fold-back
`g.linkOne = g.linkTwo ∧ planarQ g θ = 0 ∧ planarH g θ = 0`.
`crates/robot-kinematics/src/branch.rs` restates that layer over a `Field`, so it can be run
on the exact rationals as well as on `f64`. This file is the same restatement from the other
side: it evaluates the layer over `ℚ` and writes the resulting branch plans out as JSON, for
the Rust plan to be compared `==` against rather than against the thresholds `Tolerances`
documents as standing in for these predicates.

It is a restatement and not an instantiation, and the `ℝ` development is left unmodified:
this file imports `InverseKinematics` - so the generator re-elaborates whenever the
specification changes, rather than drifting from a stale copy - and defines nothing in it, so
nothing here can weaken what the proofs say. As in `KinematicsTestData.lean`, whose structure,
JSON writer and refuse-to-write-on-failure entry point this file copies, the mirror is held to
the specification by reading and by the invariants every case re-derives, not by the type
checker.

The reachability band is why this layer cannot be decided in `ℚ` alone. With
`q σ = σ * r - a1` and `r = sqrt rho`, the squared distance to the frame-1 origin is
`q σ ^ 2 + h ^ 2 = rho - 2 * σ * a1 * r + a1 ^ 2 + h ^ 2` - an element of the quadratic
extension `ℚ(√rho)`, not of `ℚ` - and the band test is a comparison in that extension. The
extension never has to be *represented*, only isolated and squared with sign care, which is
`leOfRadical` below; and what the radical is compared against is rational, because clearing
the band's positive denominator `2 * L1 * L2` and adding `L1 ^ 2 + L2 ^ 2` turns
`elbowCosine ∈ Set.Icc (-1) 1` into `(L1 - L2) ^ 2 ≤ q σ ^ 2 + h ^ 2 ≤ (L1 + L2) ^ 2`. So the
whole decision is a rational computation carrying `(alpha, beta, rho)`, and no square root is
ever taken, here or in the consumer.

Every numeral in the document is exact and every comparison is `==`. A case states its
expected plan as literals in the case itself, independent of the computation, and the
generator refuses to write a file if any case disagrees with its own literals or with any of
the invariants it claims about itself. Two of those invariants re-derive a decision a second
way: a case that states its radius as a rational has that radius checked to be the
non-negative square root of `rho` and then has the band and the fold-back re-decided through
`elbowCosine` with the root substituted, and a case that states the ZYZ pairs of its relative
rotation has the matrix re-derived from them. Both routes have to agree before anything is
written.

Regenerate the data with, from `lean/`:

    lake exe branch_decision_q ../test_data/branch_plans.json
-/

namespace BranchDecisionQ

/-- A vector in `ℚ^3` with exact rational components. -/
abbrev Vec := Fin 3 → ℚ

/-- A 3x3 matrix with exact rational entries. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℚ

/-! ## The decision layer, restated over ℚ

The definitions below are `branch.rs`'s, transliterated: the same five-way split of the
radical comparison, the same sign condition on the root of the extension, the same reading of
the wrist singularity off two entries of `R_3^6`, and the same plan assembled from them. Each
doc comment names the Lean theorem or definition the Rust function mirrors. -/

/-- Whether `m ≤ k * sqrt rho`, decided without taking the square root.

This is the whole of the quadratic extension the reachability band needs, and it is
`branch.rs`'s `le_of_radical`. The radical is isolated - `m ≤ k * sqrt rho` - and the decision
splits on the sign of its coefficient, because squaring is reversible only where both sides
are non-negative:

* `k = 0`: the radical is gone and the comparison is rational, exactly `m ≤ 0`;
* `k < 0`: `k * sqrt rho ≤ 0`, so `m > 0` decides `false` outright, and otherwise both sides
  are non-positive and `m ≤ k * sqrt rho` is `k * k * rho ≤ m * m` - the inequality negated
  before it is squared, which is the sign care the whole restatement turns on;
* `k > 0`: `k * sqrt rho ≥ 0`, so `m ≤ 0` decides `true` outright, and otherwise
  `m ≤ k * sqrt rho` is `m * m ≤ k * k * rho`.

`rho` is a sum of two squares and so non-negative, which is what makes the two squarings
legitimate; it is the only precondition the function has. -/
def leOfRadical (m k rho : ℚ) : Bool :=
  if k = 0 then
    decide (m ≤ 0)
  else if decide (m ≤ 0) then
    if decide (0 < k) then true else decide (k * k * rho ≤ m * m)
  else if decide (0 < k) then
    decide (m * m ≤ k * k * rho)
  else
    false

/-- Whether `alpha + beta * sqrt rho = 0`, decided without taking the square root.

`branch.rs`'s `radical_eq_zero`, the fold-back clause: the branch's planar target
`q σ ^ 2 + h ^ 2` is the extension value `alpha + beta * sqrt rho`, and this is the test that
it vanishes. Squaring `alpha = -beta * sqrt rho` gives `alpha ^ 2 = beta ^ 2 * rho`, which is
necessary but not sufficient - the sign has to match too, which is `alpha * beta ≤ 0` because
`sqrt rho` is non-negative. `alpha = beta = 0` satisfies both, which is right: it is the zero
of the extension whatever `rho` is. -/
def radicalEqZero (alpha beta rho : ℚ) : Bool :=
  decide (alpha * alpha = beta * beta * rho) && decide (alpha * beta ≤ 0)

/-- The wrist decision for a rational relative rotation: `wristIsSingular`, i.e.
`wristSine g T σ ε = 0`, with the sine read off `R_3^6`.

`Zyz.wristRotation_hypot_third_column` says `wristSine` is `hypot (Q 0 2) (Q 1 2)`, and
`hypot x y = 0` holds exactly when `x = 0` *and* `y = 0` - so the predicate is rational and
needs no square root, which is `branch.rs`'s `wrist_plan_exact`. It is a conjunction and not a
disjunction: one vanishing entry leaves the sine non-zero. -/
def wristPlanExact (Q : Mat) : Bool :=
  decide (Q 0 2 = 0) && decide (Q 1 2 = 0)

/-- The branch sign a shoulder label names, as the rational the arithmetic multiplies by:
`branch.rs`'s `branch_sign`. -/
def branchSign (sigma : ℤ) : ℚ := if sigma = 1 then 1 else -1

/-- The radical's coefficient for one shoulder branch: `beta σ = -2 * σ * a1`, the coefficient
of `sqrt rho` in `q σ ^ 2 + h ^ 2`. -/
def branchBeta (a1 : ℚ) (sigma : ℤ) : ℚ := -(2 * branchSign sigma * a1)

/-- The scalars the exact plan is decided from: `branch.rs`'s `ExactTarget`.

`radiusSq` is `rho = x4 ^ 2 + y4 ^ 2`, the square of `shoulderRadius g T` rather than the
radius; `height` is `planarTargetH g T`, which is `z4 - d1`; and the two link lengths are
`Geometry.linkOne` and `linkTwo`. Every field is rational when the target pose is, because the
solver's only square root is the radial one and this file carries it symbolically. -/
structure Target where
  radiusSq : ℚ
  a1 : ℚ
  height : ℚ
  linkOne : ℚ
  linkTwo : ℚ

/-- `ExactTarget::of_center`, from the components of a wrist centre. -/
def Target.ofCenter (a1 d1 linkOne linkTwo : ℚ) (center : Vec) : Target :=
  { radiusSq := center 0 * center 0 + center 1 * center 1
    a1 := a1
    height := center 2 - d1
    linkOne := linkOne
    linkTwo := linkTwo }

/-- A pair of decisions in generation order: the `+1` branch first, then the `-1` one - the
order `[1, -1] : List ℤ` gives the outer `flatMap` of `solutions`. Two named fields rather
than an array, so a reader of a case does not have to remember which slot is which. -/
structure PerShoulder where
  pos : Bool
  neg : Bool

/-- The shoulder branches in generation order, `branch.rs`'s `SHOULDER_BRANCHES`. -/
def shoulderBranches : List ℤ := [1, -1]

/-- The wrist labels `solutions` generates for every surviving arm branch, unconditionally:
`WristBranches::both()`, whose labels are `branch.rs`'s `WRIST_BRANCHES`. The singularity does
not remove a label - it changes the angles the label produces. -/
def wristLabels : List ℤ := [1, -1]

/-- The elbow labels `elbowBranches g T σ` returns: `[1, -1]` when the band test holds and
`[]` when it does not. Lean's test is a single membership, so the two labels are kept together
or not at all - `+1` alone and `-1` alone are not values the solver can produce. -/
def elbowLabels (kept : Bool) : List ℤ := if kept then [1, -1] else []

/-- Everything the dispatch over a target pose reads, before any angle is computed:
`branch.rs`'s `BranchPlan`, whose `Plan.exact` this is.

`radiusIsZero` and `wristCenterOnBaseAxis` are the same predicate - `shoulderRadius g T = 0`,
`NonDegenerate`'s first clause negated - recorded twice because the Rust plan carries it in
two places: per shoulder branch, as `ShoulderPlan.radius_is_zero` (`shoulderAngle` tests one
radius for both branches), and once for the pose, as `Degeneracy.wrist_center_on_base_axis`.
The generator checks that the two shoulder slots agree and that the two fields agree, so the
document's single `radius_is_zero` and its `wrist_center_on_base_axis` cannot drift apart. -/
structure Plan where
  /-- `shoulderRadius g T = 0`, per shoulder branch. -/
  radiusIsZero : PerShoulder
  /-- `elbowBranches g T σ`, as the band test's Boolean, per shoulder branch. -/
  elbowBranches : PerShoulder
  /-- `NonDegenerate`'s first clause negated, at the pose. -/
  wristCenterOnBaseAxis : Bool
  /-- `NonDegenerate`'s second clause negated, per shoulder branch: the branch's planar target
  vanishes, `q σ = 0` with `h = 0`, and the links are equal. -/
  foldBack : PerShoulder

/-- The exact plan: `shoulderAngle`'s anchor, `elbowBranches`' band membership and the
fold-back clause, decided in `ℚ(√rho)` with no tolerance anywhere. `BranchPlan::exact`.

The band's two bounds are `(L1 - L2) ^ 2` and `(L1 + L2) ^ 2`, rational after the positive
denominator is cleared; `alpha = rho + a1 ^ 2 + h ^ 2` is the extension's rational part and
`beta σ = -2 * σ * a1` its radical coefficient, because `sigma ^ 2 = 1` collapses
`(σ * r) ^ 2` to `rho`. `alpha + beta * sqrt rho >= lower` is `lower - alpha <= beta * sqrt rho`
and `alpha + beta * sqrt rho <= upper` is `alpha - upper <= -beta * sqrt rho`, which is the
two `leOfRadical` calls. -/
def planExact (t : Target) : Plan :=
  let rho := t.radiusSq
  let alpha := rho + t.a1 * t.a1 + t.height * t.height
  let lower := (t.linkOne - t.linkTwo) * (t.linkOne - t.linkTwo)
  let upper := (t.linkOne + t.linkTwo) * (t.linkOne + t.linkTwo)
  let reachable (sigma : ℤ) : Bool :=
    let beta := branchBeta t.a1 sigma
    leOfRadical (lower - alpha) beta rho && leOfRadical (alpha - upper) (-beta) rho
  let foldsBack (sigma : ℤ) : Bool :=
    decide (t.linkOne = t.linkTwo) && decide (t.height = 0)
      && radicalEqZero alpha (branchBeta t.a1 sigma) rho
  let radiusIsZero := decide (rho = 0)
  { radiusIsZero := ⟨radiusIsZero, radiusIsZero⟩
    elbowBranches := ⟨reachable 1, reachable (-1)⟩
    wristCenterOnBaseAxis := radiusIsZero
    foldBack := ⟨foldsBack 1, foldsBack (-1)⟩ }

/-- How many candidates a plan generates, before any is discarded: every kept elbow branch
generates `wristLabels.length` of them, which is `branch.rs`'s `candidate_count` and
`length_solutions_le_eight`'s bound computed rather than asserted. A plan with an empty elbow
family contributes nothing, which is where a pose no branch reaches turns into an empty
candidate list. -/
def candidateCount (p : Plan) : Nat :=
  (elbowLabels p.elbowBranches.pos).length * wristLabels.length
    + (elbowLabels p.elbowBranches.neg).length * wristLabels.length

/-! ## The band the long way round, and the rotation the ZYZ way

Two routes that do not go through the radical comparison, available for the cases that can
afford them. The first needs `√rho` to be rational, which is exactly what the radical route
exists to avoid, so it covers only the cases that state their radius; the second needs the
rotation to be a ZYZ product, which every case but the two that pin the wrist test as a
conjunction states. They are what makes those cases cross-checked rather than merely
self-consistent. -/

/-- The band test for a target whose radius `r` is rational: `elbowCosine` at the branch's
planar target, compared against `Set.Icc (-1) 1` with its positive denominator `2 * L1 * L2`
cleared. This is the route `BranchPlan::of_pose` takes, through `chain::planar_target` and
`chain::elbow_cosine`, with `q σ = σ * r - a1` in place of the isolated radical. -/
def reachableViaCosine (t : Target) (r : ℚ) (sigma : ℤ) : Bool :=
  let q := branchSign sigma * r - t.a1
  let distanceSq := q * q + t.height * t.height
  let known := t.linkOne * t.linkOne + t.linkTwo * t.linkTwo
  let denominator := 2 * t.linkOne * t.linkTwo
  decide (-denominator ≤ distanceSq - known) && decide (distanceSq - known ≤ denominator)

/-- The fold-back for a target whose radius is rational: `NonDegenerate`'s second clause as it
is written, `linkOne = linkTwo ∧ q = 0 ∧ h = 0`, with `q σ = σ * r - a1` evaluated. -/
def foldsBackViaPlanar (t : Target) (r : ℚ) (sigma : ℤ) : Bool :=
  decide (t.linkOne = t.linkTwo) && decide (branchSign sigma * r - t.a1 = 0)
    && decide (t.height = 0)

/-- The cosine/sine pair of one wrist angle. `Kinematics` carries the angle itself; the ZYZ
product reads it only through these two numbers, and unlike the angle they can be rational -
which is what lets a case state a rotation the decision can be run on. The pair is not
required to be normalised: the product never re-derives one entry from the other. -/
structure CosSin where
  cos : ℚ
  sin : ℚ

/-- Rotation about the y axis, given its cosine and sine. `Kinematics.rotY` at `ℚ`. -/
def rotY (x : CosSin) : Mat := !![x.cos, 0, x.sin; 0, 1, 0; -x.sin, 0, x.cos]

/-- Rotation about the z axis, given its cosine and sine. `Kinematics.rotZ` at `ℚ`. -/
def rotZ (x : CosSin) : Mat := !![x.cos, -x.sin, 0; x.sin, x.cos, 0; 0, 0, 1]

/-- The rotation from frame 3 to frame 6: `Kinematics.wristRotation` at `ℚ`, with the middle
angle negated as it is there. The `alpha4 = 90`, `alpha5 = -90` twists conjugate the three z
rotations into a ball joint, so the wrist reads as ZYZ rather than ZXZ and its third column's
first two entries are `-cos θ4 * sin θ5` and `-sin θ4 * sin θ5`: they vanish together, which
is why no rotation pins the wrist test as a disjunction. -/
def wristRotation (θ4 θ5 θ6 : CosSin) : Mat := rotZ θ4 * rotY ⟨θ5.cos, -θ5.sin⟩ * rotZ θ6

/-! ## Geometries

The two arms the corpus runs on, with the names the forward-chain corpus uses. Neither case
below reads the tool offset `Geometry.toolOffset` - `wristCenter` is the end-effector origin
pulled back along frame 6's z axis, and none of the decision layer's predicates looks at
anything else - so a geometry here is four numbers and not five. -/

/-- A geometry with the name a case refers to it by. -/
structure NamedGeometry where
  name : String
  /-- `Geometry.a1`. -/
  a1 : ℚ
  /-- `Geometry.d1`. -/
  d1 : ℚ
  /-- `Geometry.linkOne`, the DH table's `a2`. -/
  linkOne : ℚ
  /-- `Geometry.linkTwo`, the DH table's `d4`. -/
  linkTwo : ℚ
  /-- What the geometry is here for. -/
  note : String

/-- The exact target a case's wrist centre makes of a geometry. -/
def NamedGeometry.targetAt (ng : NamedGeometry) (center : Vec) : Target :=
  Target.ofCenter ng.a1 ng.d1 ng.linkOne ng.linkTwo center

/-- The geometry `robot_parameters.json` ships: `a1 = 10`, `d1 = 40`, `a2 = 40`, `d4 = 40`. -/
def shipped : NamedGeometry :=
  { name := "shipped"
    a1 := 10
    d1 := 40
    linkOne := 40
    linkTwo := 40
    note := "the arm `robot_parameters.json` ships, whose equal links make the fold-back \
      clause reachable and whose `(L1 - L2) ^ 2` is zero make the inner band edge attainable \
      only by folding the second link back onto the first" }

/-- The second arm of the forward-chain corpus: `a1 = 0`, `d1 = 25`, `a2 = 30`, `d4 = 12`.

`a1 = 0` makes `beta σ = -2 * σ * a1` vanish on both shoulder branches, so every comparison
this arm makes takes `leOfRadical`'s `k = 0` arm - the one that measures the distance against
zero and never squares anything. `linkOne ≠ linkTwo` makes the fold-back clause unreachable
here, so the two arms' cases do not overlap in what they decide. -/
def shortArm : NamedGeometry :=
  { name := "short_arm"
    a1 := 0
    d1 := 25
    linkOne := 30
    linkTwo := 12
    note := "the forward-chain corpus's second arm; `a1 = 0` puts the frame-1 origin on the \
      base rotation axis, which is what exercises `leOfRadical`'s `k = 0` arm, and \
      `linkOne ≠ linkTwo` makes the fold-back clause unreachable on it" }

def geometries : List NamedGeometry := [shipped, shortArm]

/-! ## Cases

One case per decision the corpus exists to pin down. A case states its own expected plan as
literals - independent of the computation, and checked against it before anything is written -
and the ones that can afford the extra hypothesis state their radius as a rational, so the
band is re-decided through `elbowCosine` as well, or the ZYZ pairs of their relative rotation,
so the matrix is re-derived from them.

The centres are the wrist centre `(x4, y4, z4)`, and `branch` names which of `leOfRadical`'s
five arms the case is written for; the first four comparisons of a `shipped` case enter four
different arms among them, so the tag names the one the case is *about*. -/

/-- The values a case expects the decision layer to produce, written out by hand.

`candidateCount` is `candidateCount` of the computed plan, `wristSingular` is
`wristPlanExact` of the case's rotation, and the rest are `branch.rs`'s `BranchPlan` fields
under the JSON's names. -/
structure Expected where
  radiusIsZero : Bool
  elbowBranches : PerShoulder
  wristCenterOnBaseAxis : Bool
  foldBack : PerShoulder
  wristSingular : Bool
  candidateCount : Nat

/-- One case: an arm, a wrist centre, the relative rotation the wrist decision reads, and what
the decision layer is expected to say about them. -/
structure Case where
  name : String
  /-- The arm the case runs on. -/
  geometry : NamedGeometry
  /-- The decision the case pins down. -/
  note : String
  /-- The `leOfRadical` arm the case is written for, as one of `branchTags`. -/
  branch : String
  /-- The wrist centre `(x4, y4, z4)`, whose first two components give `rho`. -/
  center : Vec
  /-- The relative rotation `R_3^6` the wrist decision reads its two entries from. -/
  relativeRotation : Mat
  /-- The ZYZ pairs of the relative rotation, when it is a wrist rotation. `none` for the
  matrices that are deliberately not rotations: `wristRotation`'s third column vanishes in its
  first two entries together, so a matrix with exactly one of them zero is the only witness
  that the singularity test is a conjunction, and it cannot be a rotation. -/
  zyz : Option (CosSin × CosSin × CosSin) := none
  /-- `√rho` as a rational, when `rho` is a perfect square. Stating it obliges the case: the
  generator checks it is the non-negative root and re-decides the band and the fold-back
  through `elbowCosine` with it substituted. -/
  radius : Option ℚ := none
  /-- The plan the case expects, as literals. -/
  expected : Expected

/-- The identity rotation, as a ZYZ product with both outer angles zero. -/
def identityRotation : Mat := wristRotation ⟨1, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩

/-- A quarter turn about the z axis, as a ZYZ product with the middle angle zero. -/
def quarterTurnRotation : Mat := wristRotation ⟨0, 1⟩ ⟨1, 0⟩ ⟨1, 0⟩

/-- A ZYZ product with the middle angle a Pythagorean pair: neither of the third column's
first two entries is zero, so this is a rotation off the wrist singularity. -/
def genericWristRotation : Mat :=
  wristRotation ⟨4 / 5, 3 / 5⟩ ⟨5 / 13, 12 / 13⟩ ⟨15 / 17, 8 / 17⟩

/-- A ZYZ product with the middle angle zero and both outer angles non-zero: the two z
rotations merge and the third column is `(0, 0, 1)`, so this rotation is at the singularity
without being the identity. -/
def flatWristRotation : Mat :=
  wristRotation ⟨4 / 5, 3 / 5⟩ ⟨1, 0⟩ ⟨15 / 17, -8 / 17⟩

/-- A matrix with `Q 0 2 = 0` and `Q 1 2 = 1 / 2`: one of the two entries vanishes and the
sine is `hypot 0 (1 / 2) = 1 / 2`. Not a rotation - only the two entries are read, and this is
the witness that they are read as a conjunction. -/
def oneEntryZeroFirst : Mat := !![1, 0, 0; 0, 1, 1 / 2; 0, 0, 1]

/-- The mirror of `oneEntryZeroFirst`: `Q 1 2 = 0` and `Q 0 2 = 2 / 3`, so the sine is
`hypot (2 / 3) 0 = 2 / 3`. Also not a rotation. -/
def oneEntryZeroSecond : Mat := !![1, 0, 2 / 3; 0, 1, 0; 0, 0, 1]

/-- The cases. The `shipped` entries exercise all four of `leOfRadical`'s non-zero arms among
them - each entry makes four comparisons, and the lower-edge comparison of the `+1` branch and
the upper-edge comparison of the `-1` one are the two that square with a negative coefficient -
and the `short_arm` entries exercise the `k = 0` arm, on both band edges and from both sides of
each. -/
def cases : List Case := [
  -- `rho = 0`: the wrist centre on the base rotation axis. The anchor `shoulderAngle` names,
  -- and the case that pins `radius_is_zero` and `wrist_center_on_base_axis` as one predicate.
  { name := "shipped/wrist_center_on_base_axis"
    geometry := shipped
    note := "rho = 0: the wrist centre on the base rotation axis, `NonDegenerate`'s first \
      clause negated. Three of the four comparisons are decided by a sign alone - two of them \
      by `m ≤ 0` on the `k > 0` side - and the two that do square find `k * k * rho = 0`, \
      which they can only get right because they compare `m * m ≥ 0 ∈ ...` the right way \
      round."
    branch := "m_nonpos_k_neg"
    center := ![0, 0, 40]
    relativeRotation := identityRotation
    zyz := some (⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩)
    radius := some 0
    expected :=
      { radiusIsZero := true
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := true
        foldBack := ⟨false, false⟩
        wristSingular := true
        candidateCount := 8 } },
  -- The same anchor, at a height where the elbow cosine is unremarkable: the two decisions
  -- are independent, and this is the case that shows the `rho = 0` arm is not merely a
  -- boundary of the band.
  { name := "shipped/wrist_center_on_base_axis_above_the_frame_one_origin"
    geometry := shipped
    note := "rho = 0 again, at a height: `q σ = -a1` on both branches, and `q ^ 2 + h ^ 2` is \
      `500` - well inside the band - where the case below has it exactly at the inner edge. \
      An off-singularity rotation, so the two halves of the plan are seen to be independent."
    branch := "m_nonpos_k_pos"
    center := ![0, 0, 60]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    radius := some 0
    expected :=
      { radiusIsZero := true
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := true
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  -- The fold-back. `NonDegenerate`'s second clause, and the one pose where the two shoulder
  -- branches disagree about it, because the clause's sign half is per branch.
  { name := "shipped/the_fold_back"
    geometry := shipped
    note := "The fold-back: with `r = 10` the centre `(10, 0, 40)` is the frame-1 origin \
      itself, `q +1 = r - a1 = 0`, `h = 0`, and `linkOne = linkTwo`. Only `σ = +1` satisfies \
      `radicalEqZero`'s sign half `alpha * beta ≤ 0`: `beta = -2 * σ * a1` is `-20` there and \
      `+20` on `σ = -1`, against `alpha = 200 > 0`, so `fold_back` is `[true, false]` and the \
      case pins which shoulder owns the fold. The same comparison is the lower band edge hit \
      exactly - `q +1 ^ 2 + h ^ 2 = 0 = (L1 - L2) ^ 2` - and it reaches it through the \
      sign-care arm at that arm's own boundary, `k * k * rho = m * m = 40000`."
    branch := "m_nonpos_k_neg"
    center := ![10, 0, 40]
    relativeRotation := quarterTurnRotation
    zyz := some (⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩)
    radius := some 10
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨true, false⟩
        wristSingular := true
        candidateCount := 8 } },
  -- The fold-back's neighbour, which is not the fold-back. `h = 0` exactly, not `h ≈ 0`.
  { name := "shipped/the_fold_back_neighbour_above"
    geometry := shipped
    note := "The fold-back's neighbour, a millionth of a unit higher: `q +1 ^ 2 + h ^ 2` is \
      `10 ^ -12` instead of `0`, so every elbow decision is the fold-back's - the pose is \
      still reachable on both branches - and the plan differs from it in one field only, \
      `fold_back`, which is now `[false, false]`. This is the case that pins the clause as \
      `h = 0` exactly rather than as a small height, and it is also an instance of the \
      sign-care arm's strict inequality: `m * m = 40000 + ... > k * k * rho = 40000`."
    branch := "m_nonpos_k_neg"
    center := ![10, 0, 40000001 / 1000000]
    relativeRotation := flatWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨1, 0⟩, ⟨15 / 17, -8 / 17⟩)
    radius := some 10
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := true
        candidateCount := 8 } },
  -- The same height as the fold-back with a radius that is not a rational square: the
  -- extension is entered, and never has to be evaluated.
  { name := "shipped/a_non_square_radius"
    geometry := shipped
    note := "The fold-back's height with `rho = 50`, which is not a rational square, so the \
      decision is made in `Q(sqrt 50)` and `√50` is never needed: the lower-edge comparison \
      of the `+1` branch is `m = -150 ≤ -20 * sqrt 50` decided as `k * k * rho = 20000 ≤ \
      m * m = 22500`, strictly - a `≤` in place of the `≥` there would drop a reachable pose, \
      which is the sign care this case exists to catch."
    branch := "m_nonpos_k_neg"
    center := ![5, 5, 40]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  -- Well inside the band, off the x axis, with the radius a perfect square so both routes to
  -- the band are available and have to agree.
  { name := "shipped/well_inside_the_band_off_axis"
    geometry := shipped
    note := "Well inside on both branches: `rho = 3600 = 60 ^ 2` off the x axis, `q +1 = 50` \
      and `q -1 = -70`, so `q +1 ^ 2 + h ^ 2 = 2500` and `q -1 ^ 2 + h ^ 2 = 4900` are both \
      inside `[0, 6400]` with room to spare. The `k = 0` arm is the one this arm never takes: \
      both lower-edge comparisons reach `m ≤ 0` with `k ≠ 0` and decide on the sign."
    branch := "m_nonpos_k_pos"
    center := ![48, 36, 40]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    radius := some 60
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  -- The upper edge approached from inside. The three heights below, with one centre and one
  -- rotation, are what pin the band as a closed interval.
  { name := "shipped/inside_the_upper_edge_by_a_hair"
    geometry := shipped
    note := "The outer band edge approached from inside by a millionth of a unit: `alpha - \
      6400 = 200 - 160 / 10 ^ 6 + 10 ^ -12 > 0`, so the `+1` branch's upper comparison takes \
      the arm that decides by squaring - `m * m ≤ k * k * rho`, strictly here - and says \
      reachable, while `σ = -1`, twenty units further out, is dropped."
    branch := "m_pos_k_pos"
    center := ![10, 0, 119999999 / 1000000]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    radius := some 10
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, false⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 4 } },
  { name := "shipped/the_upper_edge_exactly"
    geometry := shipped
    note := "The upper band edge hit exactly: `q +1 = 0` with `h = 80 = L1 + L2`, so \
      `q +1 ^ 2 + h ^ 2 = 6400` and the arm is stretched straight out. `Set.Icc (-1) 1` \
      includes its ends, so the `+1` branch is reachable, and the squaring arm meets it at \
      `m * m = k * k * rho = 40000` exactly. `σ = -1` at `q -1 = -20` has `6800 > 6400` and is \
      dropped, so one pose carries both answers. With `a1 ≠ 0` an exact edge forces `rho` to \
      be a rational square - the edge equation is linear in `r = sqrt rho`, so `r` must be \
      rational to hold at a rational centre - and here it is `10`."
    branch := "m_pos_k_pos"
    center := ![10, 0, 120]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    radius := some 10
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, false⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 4 } },
  { name := "shipped/outside_the_upper_edge_by_a_hair"
    geometry := shipped
    note := "The same edge from outside, by the same millionth: the `+1` branch's squaring arm \
      now has `m * m > k * k * rho` and the branch is dropped, and `σ = -1` is dropped with \
      it, so `candidate_count` is 0. With the two cases above it fixes the band as the closed \
      interval `[0, 6400]` at three heights one millionth apart: a strict inequality at either \
      end of the test gets one of the three wrong."
    branch := "m_pos_k_neg"
    center := ![10, 0, 120000001 / 1000000]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    radius := some 10
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨false, false⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 0 } },
  -- The same edge from the other shoulder branch: there the sign-care arm is the one that
  -- reaches it.
  { name := "shipped/the_upper_edge_exactly_mirrored"
    geometry := shipped
    note := "The same edge from the other shoulder branch: `(70, 0, 40)` puts `q -1 = -80` on \
      the edge and leaves `σ = +1`, at `q +1 = 60`, strictly inside. The edge comparison is \
      then `m = alpha - 6400 = -1400 ≤ 0` with `k = -20 < 0` - the sign-care arm - and it \
      meets that arm's boundary `k * k * rho = m * m = 1960000` exactly, where the `+1` edge \
      case meets the squaring arm's. The two `m * m` comparisons of the band are therefore \
      pinned at equality, one by each shoulder branch."
    branch := "m_nonpos_k_neg"
    center := ![70, 0, 40]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    radius := some 70
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  -- The anchor decision and the band decision are independent: `rho = 0` with the height past
  -- the reach drops both branches.
  { name := "shipped/on_the_base_axis_out_of_reach"
    geometry := shipped
    note := "rho = 0 with `h = 100`: the wrist centre is on the base axis, so \
      `radius_is_zero` and `wrist_center_on_base_axis` are true, and `q σ ^ 2 + h ^ 2 = 10100` \
      is past `(L1 + L2) ^ 2 = 6400`, so both branches are dropped and the count is 0. The \
      anchor is a decision about `rho` alone and says nothing about reachability."
    branch := "m_pos_k_neg"
    center := ![0, 0, 140]
    relativeRotation := identityRotation
    zyz := some (⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩)
    radius := some 0
    expected :=
      { radiusIsZero := true
        elbowBranches := ⟨false, false⟩
        wristCenterOnBaseAxis := true
        foldBack := ⟨false, false⟩
        wristSingular := true
        candidateCount := 0 } },
  { name := "shipped/upper_edge_with_an_off_axis_center"
    geometry := shipped
    note := "The `+1` upper edge again, with `y ≠ 0` and both halves of the centre rational \
      rather than integral: `rho = 3364 = 58 ^ 2`, `q +1 = 48`, `h = 64`. `(48, 64)` is a \
      Pythagorean point, so `q +1 ^ 2 + h ^ 2 = 6400` exactly and `m * m = k * k * rho` again \
      holds with equality; `σ = -1`, at `q -1 = -68`, has `8720 > 6400` and is dropped."
    branch := "m_pos_k_pos"
    center := ![174 / 5, 232 / 5, 104]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    radius := some 58
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, false⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 4 } },
  -- ---- `short_arm`: `a1 = 0`, so every comparison here takes `leOfRadical`'s `k = 0` arm.
  { name := "short_arm/wrist_center_on_base_axis"
    geometry := shortArm
    note := "rho = 0 on the arm with `a1 = 0`: `beta σ = -2 * σ * a1` vanishes on both \
      branches, so all four comparisons take the `k = 0` arm and both shoulder branches read \
      the same band. The centre is the frame-1 origin itself, and with links 30 and 12 it lies \
      inside the inner dead zone: `alpha = 0 < (L1 - L2) ^ 2 = 324`, so `m ≤ 0` is false and \
      the plan is empty. A dead zone is where the inner edge is violated on the small side."
    branch := "k_zero"
    center := ![0, 0, 25]
    relativeRotation := identityRotation
    zyz := some (⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩)
    radius := some 0
    expected :=
      { radiusIsZero := true
        elbowBranches := ⟨false, false⟩
        wristCenterOnBaseAxis := true
        foldBack := ⟨false, false⟩
        wristSingular := true
        candidateCount := 0 } },
  { name := "short_arm/a_square_radius"
    geometry := shortArm
    note := "A rational-square radius: `rho = 324 = 18 ^ 2` with `alpha = 324 + 400 = 724`, \
      strictly inside `[324, 1764]`. Both routes to the band are available here - the radical \
      route and `elbowCosine` with `r = 18` substituted - and the generator requires them to \
      agree before writing."
    branch := "k_zero"
    center := ![18, 0, 45]
    relativeRotation := oneEntryZeroFirst
    radius := some 18
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  { name := "short_arm/a_non_square_radius_at_the_same_height"
    geometry := shortArm
    note := "The same geometry and the same height as the case above, with `rho = 2` where \
      that one has `rho = 324`: the decision is unchanged, because with `a1 = 0` the band is \
      `alpha ∈ [324, 1764]` and `alpha` is `402` here against `724` there. `sqrt 2` is \
      irrational, so this decision is made in `Q(sqrt 2)`; the extension is entered and the \
      root is never taken. The radius route is unavailable here, which is the point of the \
      radical route existing at all."
    branch := "k_zero"
    center := ![1, 1, 45]
    relativeRotation := oneEntryZeroSecond
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  { name := "short_arm/inside_the_inner_edge_by_a_hair"
    geometry := shortArm
    note := "The inner band edge from inside, by a millionth of a unit: `alpha = rho + h ^ 2 = \
      180 + (12 + 10 ^ -6) ^ 2 = 324 + 24 / 10 ^ 6 + 10 ^ -12 > (L1 - L2) ^ 2`, so the lower \
      comparison's `m = 324 - alpha` is negative and the `k = 0` arm's `m ≤ 0` holds. \
      Reachable on both branches, since with `a1 = 0` there is no second answer to compute."
    branch := "k_zero"
    center := ![12, 6, 37000001 / 1000000]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  { name := "short_arm/the_inner_edge_exactly"
    geometry := shortArm
    note := "The inner band edge hit exactly, with `rho` still not a rational square: \
      `(x, y, h) = (12, 6, 12)` is the rational sphere point `18 * (2/3, 1/3, 2/3)`, so \
      `rho + h ^ 2 = 180 + 144 = 324 = (L1 - L2) ^ 2` and the comparison's `m` is exactly \
      `0`. `m ≤ 0` includes its end, so the pose is reachable - a strict `<` there would \
      report an arm that folds the second link back exactly onto the first as out of reach. \
      With `a1 = 0` the edge equation has no `r` in it, so nothing forces `rho` to be a \
      square here as it does on the `shipped` edges."
    branch := "k_zero"
    center := ![12, 6, 37]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  { name := "short_arm/outside_the_inner_edge_by_a_hair"
    geometry := shortArm
    note := "The inner dead zone, a millionth inside it: `alpha = 324 - 24 / 10 ^ 6 + \
      10 ^ -12 < (L1 - L2) ^ 2`, so `m = 324 - alpha > 0` and the `k = 0` arm's `m ≤ 0` \
      returns false. Both branches are dropped and the count is 0. With the two cases above \
      it pins the inner edge as a boundary of the band rather than as an artefact of where \
      the link lengths happen to fall."
    branch := "k_zero"
    center := ![12, 6, 36999999 / 1000000]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨false, false⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 0 } },
  { name := "short_arm/inside_the_outer_edge_by_a_hair"
    geometry := shortArm
    note := "The outer band edge from inside, by a millionth: `rho = 980` and `q ^ 2 + h ^ 2 = \
      980 + (28 - 10 ^ -6) ^ 2 = 1764 - 56 / 10 ^ 6 + 10 ^ -12 < (L1 + L2) ^ 2`, so the upper \
      comparison's `m = alpha - 1764` is negative and the `k = 0` arm's `m ≤ 0` holds."
    branch := "k_zero"
    center := ![28, 14, 52999999 / 1000000]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  { name := "short_arm/the_outer_edge_exactly"
    geometry := shortArm
    note := "The outer band edge hit exactly: `(x, y, h) = (28, 14, 28)` is `42 * (2/3, 1/3, \
      2/3)`, so `rho = 980` and `q ^ 2 + h ^ 2 = 980 + 784 = 1764 = (L1 + L2) ^ 2` with the \
      upper comparison's `m` exactly `0`. Reachable - the same fact as the `shipped` upper \
      edge with `a1 = 0`, so no rational radius is needed for the edge to be hit."
    branch := "k_zero"
    center := ![28, 14, 53]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 8 } },
  { name := "short_arm/outside_the_outer_edge_by_a_hair"
    geometry := shortArm
    note := "Past the outer edge by a millionth: `q ^ 2 + h ^ 2 = 1764 + 56 / 10 ^ 6 + \
      10 ^ -12`, the upper comparison's `m > 0` fails `m ≤ 0`, and both branches are dropped. \
      The three `short_arm` edge cases at heights one millionth apart pin the outer edge of \
      this arm the way the three `shipped` ones pin its own."
    branch := "k_zero"
    center := ![28, 14, 53000001 / 1000000]
    relativeRotation := genericWristRotation
    zyz := some (⟨4 / 5, 3 / 5⟩, ⟨5 / 13, 12 / 13⟩, ⟨15 / 17, 8 / 17⟩)
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨false, false⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := false
        candidateCount := 0 } },
  { name := "short_arm/well_inside_the_band"
    geometry := shortArm
    note := "Well inside, with a square radius and neither link at an extreme: `rho = 900 = \
      30 ^ 2`, `h = 15` and `alpha = 1125`, between `324` and `1764` with room to spare. The \
      arm reaches the same band from both shoulder branches, which is what `a1 = 0` means."
    branch := "k_zero"
    center := ![30, 0, 40]
    relativeRotation := quarterTurnRotation
    zyz := some (⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩)
    radius := some 30
    expected :=
      { radiusIsZero := false
        elbowBranches := ⟨true, true⟩
        wristCenterOnBaseAxis := false
        foldBack := ⟨false, false⟩
        wristSingular := true
        candidateCount := 8 } }]

/-! ## Reading a case back

The four comparisons a target makes, the arm of `leOfRadical` each one enters, and the two
routes that re-decide the band and the fold-back for a case that states its radius. -/

/-- The `(m, k)` pairs `planExact` hands to `leOfRadical`, for the target's own `rho`: the
lower-edge and upper-edge comparison of `σ = +1`, then the same two for `σ = -1`, in that
order. `leOfRadical` decides `m ≤ k * sqrt rho`, so a pair is the whole of the input a
comparison sees. -/
def radicalInputs (t : Target) : List (ℚ × ℚ) :=
  let alpha := t.radiusSq + t.a1 * t.a1 + t.height * t.height
  let lower := (t.linkOne - t.linkTwo) * (t.linkOne - t.linkTwo)
  let upper := (t.linkOne + t.linkTwo) * (t.linkOne + t.linkTwo)
  ([1, -1] : List ℤ).flatMap fun sigma =>
    let beta := branchBeta t.a1 sigma
    [(lower - alpha, beta), (alpha - upper, -beta)]

/-- The names of `leOfRadical`'s five arms, one per way the decision can be reached. A case
declares one of these and the generator checks that one of its four comparisons enters it. -/
def branchTags : List String :=
  ["k_zero", "m_nonpos_k_pos", "m_nonpos_k_neg", "m_pos_k_pos", "m_pos_k_neg"]

/-- Which arm of `leOfRadical` a comparison `m ≤ k * sqrt rho` enters, as the tag `branchTags`
names it. The two `m ≤ 0` arms and the two `m > 0` ones are the sign care: a comparison whose
sides are not both known to be non-negative is not decided by squaring it as it stands. -/
def radicalBranch (m k : ℚ) : String :=
  if k = 0 then "k_zero"
  else if decide (m ≤ 0) then
    if decide (0 < k) then "m_nonpos_k_pos" else "m_nonpos_k_neg"
  else if decide (0 < k) then "m_pos_k_pos"
  else "m_pos_k_neg"

/-- A Boolean as the JSON's spelling of it, for the failure messages. -/
def boolStr (b : Bool) : String := if b then "true" else "false"

/-- Render a rational exactly: `3` for integers, `-3/5` otherwise. `ℚ` is normalised with a
positive denominator, so this form is unambiguous. -/
def ratStr (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

/-! ## Checks

Every case is checked before anything is written, and the generator refuses to write a file if
any check fails. The checks are the ones `KinematicsTestData.lean` makes - the case's own
literals, and the invariants the case's claims about itself imply - plus the two second routes
to the band and the fold-back, which are what make a case cross-checked rather than merely
self-consistent. -/

/-- Every disagreement between a case and what the decision layer computes for it, and every
claim the case makes about itself that does not hold. A non-empty result means the case is not
usable as ground truth. -/
def caseFailures (c : Case) : List String :=
  let t := c.geometry.targetAt c.center
  let p := planExact t
  let expected := c.expected
  let field (what : String) (computed wanted : Bool) : List String :=
    if computed == wanted then []
      else [s!"{what} computes to {boolStr computed}, but the case's literal says {boolStr wanted}"]
  -- The case's geometry has to be one the document lists, dimension for dimension: a case that
  -- hand-copied a geometry would be checking a link-length set nothing else checks.
  let namedGeometry (ng : NamedGeometry) : Bool :=
    ng.name == c.geometry.name && decide (ng.a1 = c.geometry.a1)
      && decide (ng.d1 = c.geometry.d1) && decide (ng.linkOne = c.geometry.linkOne)
      && decide (ng.linkTwo = c.geometry.linkTwo)
  let observed := (radicalInputs t).map (fun (m, k) => radicalBranch m k)
  (if geometries.any namedGeometry then []
      else [s!"geometry '{c.geometry.name}' is not one of the document's"])
    ++ (if p.radiusIsZero.neg == p.radiusIsZero.pos then []
        else ["the two shoulder slots disagree on radius_is_zero, which `shoulderAngle` tests \
          once for both branches"])
    ++ field "radius_is_zero" p.radiusIsZero.pos expected.radiusIsZero
    ++ field "elbow_branches for σ = +1" p.elbowBranches.pos expected.elbowBranches.pos
    ++ field "elbow_branches for σ = -1" p.elbowBranches.neg expected.elbowBranches.neg
    ++ field "wrist_center_on_base_axis" p.wristCenterOnBaseAxis expected.wristCenterOnBaseAxis
    ++ field "fold_back for σ = +1" p.foldBack.pos expected.foldBack.pos
    ++ field "fold_back for σ = -1" p.foldBack.neg expected.foldBack.neg
    ++ field "wrist_singular" (wristPlanExact c.relativeRotation) expected.wristSingular
    ++ (if candidateCount p == expected.candidateCount then []
        else [s!"candidate_count computes to {candidateCount p}, but the case's literal says \
          {expected.candidateCount}"])
    -- `radius_is_zero` and `wrist_center_on_base_axis` are one predicate here, so a case whose
    -- two literals disagree is a case whose expectation is inconsistent with itself.
    ++ (if expected.radiusIsZero == expected.wristCenterOnBaseAxis then []
        else ["the case's literals give radius_is_zero and wrist_center_on_base_axis different \
          values, but they are the same predicate"])
    -- The declared `leOfRadical` arm: a tag no comparison of this target enters is a mistake
    -- in the case, not a fact about it.
    ++ (if branchTags.contains c.branch then []
        else [s!"'{c.branch}' is not one of leOfRadical's five arms"])
    ++ (if observed.contains c.branch then []
        else [s!"no comparison of this target enters '{c.branch}'; it enters {observed}"])
    -- A stated radius obliges the case to be the non-negative root of `rho`, and on that the
    -- band and the fold-back are re-decided the other way round.
    ++ (match c.radius with
      | none => []
      | some r =>
        (if decide (r * r = t.radiusSq) && decide (0 ≤ r) then []
            else [s!"the stated radius {ratStr r} is not the non-negative square root of rho \
              = {ratStr t.radiusSq}"])
          ++ ([1, -1].flatMap fun sigma =>
            let kept := if sigma = 1 then p.elbowBranches.pos else p.elbowBranches.neg
            let folds := if sigma = 1 then p.foldBack.pos else p.foldBack.neg
            (if reachableViaCosine t r sigma == kept then []
                else [s!"σ = {sigma}: the band through elbowCosine says \
                  {boolStr (reachableViaCosine t r sigma)} where the radical route says \
                  {boolStr kept}"])
              ++ (if foldsBackViaPlanar t r sigma == folds then []
                  else [s!"σ = {sigma}: the fold-back through q = σ * r - a1 says \
                    {boolStr (foldsBackViaPlanar t r sigma)} where the radical route says \
                    {boolStr folds}"])))
    -- A stated ZYZ product obliges the case to have the rotation it claims.
    ++ (match c.zyz with
      | none => []
      | some (θ4, θ5, θ6) =>
        if decide (wristRotation θ4 θ5 θ6 = c.relativeRotation) then []
          else ["the relative rotation is not the ZYZ product the case states"])

/-- The document-level invariants: a geometry no case uses would be a link-length set nothing
checks, an arm of `leOfRadical` no case is named for would be a branch nothing exercises, and a
wrist decision no case ever reaches would not be a decision. -/
def documentFailures : List String :=
  (geometries.filter fun ng =>
      !cases.any fun c => c.geometry.name == ng.name).map (fun ng =>
        s!"geometry '{ng.name}' is not used by any case")
    ++ (branchTags.filter fun tag =>
      !cases.any fun c => c.branch == tag).map (fun tag =>
        s!"no case is named for leOfRadical's '{tag}' arm")
    ++ (geometries.filter fun ng =>
        !cases.any fun c => c.geometry.name == ng.name
          && decide ((c.geometry.targetAt c.center).radiusSq = 0)).map (fun ng =>
      s!"no case for geometry '{ng.name}' puts the wrist centre on the base rotation axis")
    ++ (if cases.any fun c => (planExact (c.geometry.targetAt c.center)).foldBack.pos then []
        else ["no case witnesses the fold-back"])
    ++ (if cases.any fun c => wristPlanExact c.relativeRotation then []
        else ["no case is at the wrist singularity"])
    ++ (if cases.any fun c => !wristPlanExact c.relativeRotation then []
        else ["every case is at the wrist singularity"])
    ++ (if cases.any fun c => c.radius.isSome then []
        else ["no case states a rational radius, so the band is never re-derived the other way"])
    ++ (if cases.any fun c => c.radius.isNone then []
        else ["every case states a rational radius, so the extension is never entered with a \
          radical that has no rational root"])
    ++ (if cases.any fun c => c.zyz.isNone then []
        else ["every case states a ZYZ product, so no case witnesses the singularity test as a \
          conjunction"])
    ++ (if cases.length ≥ 20 then []
        else [s!"the corpus has {cases.length} entries; it is meant to carry every case the \
          decision layer is named for, and 20 is the floor"])
    ++ (if (cases.map fun c => c.name).eraseDups.length == cases.length then []
        else ["two cases share a name"])

/-! ## Serialization -/

def ratJson (q : ℚ) : Json := .str (ratStr q)

def vecJson (v : Vec) : Json := .arr #[ratJson (v 0), ratJson (v 1), ratJson (v 2)]

def matJson (M : Mat) : Json :=
  .arr #[.arr #[ratJson (M 0 0), ratJson (M 0 1), ratJson (M 0 2)],
    .arr #[ratJson (M 1 0), ratJson (M 1 1), ratJson (M 1 2)],
    .arr #[ratJson (M 2 0), ratJson (M 2 1), ratJson (M 2 2)]]

/-- The two elbow labels of one shoulder branch, kept or not: all-or-nothing, so both entries
are the same, and the shape is there because the Rust plan carries the labels separately. -/
def elbowJson (kept : Bool) : Json := .arr #[.bool kept, .bool kept]

def geometryJson (ng : NamedGeometry) : Json :=
  .mkObj [
    ("name", .str ng.name),
    ("a1", ratJson ng.a1),
    ("d1", ratJson ng.d1),
    ("link_one", ratJson ng.linkOne),
    ("link_two", ratJson ng.linkTwo),
    ("note", .str ng.note)]

/-- The plan Lean computed for a case - not the case's literals, which have been checked
against it by now: what the consumer compares with `==` has to be the computation. -/
def expectedJson (c : Case) : Json :=
  let t := c.geometry.targetAt c.center
  let p := planExact t
  .mkObj [
    ("radius_is_zero", .bool p.radiusIsZero.pos),
    ("elbow_branches", .arr #[elbowJson p.elbowBranches.pos, elbowJson p.elbowBranches.neg]),
    ("wrist_center_on_base_axis", .bool p.wristCenterOnBaseAxis),
    ("fold_back", .arr #[.bool p.foldBack.pos, .bool p.foldBack.neg]),
    ("wrist_singular", .bool (wristPlanExact c.relativeRotation)),
    ("candidate_count", Json.num (candidateCount p))]

def entryJson (c : Case) : Json :=
  let radiusJson : Json := match c.radius with
    | some r => ratJson r
    | none => .null
  .mkObj [
    ("name", .str c.name),
    ("geometry", .str c.geometry.name),
    ("note", .str c.note),
    ("branch", .str c.branch),
    ("radius", radiusJson),
    ("center", vecJson c.center),
    ("relative_rotation", matJson c.relativeRotation),
    ("expected", expectedJson c)]

def document : Json := .mkObj [
  ("schema_version", (1 : Json)),
  ("source", .str "lean/BranchDecisionQ.lean, evaluated over the rationals (exact)"),
  ("conventions", .str "Each entry is a wrist centre `(x4, y4, z4)` and the relative rotation \
    `R_3^6` of a target pose, both exact rationals, and the branch plan \
    `InverseKinematics`'s predicates decide for them. `radius_is_zero` is \
    `shoulderRadius g T = 0`, the wrist centre on the base rotation axis, which is \
    `NonDegenerate`'s first clause negated; `wrist_center_on_base_axis` is the same predicate \
    as `Degeneracy` carries it, and a consumer should find the two equal. `elbow_branches` is \
    `elbowBranches g T σ` per shoulder branch, in generation order σ = +1 then -1, each the \
    pair of elbow labels [1, -1] with kept or not: the Lean test is one band membership, so \
    the pair is kept together or not at all. `fold_back` is `Degeneracy.fold_back` per \
    shoulder branch, `NonDegenerate`'s second clause negated. `wrist_singular` is \
    `wristIsSingular` for the entry's rotation, exact because `hypot (Q 0 2) (Q 1 2) = 0` \
    holds exactly when both entries vanish. `candidate_count` is two wrist labels for every \
    kept elbow branch, which is `length_solutions_le_eight`'s bound computed. The band test \
    behind `elbow_branches` is a comparison in the quadratic extension Q(sqrt rho), with \
    `rho = x4^2 + y4^2`: the generator isolates the radical and squares with sign care, so no \
    square root is ever evaluated and every value here is exact. `branch` names which of the \
    five arms a case is written for (`k_zero`; `m_nonpos_k_pos`; `m_nonpos_k_neg`, the one \
    that squares only after negating; `m_pos_k_pos`; `m_pos_k_neg`) and a case whose declared \
    arm none of its four comparisons enters is not written at all. `radius` is the \
    non-negative rational square root of `rho` when there is one and null otherwise: it is \
    what lets the generator re-derive the band the long way round, through `elbowCosine`, and \
    no consumer needs it. Geometry is named by the kinematic dimensions: `a1` is \
    `Geometry.a1`, `d1` is `Geometry.d1`, `link_one` is `linkOne` (the DH table's `a2`) and \
    `link_two` is `linkTwo` (`d4`); no case reads the tool offset, so these geometries do not \
    carry one. Two cases carry a matrix that is not a rotation - one entry of the third \
    column zero and the other not - because that is the only witness that \
    `wrist_plan_exact` is a conjunction, and `wristRotation`'s third column vanishes in both \
    entries at once; the rest are ZYZ products with rational cosine/sine pairs, which the \
    generator re-derives before writing. Every numeral is an exact integer or \"num/den\" \
    string, never a JSON number."),
  ("geometries", .arr (geometries.map geometryJson).toArray),
  ("entries", .arr (cases.map entryJson).toArray)]

end BranchDecisionQ

open BranchDecisionQ

/-- Entry point: check every case and the document-level invariants, then write the JSON. Takes
the output path as its only argument, defaulting to `../test_data/branch_plans.json` (relative
to `lean/`, which is where `lake exe` is run from). Exits non-zero without writing anything if
a case fails its checks. -/
def main (args : List String) : IO UInt32 := do
  let path := args.head?.getD "../test_data/branch_plans.json"
  let failures := (cases.filterMap fun c =>
      match caseFailures c with
      | [] => none
      | fs => some (c.name, fs))
    ++ (if documentFailures.isEmpty then [] else [("<document>", documentFailures)])
  unless failures.isEmpty do
    IO.eprintln "refusing to write test data: a case failed its checks"
    for (name, fs) in failures do
      for f in fs do
        IO.eprintln s!"  {name}: {f}"
    return 1
  if let some dir := (System.FilePath.mk path).parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path (Json.pretty document ++ "\n")
  IO.println s!"wrote {cases.length} entries over {geometries.length} geometries to {path}"
  return 0
