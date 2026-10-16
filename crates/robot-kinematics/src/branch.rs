//! The branch decision core: the predicates `InverseKinematics.lean` decides exactly, and
//! the float stand-ins `kinematics.py` decides instead.
//!
//! The solver's control flow is a dispatch over labels — which shoulder branches, which
//! elbow branches, which wrist branches, which candidate to build. What feeds that dispatch
//! is a handful of scalar comparisons, and those comparisons are the only place a tolerance
//! can enter. [`BranchPlan::exact`] makes them exactly, in the quadratic extension
//! described below; [`BranchPlan::of_pose`] makes them against the named thresholds in
//! [`Tolerances`], each of which cites the Lean predicate it stands in for.
//!
//! The split is deliberate. The dispatch is a finite function of the plan's fields, so it
//! can be model-checked (Kani, a later workstream). The comparisons cannot: their
//! correctness is the claim "this float test reproduces that real-number predicate", which
//! no model checker over bit patterns can establish. Keeping the two in one file but in
//! separate functions is what lets each be argued about on its own terms.
//!
//! Nothing here computes an angle, and nothing here calls a trigonometric function.
//! `hypot` appears for one reason: `hypot (x, y) = 0` is how `shoulderAngle`'s
//! `shoulderRadius g T = 0` is spelled once a square root is available, and
//! `RealAtan2.hypot` never returns a negative number, so the test is still a comparison
//! against zero.

use crate::chain::{PlanarTarget, elbow_cosine, planar_target, wrist_center};
use crate::geometry::Geometry;
use crate::mat3::Mat3;
use crate::pose::Pose;
use crate::scalar::{Field, Scalar};

/// The shoulder branches, in the order `solutions` generates them: `+1` then `-1`.
///
/// Lean writes the same list as the literal `([1, -1] : List ℤ)` the outer `flatMap` runs
/// over, so this constant *is* that list, not a description of it.
pub const SHOULDER_BRANCHES: [i8; 2] = [1, -1];

/// The elbow branches, in generation order. Lean's `elbowBranches g T σ` returns either
/// this list or the empty one; which of the two is the band test's answer.
pub const ELBOW_BRANCHES: [i8; 2] = [1, -1];

/// The wrist branches, in generation order.
///
/// Unlike the elbow list, this one is never filtered: `solutions` runs
/// `([1, -1] : List ℤ).map fun wb => ...` unconditionally, which is
/// `wristBranch_eq_one_or_neg_one` read as generation. The singularity does not remove a
/// label — it changes the *angles* that label produces ([`WristPlan`]).
pub const WRIST_BRANCHES: [i8; 2] = [1, -1];

/// The slot a branch label occupies in a plan's two-entry arrays. `+1` is slot 0 and `-1`
/// is slot 1, so a plan's arrays are in generation order and `for sigma in
/// SHOULDER_BRANCHES { plan.shoulder[shoulder_index(sigma)] }` walks the list the way
/// `solutions` does.
#[inline]
pub fn shoulder_index(sigma: i8) -> usize {
    if sigma == 1 { 0 } else { 1 }
}

/// The sign a branch label names, as the scalar the arithmetic multiplies by.
#[inline]
pub fn branch_sign<S: Field>(label: i8) -> S {
    if label == 1 { S::one() } else { -S::one() }
}

/// The thresholds `kinematics.py` compares against, each standing in for one exact Lean
/// predicate.
///
/// `Tolerances` is the whole of the float/integer gap this layer has to declare: every
/// comparison in [`BranchPlan::of_pose`] and [`WristPlan`] reads one of these four fields,
/// and no other float test in the crate is tolerance-bearing. The fields are `f64` rather
/// than generic because they are configuration, not arithmetic: a caller picks them once
/// and the solver converts them to its own scalar.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Tolerances {
    /// `kinematics.py`'s `base_radius > tolerance`.
    ///
    /// Stands in for `shoulderAngle`'s case split on `shoulderRadius g T = 0`: the exact
    /// predicate says the wrist centre lies on the base rotation axis, which leaves the
    /// arm plane's azimuth — and so `theta 1` — undetermined. Zero recovers Lean exactly,
    /// because `hypot` is never negative and so `r <= 0` is `r = 0`.
    pub base_radius: f64,
    /// `kinematics.py`'s `cosine < -1 - tolerance or cosine > 1 + tolerance`, and the
    /// clamp into `[-1, 1]` it is followed by.
    ///
    /// Stands in for `elbowBranches`' `elbowCosine g (planarTargetQ g T σ) (planarTargetH g T)
    /// ∈ Set.Icc (-1) 1`. Zero recovers Lean exactly, and the boundary counts as reachable
    /// at both ends, which is what `Set.Icc` means.
    pub reachability: f64,
    /// `kinematics.py`'s `sine_five <= 1e-6` — a threshold of its own, not the `tolerance`
    /// argument.
    ///
    /// Stands in for `wristIsSingular`'s `wristSine g T σ ε = 0`. Zero recovers Lean
    /// exactly, since `wristSine` is a `hypot`. This is the threshold with the sharpest
    /// consequence: crossing it makes `solve` offer the flat wrist candidate as well as the
    /// read-back one, which is the divergence `solutions` is defined by *not* having.
    pub wrist_singularity: f64,
    /// `kinematics.py`'s final `position_error <= tolerance and orientation_error <=
    /// tolerance`, which discards a candidate whose forward kinematics misses the target.
    ///
    /// This one stands in for **no** Lean predicate, and that is the point of it: over `ℝ`
    /// the filter has nothing to reject (`fk_of_mem_solutions`), so `solve` carries the
    /// hypothesis `kinematics.py` needs and `solutions` carries none.
    pub pose: f64,
}

impl Tolerances {
    /// `kinematics.py`'s defaults: `inverse_kinematics(tolerance=1e-7)` plus the `1e-6`
    /// the wrist singularity is decided with.
    pub const fn python() -> Self {
        Self {
            base_radius: 1e-7,
            reachability: 1e-7,
            wrist_singularity: 1e-6,
            pose: 1e-7,
        }
    }

    /// All four zero, which is the exact predicate in every case: `r <= 0` is `r = 0` for a
    /// `hypot`, `-1 <= c <= 1` is `c ∈ Set.Icc (-1) 1`, and `sine <= 0` is `sine = 0`.
    /// [`crate::ik::solutions`] runs on this value and nothing else, which is what makes it
    /// the Lean function rather than the Python one.
    pub const fn exact() -> Self {
        Self {
            base_radius: 0.0,
            reachability: 0.0,
            wrist_singularity: 0.0,
            pose: 0.0,
        }
    }

    /// One threshold for every comparison. Useful for a test that wants to widen all of
    /// them together; production names the four separately.
    pub const fn all(tolerance: f64) -> Self {
        Self {
            base_radius: tolerance,
            reachability: tolerance,
            wrist_singularity: tolerance,
            pose: tolerance,
        }
    }
}

impl Default for Tolerances {
    fn default() -> Self {
        Self::python()
    }
}

/// Which elbow branches `elbowBranches g T σ` returns for one shoulder branch.
///
/// A set of labels rather than a pair of booleans, because the two are correlated: the band
/// test keeps `[1, -1]` together or keeps neither, so `+1`-only and `-1`-only are not
/// values the solver can produce. Constructing this from separate flags would allow them,
/// which is exactly the kind of state the dispatch should not have to defend against.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct ElbowBranches {
    /// Bit 0 is `+1`, bit 1 is `-1`.
    kept: u8,
}

impl ElbowBranches {
    /// The band test's rejection: `elbowBranches g T σ = []`.
    pub const NONE: Self = Self { kept: 0 };
    /// The band test's acceptance: `elbowBranches g T σ = [1, -1]`.
    pub const BOTH: Self = Self { kept: 0b11 };

    /// The set of the given labels, in generation order.
    pub fn of_labels(labels: &[i8]) -> Self {
        let mut kept = 0;
        for &label in labels {
            if label == 1 {
                kept |= 0b01;
            } else if label == -1 {
                kept |= 0b10;
            }
        }
        Self { kept }
    }

    /// Whether this shoulder branch generates the given elbow label.
    #[inline]
    pub fn keeps(self, epsilon: i8) -> bool {
        let bit = if epsilon == 1 {
            0b01
        } else if epsilon == -1 {
            0b10
        } else {
            return false;
        };
        self.kept & bit != 0
    }

    /// How many branches the band kept: 2 or 0.
    #[inline]
    pub fn count(self) -> usize {
        self.kept.count_ones() as usize
    }

    /// Whether the reachability band rejected this shoulder branch entirely.
    #[inline]
    pub fn is_empty(self) -> bool {
        self.kept == 0
    }

    /// The labels as a length-prefixed array, in generation order. A slice would need the
    /// data to live somewhere; this crate allocates nothing.
    #[inline]
    pub fn labels(self) -> ([i8; 2], usize) {
        let mut labels = [1i8, -1];
        let mut length = 0;
        for label in ELBOW_BRANCHES {
            if self.keeps(label) {
                labels[length] = label;
                length += 1;
            }
        }
        (labels, length)
    }
}

/// The shoulder half of a plan: `shoulderAngle`'s case split, per branch.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct ShoulderPlan {
    /// `+1` or `-1`: the label, recorded so a plan's two entries identify themselves.
    pub sigma: i8,
    /// `shoulderRadius g T = 0` — the wrist centre on the base rotation axis.
    ///
    /// It is a *whole plan's* field rather than a per-branch one, because Lean's
    /// `shoulderAngle` tests the radius the same way on both branches; it is recorded per
    /// branch so that a reader does not have to know that.
    pub radius_is_zero: bool,
}

/// The wrist labels `solutions` generates for a surviving arm branch.
///
/// The field exists to make the dispatch total: the wrist family is the one place the
/// solver branches on *nothing*, and a `BranchPlan` whose wrist half were implicit would
/// leave the reader to infer that. [`WristPlan`] is the wrist decision that does exist, and
/// it is per elbow family because it needs the recovered `R_3^6`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct WristBranches {
    labels: [i8; 2],
}

impl WristBranches {
    /// Both labels, which is the only value `solutions` can generate.
    pub const fn both() -> Self {
        Self {
            labels: WRIST_BRANCHES,
        }
    }

    /// The labels, in generation order.
    #[inline]
    pub fn labels(self) -> [i8; 2] {
        self.labels
    }

    /// Whether the given label is generated. Always true for `+1` and `-1`.
    #[inline]
    pub fn keeps(self, wrist: i8) -> bool {
        wrist == 1 || wrist == -1
    }
}

impl Default for WristBranches {
    fn default() -> Self {
        Self::both()
    }
}

/// Which of `NonDegenerate`'s clauses a target pose fails.
///
/// Reported, never branched on: `solutions` tests none of these, because the solver has a
/// candidate for every pose the arm reaches, degenerate ones included (`solutions_ne_nil`).
/// The classification is what tells a *caller* that the angles it got back are not
/// recoverable from the pose, and it is what the completeness and soundness suites read to
/// label their adversarial cases.
///
/// The third clause, `Real.sin (theta 4) ≠ 0`, is stated on a configuration and becomes a
/// statement about a pose only once the arm half has been solved — the wrist sine is read
/// off `R_3^6`, which needs `theta 1` to `theta 3` first. It is therefore [`WristPlan`],
/// decided per elbow family, and not a field here.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub struct Degeneracy {
    /// `NonDegenerate`'s first clause, negated: `g.a1 + planarQ g θ = 0` at a
    /// configuration, which `shoulderRadius_fk` turns into `shoulderRadius g (fk g θ) = 0`
    /// at its pose. The wrist centre sits on the base axis and the plane's azimuth is free.
    pub wrist_center_on_base_axis: bool,
    /// The second clause, negated: `linkOne = linkTwo` with the wrist centre back on the
    /// frame-1 origin, so the arm plane folds double and `theta 2` is free.
    ///
    /// Indexed by shoulder slot, because the frame-1 origin is where the *branch's* planar
    /// target vanishes — `sigma * r = a1` in polar form, `planarQAt g θ₂ ψ = planarHAt g θ₂ ψ = 0`
    /// in the configuration's own terms. `linkOne_eq_linkTwo_of_planar_eq_zero` is why the
    /// link equality in the clause is redundant once the planar target vanishes; it is
    /// still tested here, because the pose-level target can vanish on a branch the
    /// configuration does not sit on.
    pub fold_back: [bool; 2],
}

/// Everything `solutions` branches on for one target pose, before any angle is computed.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct BranchPlan {
    /// `shoulderAngle`'s anchor and the reachability band, per shoulder branch, in
    /// generation order.
    pub shoulder: [ShoulderPlan; 2],
    /// `elbowBranches g T σ`, per shoulder branch, in generation order.
    pub elbow_branches: [ElbowBranches; 2],
    /// The wrist family's labels.
    pub wrist: WristBranches,
    /// The pose's degeneracy classification. Not read by the solver; see [`Degeneracy`].
    pub degenerate: Degeneracy,
}

/// The wrist decision: `InverseKinematics.wristIsSingular`, `wristSine g T σ ε = 0`.
///
/// At the singularity joints 4 and 6 share an axis and only their sum is observable —
/// `Zyz.wristRotation_zero_middle` for `theta 5 = 0` and `Zyz.wristRotation_pi_middle` for
/// `theta 5 = π` — so the solver holds joint 4 at zero and reads joint 6 off the rotation
/// with the middle joint taken out. Off it, both wrist branches read the rotation directly.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct WristPlan {
    /// `wristSine g T σ ε = 0`.
    pub singular: bool,
}

/// The scalars the exact plan is decided from.
///
/// Every field is rational when the target pose is: the solver's only square root is the
/// radial one, and the exact plan carries it symbolically instead of evaluating it. That is
/// what makes the reachability band decidable at all — see [`BranchPlan::exact`].
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct ExactTarget<S> {
    /// `rho = x4² + y4²`, the square of `shoulderRadius g T`. Non-negative in any ordered
    /// field, which is the precondition the radical comparisons below rely on.
    pub radius_sq: S,
    /// The base offset `a1`.
    pub a1: S,
    /// `planarTargetH g T` — `z4 - d1`.
    pub height: S,
    /// The first link length.
    pub link_one: S,
    /// The second link length.
    pub link_two: S,
}

impl<S: Field> ExactTarget<S> {
    /// The exact target of a pose, from the components of its wrist centre.
    ///
    /// `rho = x4² + y4²` rather than `shoulderRadius g T ^ 2`: the two agree, but the
    /// square is what the exact arithmetic has and the square root is what it does not.
    pub fn of_center(
        a1: S,
        d1: S,
        link_one: S,
        link_two: S,
        center_x: S,
        center_y: S,
        center_z: S,
    ) -> Self {
        Self {
            radius_sq: center_x * center_x + center_y * center_y,
            a1,
            height: center_z - d1,
            link_one,
            link_two,
        }
    }
}

/// Whether `m <= k * sqrt rho`, decided without taking the square root.
///
/// This is the whole of the quadratic extension the reachability band needs. Isolate the
/// radical — `m <= k * sqrt rho` — then split on the sign of the radical's coefficient,
/// because squaring is only reversible where both sides are non-negative:
///
/// * `k = 0`: the radical is gone and the test is rational.
/// * `k < 0`: `k * sqrt rho <= 0`, so `m > 0` decides `false` outright and otherwise both
///   sides are non-positive and `m <= k * sqrt rho` is `m² >= k² rho` (negating both sides
///   of a non-positive inequality, then squaring).
/// * `k > 0`: `k * sqrt rho >= 0`, so `m <= 0` decides `true` outright and otherwise
///   `m <= k * sqrt rho` is `m² <= k² rho`.
///
/// Every operation is a field operation and a comparison, so this is exact whenever its
/// arguments are, and it is the reason `BranchDecisionQ.lean` can emit the reachability
/// decision as a rational computation rather than as a rational *approximation*.
pub fn le_of_radical<S: Field>(m: S, k: S, rho: S) -> bool {
    let zero = S::zero();
    if k == zero {
        return m <= zero;
    }
    if m <= zero {
        if k > zero { true } else { m * m >= k * k * rho }
    } else if k > zero {
        m * m <= k * k * rho
    } else {
        false
    }
}

/// Whether `alpha + beta * sqrt rho = 0`, decided without taking the square root.
///
/// Used for the fold-back clause, where the planar target `q_sigma² + h²` is the extension
/// value that has to vanish. Squaring `alpha = -beta sqrt rho` gives `alpha² = beta² rho`,
/// which is necessary but not sufficient: the sign has to match too, which is `alpha * beta <= 0`
/// because `sqrt rho` is non-negative. The `alpha = beta = 0` case satisfies both, which is
/// right — it is the zero of the extension however `rho` is chosen.
pub fn radical_eq_zero<S: Field>(alpha: S, beta: S, rho: S) -> bool {
    alpha * alpha == beta * beta * rho && alpha * beta <= S::zero()
}

impl BranchPlan {
    /// The exact plan: `shoulderAngle`'s `shoulderRadius g T = 0`, `elbowBranches`'
    /// `elbowCosine g .. ∈ Set.Icc (-1) 1` and the fold-back clause, decided in the
    /// quadratic extension `ℚ(√rho)` with no tolerance anywhere.
    ///
    /// **Why the extension is needed.** The band test is a test on
    /// `elbowCosine = (q² + h² - L1² - L2²) / (2 L1 L2)`, and with `q = sigma * r - a1`
    /// the quantity `q² + h²` expands to `rho - 2 sigma a1 r + a1² + h²`, where `rho` is
    /// rational but `r = sqrt rho` is not. Clearing the band's positive denominator and
    /// adding `L1² + L2²` makes it `(L1 - L2)² <= q² + h² <= (L1 + L2)²`, whose bounds are
    /// rational — so the whole decision is "compare `alpha + beta sqrt rho` against a
    /// rational bound", which [`le_of_radical`] decides exactly. The extension never has to
    /// be *represented*, only isolated.
    ///
    /// The two other clauses `NonDegenerate` names — `r = 0` and the fold-back — are
    /// rational on their own, and are decided as such here.
    pub fn exact<S: Field>(target: &ExactTarget<S>) -> Self {
        let zero = S::zero();
        let two = S::from_f64(2.0);
        let rho = target.radius_sq;
        let a1 = target.a1;
        let height = target.height;
        // `(L1 - L2)²` and `(L1 + L2)²`: `elbowCosine ∈ Set.Icc (-1) 1` with its positive
        // denominator cleared, which is `|L2 - L4| <= D <= L2 + L4` in `mathematics.md` §4.
        let lower = (target.link_one - target.link_two) * (target.link_one - target.link_two);
        let upper = (target.link_one + target.link_two) * (target.link_one + target.link_two);
        // `q_sigma² + h² = alpha + beta sqrt rho`, with `alpha` rational and `beta` the
        // radical's coefficient. `sigma² = 1` is what collapses `(sigma r)²` to `rho`.
        let alpha = rho + a1 * a1 + height * height;
        let radius_is_zero = rho == zero;
        let mut plan = Self {
            shoulder: [
                ShoulderPlan {
                    sigma: 1,
                    radius_is_zero,
                },
                ShoulderPlan {
                    sigma: -1,
                    radius_is_zero,
                },
            ],
            elbow_branches: [ElbowBranches::NONE; 2],
            wrist: WristBranches::both(),
            degenerate: Degeneracy {
                wrist_center_on_base_axis: radius_is_zero,
                fold_back: [false; 2],
            },
        };
        for sigma in SHOULDER_BRANCHES {
            let slot = shoulder_index(sigma);
            let beta = -(two * branch_sign::<S>(sigma) * a1);
            // `alpha + beta sqrt rho >= lower` is `lower - alpha <= beta sqrt rho`, and
            // `alpha + beta sqrt rho <= upper` is `alpha - upper <= -beta sqrt rho`.
            let reachable =
                le_of_radical(lower - alpha, beta, rho) && le_of_radical(alpha - upper, -beta, rho);
            plan.elbow_branches[slot] = if reachable {
                ElbowBranches::BOTH
            } else {
                ElbowBranches::NONE
            };
            // The fold-back clause: the branch's planar target vanishes, which is
            // `q_sigma = 0` together with `h = 0`, equivalently `q_sigma² + h² = 0`.
            plan.degenerate.fold_back[slot] = target.link_one == target.link_two
                && height == zero
                && radical_eq_zero(alpha, beta, rho);
        }
        plan
    }

    /// The float plan: the same three predicates, each comparison widened by its named
    /// tolerance.
    ///
    /// The unary predicates are cheap enough to be spelled out; the band test is not, and
    /// it reads [`crate::chain::elbow_cosine`] so that the value being compared is the same
    /// function `solutions` uses rather than a transcription of it.
    pub fn of_pose<S: Scalar>(g: &Geometry<S>, target: &Pose<S>, tolerances: &Tolerances) -> Self {
        let center = wrist_center(g, target);
        let radius = center.hypot_xy();
        // `shoulderAngle`'s anchor. Lean compares against exact zero; the tolerance is
        // `kinematics.py`'s, and zero recovers the exact test because `hypot` is never
        // negative.
        let radius_is_zero = radius <= S::from_f64(tolerances.base_radius);
        let height = center.z() - g.d1;
        let reach = S::from_f64(tolerances.reachability);
        let one = S::one();
        let mut plan = Self {
            shoulder: [
                ShoulderPlan {
                    sigma: 1,
                    radius_is_zero,
                },
                ShoulderPlan {
                    sigma: -1,
                    radius_is_zero,
                },
            ],
            elbow_branches: [ElbowBranches::NONE; 2],
            wrist: WristBranches::both(),
            degenerate: Degeneracy {
                wrist_center_on_base_axis: radius_is_zero,
                fold_back: [false; 2],
            },
        };
        for sigma in SHOULDER_BRANCHES {
            let slot = shoulder_index(sigma);
            let planar: PlanarTarget<S> = planar_target(g, center, branch_sign::<S>(sigma));
            // `elbowBranches`' band test. The `hypot` route `chain::planar_target` takes is
            // the floating-point one: over `ℝ` the same quantity is `alpha + beta sqrt rho`.
            let cosine = elbow_cosine(g, &planar);
            plan.elbow_branches[slot] = if cosine >= -(one + reach) && cosine <= one + reach {
                ElbowBranches::BOTH
            } else {
                ElbowBranches::NONE
            };
            // The fold-back is *reported*, never branched on, and `kinematics.py` has no
            // tolerance for it — so it is tested exactly. A wrist centre one ulp off the
            // frame-1 origin is not the fold-back, and widening this would report a
            // degeneracy `NonDegenerate` does not exclude.
            plan.degenerate.fold_back[slot] =
                g.link_one == g.link_two && planar.q == S::zero() && height == S::zero();
        }
        plan
    }
}

/// `InverseKinematics.wristIsSingular` at a recovered `R_3^6`: whether the wrist sits at
/// the singularity, where joints 4 and 6 share an axis.
///
/// The parameter is the relative rotation, not `wristSine`, so that the caller cannot pass
/// a differently-computed sine: `wristSine` is `hypot (Q 0 2) (Q 1 2)` by definition
/// (`Zyz.wristRotation_hypot_third_column` reads it off the rotation as `|sin theta 5|`),
/// and computing it anywhere else would be a second definition to keep in step.
pub fn wrist_plan<S: Scalar>(relative_rotation: &Mat3<S>, tolerances: &Tolerances) -> WristPlan {
    let sine = relative_rotation.at(0, 2).hypot(relative_rotation.at(1, 2));
    WristPlan {
        singular: sine <= S::from_f64(tolerances.wrist_singularity),
    }
}

/// The exact wrist decision, for scalars that have no square root at all.
///
/// `hypot x y = 0` holds exactly when `x = 0 ∧ y = 0` — that is the identity that makes
/// `wristSine = 0` a rational predicate, as `docs/verification.md` notes — so this is the
/// same test [`wrist_plan`] makes with a zero tolerance, spelled in the field rather than
/// through `Scalar::hypot`. It is what lets `BranchDecisionQ.lean` emit the wrist decision
/// for a rational rotation and have it compared with `==`, which is the half of the plan the
/// float route could not check exactly.
pub fn wrist_plan_exact<S: Field>(relative_rotation: &Mat3<S>) -> WristPlan {
    let zero = S::zero();
    WristPlan {
        singular: relative_rotation.at(0, 2) == zero && relative_rotation.at(1, 2) == zero,
    }
}

/// How many candidates a plan generates, before any is discarded: `sum over the shoulder
/// branches of (kept elbow branches) * 2`. This is `length_solutions_le_eight`'s bound
/// computed rather than asserted, and a plan with an empty elbow family contributes nothing
/// — which is where a pose no branch reaches turns into an empty candidate list.
pub fn candidate_count(plan: &BranchPlan) -> usize {
    let mut total = 0;
    for slot in 0..2 {
        total += plan.elbow_branches[slot].count() * WRIST_BRANCHES.len();
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shipped() -> Geometry<f64> {
        Geometry::shipped()
    }

    /// A pose whose wrist centre is at `(x, y, z)`, with an identity rotation. The plans
    /// below read only the centre, so the rotation is free.
    fn pose_with_center(x: f64, y: f64, z: f64) -> Pose<f64> {
        Pose::new(Mat3::identity(), crate::vec3::Vec3::new(x, y, z))
    }

    /// The wrist centre of `pose_with_center` is that point plus `d6` along the identity
    /// rotation's z axis, so a caller asking for a centre at `(x, y, z)` has to place the
    /// end effector at `(x, y, z + d6)`.
    fn pose_at_center(x: f64, y: f64, z: f64) -> Pose<f64> {
        pose_with_center(x, y, z + shipped().tool_offset)
    }

    #[test]
    fn the_fold_back_is_the_branch_whose_planar_target_vanishes() {
        // `a1 = 10` with the wrist centre at `(10, 0, 32)`: `q_+1 = r - a1 = 0` and
        // `h = 0`, so the `+1` branch's planar target is the frame-1 origin — the fold-back
        // clause — while the `-1` branch's is not, on the same pose. Equal links are the
        // clause's other half, so this is also the case that pins the indexing.
        let target = ExactTarget::of_center(10.0, 32.0, 25.0, 25.0, 10.0, 0.0, 32.0);
        let plan = BranchPlan::exact(&target);
        assert_eq!(plan.elbow_branches[0], ElbowBranches::BOTH);
        assert_eq!(plan.degenerate.fold_back, [true, false]);
    }

    #[test]
    fn the_reachability_band_includes_its_ends() {
        // `Set.Icc (-1) 1` includes the boundary, which is `d = L1 + L2` here: the arm is
        // straight out. `q_+1 = 0`, so `h = 50` puts the distance exactly on the bound.
        let target = ExactTarget::of_center(10.0, 32.0, 25.0, 25.0, 10.0, 0.0, 32.0 + 50.0);
        let plan = BranchPlan::exact(&target);
        assert_eq!(plan.elbow_branches[0], ElbowBranches::BOTH);
        // A hair further out is the far side of the bound.
        let target = ExactTarget::of_center(10.0, 32.0, 25.0, 25.0, 10.0, 0.0, 32.0 + 50.0000001);
        let plan = BranchPlan::exact(&target);
        assert_eq!(plan.elbow_branches[0], ElbowBranches::NONE);
    }

    #[test]
    fn a_target_beyond_the_reach_is_rejected_on_both_shoulder_branches() {
        // `h` alone takes the distance past `L1 + L2 = 50`.
        let target = ExactTarget::of_center(10.0, 32.0, 25.0, 25.0, 0.0, 0.0, 32.0 + 100.0);
        let plan = BranchPlan::exact(&target);
        assert_eq!(plan.elbow_branches[0], ElbowBranches::NONE);
        assert_eq!(plan.elbow_branches[1], ElbowBranches::NONE);
        assert_eq!(candidate_count(&plan), 0);
    }

    #[test]
    fn the_fold_back_needs_the_equal_links() {
        // `q = 0` and `h = 0` with unequal links: reachable, but not the fold-back, because
        // the second link cannot reach back to the frame-1 origin.
        let target = ExactTarget::of_center(0.0, 40.0, 40.0, 30.0, 0.0, 0.0, 40.0);
        let plan = BranchPlan::exact(&target);
        assert!(!plan.degenerate.fold_back[0]);
        assert!(!plan.degenerate.fold_back[1]);
    }

    #[test]
    fn le_of_radical_agrees_with_an_exact_square_root() {
        // `rho` a perfect square, so `sqrt rho` is exact in `f64` and the direct comparison
        // is a legitimate oracle for the squaring.
        for rho in [0.0, 1.0, 4.0, 9.0] {
            for k in [-3.0, -1.0, 0.0, 1.0, 2.0] {
                for m in [-5.0, -1.0, 0.0, 1.0, 5.0] {
                    assert_eq!(
                        le_of_radical(m, k, rho),
                        m <= k * rho.sqrt(),
                        "m = {m}, k = {k}, rho = {rho}"
                    );
                }
            }
        }
    }

    #[test]
    fn radical_eq_zero_matches_the_extension() {
        for rho in [0.0, 1.0, 4.0] {
            for beta in [-2.0, 0.0, 3.0] {
                for alpha in [-4.0, 0.0, 4.0] {
                    assert_eq!(
                        radical_eq_zero(alpha, beta, rho),
                        alpha + beta * rho.sqrt() == 0.0,
                        "alpha = {alpha}, beta = {beta}, rho = {rho}"
                    );
                }
            }
        }
    }

    #[test]
    fn the_wrist_centre_on_the_base_axis_is_the_first_clause() {
        // `rho = 0` on both branches; the anchor case `shoulderAngle` names.
        let target = ExactTarget::of_center(10.0, 32.0, 25.0, 25.0, 0.0, 0.0, 32.0);
        let plan = BranchPlan::exact(&target);
        assert!(plan.shoulder[0].radius_is_zero);
        assert!(plan.degenerate.wrist_center_on_base_axis);
        // With `a1 = 10` neither branch's planar target can vanish at `rho = 0`, so this is
        // not the fold-back.
        assert!(!plan.degenerate.fold_back[0]);
        assert!(!plan.degenerate.fold_back[1]);
    }

    #[test]
    fn the_exact_and_float_plans_agree_on_the_shipped_arm() {
        // Grid of wrist centres, both paths. A disagreement here is a bug in one of the
        // two, since `f64` represents these values exactly and the arithmetic on them is
        // exact too (small integers, and `hypot` of exact squares of integers stays exact
        // for these magnitudes).
        let g = shipped();
        for x in [-100.0, -50.0, -10.0, 0.0, 10.0, 30.0, 50.0, 100.0] {
            for z in [-20.0, 0.0, 32.0, 57.0, 82.0] {
                let pose = pose_at_center(x, 0.0, z);
                let center = wrist_center(&g, &pose);
                let exact = BranchPlan::exact(&ExactTarget::of_center(
                    g.a1,
                    g.d1,
                    g.link_one,
                    g.link_two,
                    center.x(),
                    center.y(),
                    center.z(),
                ));
                let float = BranchPlan::of_pose(&g, &pose, &Tolerances::exact());
                assert_eq!(exact, float, "wrist centre ({x}, 0, {z})");
            }
        }
    }

    #[test]
    fn the_float_plan_widens_the_band_by_the_named_tolerance() {
        // A target just outside the band: rejected exactly, kept by `kinematics.py`'s
        // `1e-7`. The two plans differing *is* the divergence, so the test asserts both.
        let g = shipped();
        // `q = 0`, so the distance is `|h|`; `L1 + L2 = 50`. Place the centre one ulp past
        // the band.
        let h = 50.0 + 1e-9;
        let pose = pose_at_center(10.0, 0.0, g.d1 + h);
        let exact = BranchPlan::of_pose(&g, &pose, &Tolerances::exact());
        let python = BranchPlan::of_pose(&g, &pose, &Tolerances::python());
        assert_eq!(exact.elbow_branches[0], ElbowBranches::NONE);
        assert_eq!(python.elbow_branches[0], ElbowBranches::BOTH);
    }

    #[test]
    fn the_elbow_family_is_all_or_nothing() {
        let both = ElbowBranches::BOTH;
        assert!(both.keeps(1) && both.keeps(-1));
        assert_eq!(both.count(), 2);
        assert_eq!(both.labels(), ([1, -1], 2));

        let none = ElbowBranches::NONE;
        assert!(!none.keeps(1) && !none.keeps(-1));
        assert!(none.is_empty());
        assert_eq!(none.labels().1, 0);

        assert_eq!(ElbowBranches::of_labels(&[1, -1]), ElbowBranches::BOTH);
        assert_eq!(ElbowBranches::of_labels(&[]), ElbowBranches::NONE);
        let forward = ElbowBranches::of_labels(&[1]);
        assert!(forward.keeps(1) && !forward.keeps(-1));
        assert_eq!(forward.labels(), ([1, -1], 1));
    }

    #[test]
    fn the_wrist_family_is_generated_unconditionally() {
        let wrist = WristBranches::both();
        assert_eq!(wrist.labels(), [1, -1]);
        assert!(wrist.keeps(1) && wrist.keeps(-1));
    }
}
