//! The ZYZ wrist reconstruction: the three angles the solver reads off the wrist's share
//! of a target rotation.
//!
//! The counterpart of `lean/Zyz.lean`, and the last step of the closed-form solver. The
//! solver divides the arm's rotation out of a target pose and is left holding `R_3^6`, the
//! rotation from frame 3 to frame 6; joints 4, 5 and 6 are that matrix's ZYZ
//! decomposition, so the solver has to turn the matrix back into them. The functions below
//! are that decomposition in both `atan2` branches ([`reconstruct`], [`reconstruct_mirror`])
//! and at the wrist singularity ([`reconstruct_flat`]), together with the reads
//! `InverseKinematics.lean` assembles its candidates out of and the read-off theorems that
//! say those reads invert the product.
//!
//! Angle triples here are in [`crate::chain::wrist_rotation`]'s own convention,
//! `rotZ θ4 · rotY (-θ5) · rotZ θ6` — the middle angle is negated *inside* that definition
//! — so what this module returns is the middle angle as the solver reports it, handed on
//! unchanged. The two branches are `(a, θ5, c)` and `(a + π, -θ5, c + π)`:
//! `Zyz.wristRotation_mirror` is the theorem that they are the *same* rotation, which is
//! what removes the sign case split from the reconstruction.
//!
//! Every reconstruction statement carries the non-degeneracy `(Q 0 2, Q 1 2) ≠ (0, 0)`,
//! i.e. `sin θ5 ≠ 0`: the third column not vertical, which is exactly the regime in which
//! joints 4, 5 and 6 are separately observable. What the product still says once the column
//! *is* vertical is [`reconstruct_flat`]'s subject.

use crate::mat3::Mat3;
use crate::scalar::Scalar;

/// The three wrist angles the ZYZ decomposition of a rotation `Q` recovers, as the
/// solver's joints 4, 5 and 6 (0-based `angles[3..6]`, `mathematics.md`'s theta4..6).
///
/// The triple is in `wristRotation`'s convention, so handing it straight to
/// [`crate::chain::wrist_rotation`] returns the rotation it was read off — that is what
/// each of the three reconstruction theorems states, and the only sense in which these
/// angles are "the" answer.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct WristAngles<S> {
    /// The first of the wrist's three angles, `InverseKinematics.wristTheta4`.
    pub theta4: S,
    /// The middle one, `InverseKinematics.wristTheta5`.
    pub theta5: S,
    /// The last, `InverseKinematics.wristTheta6`.
    pub theta6: S,
}

/// `InverseKinematics.wristReadTheta4`: the direction of joint 4, `atan2 (Q 1 2) (Q 0 2)`.
///
/// The pair is the third column's `(x, y)` part, which at a wrist product is `-sin θ5`
/// times the unit-circle point of `θ4`; the read is therefore `θ4` up to the half turn that
/// negative factor costs. `Zyz.wristRotation_read_theta4_coe_angle` is that read stated as
/// an angle: `θ4` itself, plus `π` exactly when `sin θ5` is positive.
#[inline]
pub fn read_theta4<S: Scalar>(q: &Mat3<S>) -> S {
    q.at(1, 2).atan2(q.at(0, 2))
}

/// `InverseKinematics.wristReadTheta6`: the direction of joint 6,
/// `atan2 (Q 2 1) (-(Q 2 0))`.
///
/// The pair is the third row's `(y, -x)` part. Negating `Q 2 0` is what puts the same
/// `-sin θ5` factor in front of `(sin θ6, cos θ6)` that [`read_theta4`] reads off
/// `(sin θ4, cos θ4)`, so the two reads carry the *same* half-turn offset — the reason one
/// branch label serves both joints.
#[inline]
pub fn read_theta6<S: Scalar>(q: &Mat3<S>) -> S {
    q.at(2, 1).atan2(-q.at(2, 0))
}

/// `InverseKinematics.wristReadTheta6Flat`: joint 6's direction at the wrist singularity,
/// read off the flattened product `rotY θ5 * Q` with `θ5 = atan2 0 (Q 2 2)`.
///
/// With the third column vertical the middle angle's sine is zero, so `rotY θ5` is the
/// diagonal `diag (cos θ5, 1, cos θ5)`; multiplying it in is what takes the middle factor
/// back out of the product, leaving the first column's top two entries a unit pair pointing
/// at `θ6`. `Zyz.wristRotation_reconstruct_flat` is that computation — its proof carries the
/// flattened matrix as `diag (r, 1, r) * rotZ θ6` — and the `atan2` here is the read it
/// licenses. The flattening angle is the *positive* `atan2 0 (Q 2 2)`, not signed by a
/// branch: at the singularity it is `0` or `π`, and `rotY` cannot tell `π` from `-π`, so
/// the two signs agree and `InverseKinematics.wristTheta6` takes the sign out to keep the
/// branching in `wristTheta5` alone.
#[inline]
pub fn read_theta6_flat<S: Scalar>(q: &Mat3<S>) -> S {
    let theta5 = S::zero().atan2(q.at(2, 2));
    let flattened = Mat3::rot_y(theta5) * *q;
    flattened.at(1, 0).atan2(flattened.at(0, 0))
}

/// `InverseKinematics.wristSine` at a rotation `Q`: `hypot (Q 0 2) (Q 1 2)`, the length of
/// the third column's `(x, y)` part.
///
/// `Zyz.wristRotation_hypot_third_column` evaluates it at a wrist product as `|sin θ5|`:
/// the two entries are a common factor times a unit-circle point, and a length cannot
/// remember the sign of that factor — only its absolute value. `hypot_third_column q = 0`
/// holds exactly when both entries vanish, which is `InverseKinematics.wristIsSingular`
/// and the negation of the `hne` hypothesis
/// [`wristRotation_reconstruct`](reconstruct) carries.
#[inline]
pub fn hypot_third_column<S: Scalar>(q: &Mat3<S>) -> S {
    q.at(0, 2).hypot(q.at(1, 2))
}

/// `InverseKinematics.wristCosine`: the `(2, 2)` entry of `R_3^6`, which is the cosine of
/// the middle angle — the third conjunct of `Kinematics.rotZ_mul_rotY_mul_rotZ_entries`
/// read at `(a, -θ5, c)`.
///
/// It needs no transcendental of its own, but it is stated alongside
/// [`hypot_third_column`] because it is always consumed with it: the two are the pair
/// `atan2` is taken of for the middle angle, in [`read_theta5`] and in the reconstruction.
#[inline]
pub fn cosine_third_entry<S: Scalar>(q: &Mat3<S>) -> S {
    q.at(2, 2)
}

/// `Zyz.wristRotation_read_theta5_coe_angle`'s shape: the signed middle angle
/// `branch * atan2 (hypot (Q 0 2) (Q 1 2)) (Q 2 2)`.
///
/// `hypot` is never negative, so the `atan2` alone is the middle angle's *magnitude* —
/// `InverseKinematics.wristTheta5`'s `atan2 (wristSine) (wristCosine)` — and `branch`
/// supplies the sign. The theorem says which label inverts the product: it is the sign of
/// the command's own `sin θ5`, and then the read is `θ5` itself, not merely `θ5` up to a
/// half turn. The solver passes `+1` or `-1`; the multiplication is Lean's own, so any
/// other integer scales the magnitude exactly as `wb * atan2 …` does over `ℝ`.
#[inline]
pub fn read_theta5<S: Scalar>(q: &Mat3<S>, branch: i8) -> S {
    S::from_f64(branch as f64) * hypot_third_column(q).atan2(cosine_third_entry(q))
}

/// `Zyz.wristRotation_reconstruct`: the direct branch, the three angles
/// `(atan2 (Q 1 2) (Q 0 2), -(atan2 (hypot (Q 0 2) (Q 1 2)) (Q 2 2)), atan2 (Q 2 1) (-(Q 2 0)))`.
///
/// Its angles satisfy `wristRotation θ4 θ5 θ6 = Q` for every `Q` that is a rotation —
/// `Qᵀ Q = 1` and `det Q = 1` are the theorem's hypotheses — whose third column is not
/// vertical. A matrix that is not a rotation is outside what this function claims: the
/// entries the reads do not mention are pinned down by the cofactor relations `det Q = 1`
/// gives, so "reading it back" is a property of rotations and not of 3x3 matrices, and the
/// `hne` hypothesis is the same boundary for the middle angle — it is
/// `hypot_third_column q ≠ 0`, and beyond it [`reconstruct_flat`] is the branch.
///
/// The middle angle is the negated `atan2` because `wristRotation` negates its middle
/// argument again; this is the solver's `-1` branch label, `read_theta5(q, -1)`, and the
/// other label's triple is [`reconstruct_mirror`].
#[inline]
pub fn reconstruct<S: Scalar>(q: &Mat3<S>) -> WristAngles<S> {
    WristAngles {
        theta4: read_theta4(q),
        // The theorem's `-(atan2 (hypot …) (Q 2 2))`: the magnitude read at the `-1` label.
        theta5: read_theta5(q, -1),
        theta6: read_theta6(q),
    }
}

/// `Zyz.wristRotation_reconstruct_mirror`: joints 4 and 6 turned by `pi`, the middle angle
/// the other way round, rebuilding the same `Q`.
///
/// `atan2`'s other branch for the two outer joints costs a half turn each, and the middle
/// angle that goes with it is [`reconstruct`]'s negated — `(a + π, -θ5, c + π)` against
/// `(a, θ5, c)`, which is `Zyz.wristRotation_mirror`'s own statement. Nothing new is
/// needed to rebuild `Q`: the mirrored triple *is* the direct one's rotation
/// (`Zyz.rotZ_pi_mul_rotY_mul_rotZ_pi` is the cancellation that makes it so), which is why
/// the solver can return both branches without a sign case split. This is the `+1` label,
/// `read_theta5(q, 1)`.
#[inline]
pub fn reconstruct_mirror<S: Scalar>(q: &Mat3<S>) -> WristAngles<S> {
    WristAngles {
        theta4: read_theta4(q) + S::pi(),
        theta5: read_theta5(q, 1),
        theta6: read_theta6(q) + S::pi(),
    }
}

/// `Zyz.wristRotation_reconstruct_flat`: the wrist-singularity branch, joint 4 held at zero
/// and joint 6 read off the flattened product, with `θ5 = atan2 0 (Q 2 2)`.
///
/// At the singularity the third column is vertical, joints 4 and 6 share an axis, and only
/// `θ4 + θ6` (or `θ4 - θ6`) is observable — `Zyz.wristRotation_zero_middle` at `θ5 = 0`
/// and `Zyz.wristRotation_pi_middle` at `θ5 = π`. The solver resolves that freedom by
/// pinning joint 4 at zero and handing the whole combination to joint 6, which is
/// `kinematics.py`'s `flattened` fallback; the theorem says the split reconstructs `Q`
/// exactly, for any rotation whose third column is vertical. The middle angle carries no
/// branch sign — see [`read_theta6_flat`] for why `rotY` cannot see one here.
#[inline]
pub fn reconstruct_flat<S: Scalar>(q: &Mat3<S>) -> WristAngles<S> {
    WristAngles {
        // Exact, not merely close: nothing about the pose can move the pinned joint.
        theta4: S::zero(),
        theta5: S::zero().atan2(cosine_third_entry(q)),
        theta6: read_theta6_flat(q),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::wrist_rotation;
    use crate::units::wrap_angle;
    use core::f64::consts::PI;

    /// A spread of commanded wrists, all with `sin θ5 ≠ 0`: outside the wrist singularity,
    /// which is where the three angles are separately observable and where
    /// `Zyz.wristRotation_reconstruct` applies. Angles stay inside a full turn so that the
    /// `f64` `atan2` and the trigonometric functions are the only rounding in play.
    const TRIPLES: [(f64, f64, f64); 6] = [
        (0.0, 1.1, 0.0),
        (0.3, -0.7, 2.6),
        (-2.0, 2.4, -1.4),
        (2.9, -2.2, 0.15),
        (-1.6, 0.4, 1.0),
        (1.0, 3.0, -2.3),
    ];

    /// Assert two rotations agree entry for entry, to the rounding a chain of products of
    /// cosines and sines can reach.
    fn assert_same_rotation(got: Mat3<f64>, want: Mat3<f64>, what: &str) {
        for i in 0..3 {
            for j in 0..3 {
                assert!(
                    (got.at(i, j) - want.at(i, j)).abs() < 1e-12,
                    "{what}: entry ({i}, {j}) is {}, want {}",
                    got.at(i, j),
                    want.at(i, j)
                );
            }
        }
    }

    /// Assert two angles are the same modulo a full turn. That is the shape of every
    /// read-back statement: the Lean conclusions are `Real.Angle` equalities, which is
    /// equality modulo `2π`.
    fn assert_same_angle(got: f64, want: f64, what: &str) {
        assert!(
            wrap_angle(got - want).abs() < 1e-12,
            "{what}: {got} is not {want} modulo a full turn"
        );
    }

    /// `Zyz.wristRotation_reconstruct` and `Zyz.wristRotation_reconstruct_mirror`: either
    /// branch of the reconstruction rebuilds the rotation it was read off, entry for entry.
    #[test]
    fn reconstruct_round_trips() {
        for (a, b, c) in TRIPLES {
            let q = wrist_rotation(a, b, c);
            let direct = reconstruct(&q);
            assert_same_rotation(
                wrist_rotation(direct.theta4, direct.theta5, direct.theta6),
                q,
                "reconstruct",
            );
            let mirror = reconstruct_mirror(&q);
            assert_same_rotation(
                wrist_rotation(mirror.theta4, mirror.theta5, mirror.theta6),
                q,
                "reconstruct_mirror",
            );
        }
    }

    /// `Zyz.wristRotation_mirror`: the mirrored triple is the same rotation, and the two
    /// reconstructions differ by exactly that mirror — a half turn on joints 4 and 6, the
    /// middle angle negated (`Zyz`'s module doc names the pair `(a, -β, c)` and
    /// `(a + π, β, c + π)`). The half turn is what `atan2`'s other branch costs the outer
    /// joints; negating the middle one is what keeps the product the same, the two half
    /// turns moving past the middle factor by `Zyz.rotZ_pi_mul_rotY_mul_rotZ_pi`.
    #[test]
    fn the_two_branches_are_the_same_rotation() {
        for (a, b, c) in TRIPLES {
            assert_same_rotation(
                wrist_rotation(a + PI, -b, c + PI),
                wrist_rotation(a, b, c),
                "wristRotation_mirror",
            );
            let q = wrist_rotation(a, b, c);
            let direct = reconstruct(&q);
            let mirror = reconstruct_mirror(&q);
            assert_same_angle(mirror.theta4 - direct.theta4, PI, "mirror theta4");
            assert_same_angle(mirror.theta6 - direct.theta6, PI, "mirror theta6");
            assert_same_angle(mirror.theta5 + direct.theta5, 0.0, "mirror theta5");
            // The middle relationship is exact, not merely a full turn apart: the direct
            // branch returns the `atan2` magnitude's negation and the mirror the magnitude
            // itself. That is what the solver's one branch label rides on.
            assert_eq!(mirror.theta5, -direct.theta5);
        }
    }

    /// `Zyz.wristRotation_read_theta4_coe_angle`, `..._theta6_coe_angle` and
    /// `..._theta5_coe_angle`: the reads invert the product. The outer two carry the *same*
    /// half-turn offset, `if 0 < sin θ5 then π else 0`, because both read the one factor
    /// `-sin θ5` off a unit-circle point — which is why a single branch label serves both
    /// joints. The middle read needs the label that matches the command's own sign.
    #[test]
    fn the_reads_invert_the_wrist_rotation() {
        for (a, b, c) in TRIPLES {
            let q = wrist_rotation(a, b, c);
            // Positive sine: the factor in front of the pair is negative, so the read
            // comes back a half turn around; negative sine: the read is the angle itself.
            let offset = if b.sin() > 0.0 { PI } else { 0.0 };
            assert_same_angle(read_theta4(&q), a + offset, "read_theta4");
            assert_same_angle(read_theta6(&q), c + offset, "read_theta6");
            let branch = if b.sin() > 0.0 { 1 } else { -1 };
            assert_same_angle(read_theta5(&q, branch), b, "read_theta5");
            // The other label is the mirrored branch, and there the read is `-θ5`.
            assert_same_angle(read_theta5(&q, -branch), -b, "read_theta5, other label");
        }
        // On the positive half of the sine the label is `+1` outright.
        let q = wrist_rotation(0.3, 1.1, -0.7);
        assert_same_angle(read_theta5(&q, 1), 1.1, "read_theta5 at +1");
    }

    /// `Zyz.wristRotation_hypot_third_column`, and the entry
    /// `Kinematics.rotZ_mul_rotY_mul_rotZ_entries` gives alongside it: the third column's
    /// `(x, y)` length is `|sin θ5|` — a length cannot see the sign of the middle angle —
    /// and `Q 2 2` is `cos θ5`. These are `InverseKinematics.wristSine` and `wristCosine`,
    /// the pair the middle read is taken of.
    #[test]
    fn the_third_column_reports_the_middle_angle() {
        for (a, b, c) in TRIPLES {
            let q = wrist_rotation(a, b, c);
            assert!((hypot_third_column(&q) - b.sin().abs()).abs() < 1e-12);
            assert!((cosine_third_entry(&q) - b.cos()).abs() < 1e-12);
        }
    }

    /// `Zyz.wristRotation_reconstruct_flat`: at `sin θ5 = 0` joints 4 and 6 share an axis
    /// and only `θ4 + θ6` (`Zyz.wristRotation_zero_middle`) or `θ4 - θ6`
    /// (`Zyz.wristRotation_pi_middle`) survives, so the solver's split — joint 4 pinned at
    /// zero, the combination handed to joint 6 — has to rebuild `Q` in both halves of the
    /// singular set.
    #[test]
    fn the_flat_branch_holds_joint_four_at_zero() {
        for a in [0.0, 0.9, -2.4] {
            for c in [0.0, 1.7, -0.6] {
                for b in [0.0, PI] {
                    let q = wrist_rotation(a, b, c);
                    let flat = reconstruct_flat(&q);
                    assert_eq!(flat.theta4, 0.0);
                    // `θ5` is `0` or `π`, the two angles `rotY` cannot tell apart.
                    assert!(flat.theta5.sin().abs() < 1e-12);
                    assert_same_rotation(
                        wrist_rotation(flat.theta4, flat.theta5, flat.theta6),
                        q,
                        "reconstruct_flat",
                    );
                }
            }
        }
    }

    /// The reconstruction is written against [`Scalar`], not `f64`: the same code runs at
    /// the other scalars the crate implements, which is what the trait split in
    /// [`crate::scalar`] is for. `f32` is only implemented under `std`, so this is gated
    /// to the configuration that has it.
    #[cfg(feature = "std")]
    #[test]
    fn the_reconstruction_runs_over_any_scalar() {
        let q: Mat3<f32> = wrist_rotation(0.3f32, -0.7f32, 2.6f32);
        let r = reconstruct(&q);
        let rebuilt = wrist_rotation(r.theta4, r.theta5, r.theta6);
        for i in 0..3 {
            for j in 0..3 {
                assert!((rebuilt.at(i, j) - q.at(i, j)).abs() < 1e-5);
            }
        }
    }
}
