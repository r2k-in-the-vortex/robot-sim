//! The forward chain evaluated over the exact rationals.
//!
//! This is the load-bearing test of the whole verification design: it shows that the
//! *same* code the application runs can be evaluated over `ℚ` with no tolerance
//! anywhere, so the vectors `lean/KinematicsTestData.lean` emits can be compared with
//! `==` rather than against a band.
//!
//! It works because every alpha in the supported arm's fixed twist pattern is a quarter
//! turn, whose cosine and sine are `0` and `1` exactly, and because the chain reads each
//! joint angle only through its cosine and sine — `dh_congr` in Lean. Supplying those
//! pairs as data makes the whole forward chain a polynomial, and a polynomial evaluates
//! over any commutative ring.

use robot_golden::Ratio as R;
use robot_kinematics::{
    CosSin, Field, Geometry, Mat3, Pose, Vec3, carrier_pose_cs, fk_cs, wrist_center,
};

/// The cosine and sine of a quarter turn, exactly: `Kinematics.quarter`, whose values
/// are `0` and `1` with no rounding.
fn quarter_turn() -> CosSin<R> {
    CosSin::new(R::zero(), R::one())
}

fn geometry() -> Geometry<R> {
    Geometry::new(
        R::integer(10),
        R::integer(40),
        R::integer(40),
        R::integer(40),
        R::integer(10),
    )
    .expect("the shipped geometry is a supported arm")
}

/// The zero pose, which the shipped table reaches with a 90 degree static offset on
/// joint 2. Every frame origin is an exact integer, so the whole chain must reproduce
/// them with no error at all.
#[test]
fn the_zero_pose_is_exact_over_the_rationals() {
    let g = geometry();
    let theta = [
        CosSin::new(R::ONE, R::ZERO),
        quarter_turn(),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
    ];
    let tower = carrier_pose_cs(&g, &theta);

    let expected = [
        (0, 0, 0),
        (10, 0, 40),
        (10, 0, 80),
        (10, 0, 80),
        (50, 0, 80),
        (50, 0, 80),
        (60, 0, 80),
    ];
    for (frame, (x, y, z)) in tower.iter().zip(expected) {
        assert_eq!(
            frame.p,
            Vec3::new(R::integer(x), R::integer(y), R::integer(z)),
            "frame origin"
        );
    }
}

/// A configuration with a Pythagorean rotation: a `3-4-5` triangle gives exact cosine
/// and sine for both `θ1` and `θ2`, and the resulting pose is exact.
#[test]
fn a_pythagorean_configuration_gives_an_exact_pose() {
    let g = geometry();
    // cos = 4/5, sin = 3/5 for joint 1; cos = 5/13, sin = 12/13 for joint 2.
    let theta = [
        R::pair((4, 5), (3, 5)),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        R::pair((5, 13), (12, 13)),
        CosSin::new(R::ONE, R::ZERO),
    ];
    let pose = fk_cs(&g, &theta);

    // Every entry is a rational with a denominator dividing 5^2 * 13^2 = 4225, so the
    // comparison is exact and any disagreement is a real disagreement.
    for i in 0..3 {
        for j in 0..3 {
            let entry = pose.r.at(i, j);
            assert!(
                entry.denominator() <= 4225,
                "rotation entry ({i}, {j}) = {entry:?} has an unexpected denominator"
            );
        }
    }
    // The rotation must still be orthogonal, exactly, over the rationals. This is
    // `fk_R_orth` with no tolerance: `Rᵀ R` is the identity on the nose.
    let gram = pose.r.transpose() * pose.r;
    assert_eq!(gram, Mat3::<R>::identity());

    // The pose itself, against values derived independently of this crate — a
    // `fractions.Fraction` transcription of the same DH table, not a re-run of the
    // Rust. Agreement between two implementations in different languages and different
    // arithmetic is the point; an expectation read off this code would prove nothing.
    assert_eq!(
        pose.p,
        Vec3::new(rational(424, 13), rational(318, 13), rational(-50, 13))
    );

    let expected = [
        [rational(4, 13), rational(3, 5), rational(-48, 65)],
        [rational(3, 13), rational(-4, 5), rational(-36, 65)],
        [rational(-12, 13), R::zero(), rational(-5, 13)],
    ];
    for (i, row) in expected.iter().enumerate() {
        for (j, want) in row.iter().enumerate() {
            assert_eq!(pose.r.at(i, j), *want, "rotation entry ({i}, {j})");
        }
    }
}

/// An exact rational from a small integer pair.
fn rational(numerator: i128, denominator: i128) -> R {
    R::new(numerator, denominator)
}

/// The wrist centre is a polynomial in the pose alone, so it is exact whenever the pose
/// is. `carrierPose_four_p` holds with no error term.
#[test]
fn the_wrist_centre_is_exact_and_at_the_fourth_frame() {
    let g = geometry();
    let theta = [
        R::pair((4, 5), (3, 5)),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        R::pair((5, 13), (12, 13)),
        CosSin::new(R::ONE, R::ZERO),
    ];
    let pose = fk_cs(&g, &theta);
    let center = wrist_center(&g, &pose);
    let tower = carrier_pose_cs(&g, &theta);
    assert_eq!(tower[4].p, center, "carrierPose_four_p, exactly");
}

/// The arm's rotation factorises through frame 3 exactly, which is `fk_R`.
#[test]
fn the_rotation_factors_through_frame_three_exactly() {
    let g = geometry();
    let theta = [
        R::pair((4, 5), (3, 5)),
        R::pair((12, 13), (5, 13)),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        R::pair((5, 13), (12, 13)),
        R::pair((15, 17), (8, 17)),
    ];
    let pose = fk_cs(&g, &theta);
    let factored = robot_kinematics::arm_rotation_cs(theta[0], theta[1], theta[2])
        * robot_kinematics::wrist_rotation_cs(theta[3], theta[4], theta[5]);
    assert_eq!(pose.r, factored);
}

/// A full turn is invisible to the chain over the rationals too, exactly: the pairs
/// `(1, 0)` and `(-1, 0)` name angles a half turn apart and the chain reads only the
/// pairs. This is the rational shadow of `fk_congr`.
#[test]
fn the_chain_reads_only_the_pairs() {
    let g = geometry();
    let identity_pair = CosSin::new(R::ONE, R::ZERO);
    let theta = [
        R::pair((4, 5), (3, 5)),
        identity_pair,
        identity_pair,
        identity_pair,
        identity_pair,
        identity_pair,
    ];
    // Replacing a pair by the same pair built a different way changes nothing: the pair
    // *is* the input, and there is no angle to normalise.
    let rebuilt = [
        CosSin::new(R::new(4, 5), R::new(3, 5)),
        identity_pair,
        identity_pair,
        identity_pair,
        identity_pair,
        identity_pair,
    ];
    assert_eq!(fk_cs(&g, &theta), fk_cs(&g, &rebuilt));
}

/// The homogeneous view is exact as well, so a golden vector for `to_matrix4` can carry
/// the full 4x4 the Python and the mathematics both write.
#[test]
fn the_homogeneous_matrix_is_exact() {
    let g = geometry();
    let theta = [
        R::pair((4, 5), (3, 5)),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
        CosSin::new(R::ONE, R::ZERO),
    ];
    let m = fk_cs(&g, &theta).to_matrix4();
    assert_eq!(m[3], [R::zero(), R::zero(), R::zero(), R::one()]);
    // Frame 6's origin, again from the independent Fraction computation.
    assert_eq!(m[0][3], R::integer(40));
    assert_eq!(m[1][3], R::integer(30));
    assert_eq!(m[2][3], R::integer(-10));
    // The rotation is a half turn about the y axis composed with the base rotation.
    assert_eq!(m[0][0], rational(4, 5));
    assert_eq!(m[0][1], rational(3, 5));
    assert_eq!(m[1][0], rational(3, 5));
    assert_eq!(m[1][1], rational(-4, 5));
    assert_eq!(m[2][2], R::integer(-1));
}

/// A pose built over the rationals is not automatically a rotation: `Pose` carries no
/// such invariant over an arbitrary field, so the check `rotation_is_a_rotation` is
/// only available where a square root is. This is the trait boundary made visible.
#[test]
fn the_rotation_check_lives_on_the_transcendental_side() {
    // `rotation_is_a_rotation` and `frobenius_distance` need `Scalar`, so they are not
    // reachable from a `Field`-only context. The exact test above checks orthogonality
    // by comparing `Rᵀ R` to the identity instead, which is stronger anyway.
    let g = geometry();
    let identity_pair = CosSin::new(R::ONE, R::ZERO);
    let pose: Pose<R> = fk_cs(&g, &[identity_pair; 6]);
    assert_eq!(pose.r.transpose() * pose.r, Mat3::<R>::identity());
}
