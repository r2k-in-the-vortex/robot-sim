//! The pose jogs: the arithmetic behind the Translate and Rotate button groups.
//!
//! The reference keeps a pose as a 4x4 homogeneous matrix and works on its entries
//! directly (`simulator.py:60-144`); the Rust keeps the rotation and the translation in a
//! [`Pose`], so the same operations read as a line each. What has to survive the change of
//! shape is the arithmetic: which axis of which frame a jog runs along, whether the
//! rotation pre- or post-multiplies, and — since the result is compared against a
//! solution pose at a millimetre's tolerance by the IK step downstream — the order the
//! floating-point operations happen in.
//!
//! # The two frames
//!
//! A base-axis jog adds to the pose's translation along a coordinate axis of the base
//! frame and leaves the orientation alone, which is [`offset_pose_translation`]. A
//! tool-axis jog adds along an axis *the pose itself carries*, which is a column of its
//! rotation block rather than a row — [`offset_pose_tool_translation`] is the one line
//! where that distinction lives, and the reference spells it out at `simulator.py:75-93`.
//! The rotations divide the same way: pre-multiplying turns the pose about the base axes
//! ([`rotate_pose_world_axis`]), post-multiplying turns it about the axes it already
//! carries ([`rotate_pose_tool_axis`]).
//!
//! # Validation
//!
//! The Python helpers raise `ValueError` for three things: a pose that is not 4x4, an
//! axis that is not 0, 1 or 2, and a non-finite distance or angle
//! (`simulator.py:64-69`, `:83-88`, `:110-115`, `:133-138`). Two of the three cannot
//! happen here: [`Pose`] has no shape to get wrong, and [`Axis`] has no fourth variant.
//! The third is left to the caller, because it is the caller who has the user's text: the
//! reference reads its step entries through `_read_step` (`simulator.py:355-360`), which
//! rejects anything but a positive finite number before any of this runs. A non-finite
//! distance or angle passed here propagates NaN through the pose rather than being
//! stopped, so the caller must validate first; these functions never panic.

use robot_kinematics::{Mat3, Pose, Vec3};

/// One of the three coordinate axes, which is also how the reference names them in
/// its status strings (`'XYZ'[axis]`, `simulator.py:405`).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Axis {
    X,
    Y,
    Z,
}

impl Axis {
    /// All three, in the order the reference's strings index them.
    pub const ALL: [Axis; 3] = [Axis::X, Axis::Y, Axis::Z];

    /// `0`, `1`, `2`.
    pub const fn index(self) -> usize {
        self as usize
    }

    /// `'X'`, `'Y'`, `'Z'`.
    pub const fn letter(self) -> char {
        // `'XYZ'[axis]` in the reference; same order, same letters.
        match self {
            Axis::X => 'X',
            Axis::Y => 'Y',
            Axis::Z => 'Z',
        }
    }

    /// The axis at `index`, or `None` outside `0..3`.
    ///
    /// Python's `axis not in (0, 1, 2)` test (`simulator.py:66`) in the shape a caller
    /// looping over a row of buttons wants: the button row is indexed by number, the jog
    /// itself by [`Axis`].
    ///
    /// The window's own rows iterate [`Axis::ALL`] rather than indexing, so nothing in
    /// the binary calls this yet and the bin target would name it as dead code. The allow
    /// is for that and can go the day a numeric index reaches one of these; everything
    /// else here is called from `session` or `ui` and needs no such thing.
    #[allow(dead_code)]
    pub fn from_index(index: usize) -> Option<Axis> {
        Axis::ALL.get(index).copied()
    }
}

/// `_axis_rotation`, `simulator.py:95`.
///
/// The three are the rotation matrices of `Mat3::rot_x`, `rot_y` and `rot_z` — this is a
/// transcription of the reference's explicit literals (`simulator.py:99-103`) and the
/// tests hold it to the crate's bit for bit, because a sign or a transpose here is a jog
/// that turns the wrong way, which nothing downstream can tell from a correct one.
///
/// The reference computes the cosine and the sine once per call (`simulator.py:97-98`)
/// and reuses them across the whole matrix; so does this, in the same order, so the two
/// produce the same bits for the same angle.
pub fn axis_rotation(axis: Axis, angle: f64) -> Mat3<f64> {
    let cosine = angle.cos();
    let sine = angle.sin();
    match axis {
        Axis::X => Mat3::from_rows([[1.0, 0.0, 0.0], [0.0, cosine, -sine], [0.0, sine, cosine]]),
        Axis::Y => Mat3::from_rows([[cosine, 0.0, sine], [0.0, 1.0, 0.0], [-sine, 0.0, cosine]]),
        Axis::Z => Mat3::from_rows([[cosine, -sine, 0.0], [sine, cosine, 0.0], [0.0, 0.0, 1.0]]),
    }
}

/// `offset_pose_translation`, `simulator.py:60`.
///
/// A base-axis offset: `result[axis][3] += distance` (`simulator.py:71`), the fourth
/// column entry of one row, which is exactly one component of the pose's translation. The
/// other three entries of that column are copied, and the rotation block is copied
/// untouched, so the orientation is preserved exactly rather than to rounding.
pub fn offset_pose_translation(pose: &Pose<f64>, axis: Axis, distance: f64) -> Pose<f64> {
    let p = pose.p;
    let moved = match axis {
        Axis::X => Vec3::new(p.x() + distance, p.y(), p.z()),
        Axis::Y => Vec3::new(p.x(), p.y() + distance, p.z()),
        Axis::Z => Vec3::new(p.x(), p.y(), p.z() + distance),
    };
    Pose::new(pose.r, moved)
}

/// `offset_pose_tool_translation`, `simulator.py:75`.
///
/// The tool frame's axes are the columns of the pose's rotation block, so this offsets
/// along `pose.r.col(axis)` — `result[row][3] += pose[row][axis] * distance`
/// (`simulator.py:91`), a column of `pose`, not a row. Orientation is preserved exactly,
/// as above, and each component is a single multiply added to a single translation
/// entry, in the Python's order.
pub fn offset_pose_tool_translation(pose: &Pose<f64>, axis: Axis, distance: f64) -> Pose<f64> {
    Pose::new(pose.r, pose.p + pose.r.col(axis.index()) * distance)
}

/// `rotate_pose_world_axis`, `simulator.py:106`.
///
/// Pre-multiplies: `R = axis_rotation · R` (`simulator.py:120`), which is a turn about a
/// base axis. Only the rotation block is written; the origin is copied across, so it
/// stays fixed exactly, which is what lets a rotation jog be solved for as a position
/// problem in the IK step.
///
/// The product is [`Mat3`]'s, whose entries accumulate index `0`, `1`, `2` from the
/// left. Python's `sum` starts its accumulation at `0.0` and so differs from this only
/// in the sign of a term that is an exact zero — `+0.0 + -0.0` is `+0.0` where
/// `-0.0 + -0.0` is `-0.0` — which no equality test or solve sees.
pub fn rotate_pose_world_axis(pose: &Pose<f64>, axis: Axis, angle: f64) -> Pose<f64> {
    Pose::new(axis_rotation(axis, angle) * pose.r, pose.p)
}

/// `rotate_pose_tool_axis`, `simulator.py:124`.
///
/// Post-multiplies: `R = R · axis_rotation` (`simulator.py:143`), which is a turn about
/// the axes the pose already carries. The origin is copied across untouched, exactly as
/// in [`rotate_pose_world_axis`], and the accumulation note there applies here too.
pub fn rotate_pose_tool_axis(pose: &Pose<f64>, axis: Axis, angle: f64) -> Pose<f64> {
    Pose::new(pose.r * axis_rotation(axis, angle), pose.p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use robot_kinematics::{Geometry, SolutionSet, solutions};
    use std::f64::consts::{FRAC_PI_2, PI};

    /// The shipped arm's DH table, `(theta_offset_deg, d, a, alpha_deg)`: the reference's
    /// `DEFAULT_DH_VALUES` (`simulator.py:30-37`), which is also the table in
    /// `robot_parameters.json`.
    const SHIPPED_DH_DEG: [(f64, f64, f64, f64); 6] = [
        (0.0, 32.0, 10.0, 90.0),
        (90.0, 0.0, 25.0, 0.0),
        (0.0, 0.0, 0.0, 90.0),
        (0.0, 25.0, 0.0, 90.0),
        (0.0, 0.0, 0.0, -90.0),
        (0.0, 6.0, 0.0, 0.0),
    ];

    /// The runtime joint angles the Python tests jog from (`test_kinematics.py:188`).
    ///
    /// The tests below are `test_kinematics.py:172-241` transcribed; the Python takes its
    /// start pose from `forward_kinematics(...)[-1]` of the shipped table, so these build
    /// the same pose rather than reaching into the app's own scene state: a pose with a
    /// non-trivial rotation is what makes a transposed column or a post-multiply written
    /// as a pre-multiply visible at all.
    const TEST_ANGLES: [f64; 6] = [0.2, -0.3, 0.4, -0.1, 0.5, -0.6];

    /// `forward_kinematics(parameters_at_angles(...))[-1]` (`kinematics.py:64-84`): the
    /// left-nested product of the standard-DH transforms `Pose::dh` builds, at the fixed
    /// alphas and the given runtime angles.
    fn tool_pose(joint_angles_rad: [f64; 6]) -> Pose<f64> {
        let mut pose = Pose::identity();
        for ((theta_offset_deg, d, a, alpha_deg), angle) in
            SHIPPED_DH_DEG.iter().zip(joint_angles_rad)
        {
            pose = pose
                * Pose::dh(
                    theta_offset_deg.to_radians() + angle,
                    *d,
                    *a,
                    alpha_deg.to_radians(),
                );
        }
        pose
    }

    /// `test_cartesian_jogs_preserve_orientation_and_remain_solvable`
    /// (`test_kinematics.py:172-185`).
    ///
    /// The rotation block is compared with `assertEqual` in Python, so it is compared
    /// exactly here; the translation comparison is `assertAlmostEqual` at its default
    /// seven places, and the entry that does move has to move by the whole step.
    ///
    /// The Python's closing `assertTrue(inverse_kinematics(target_pose, ...))` is here too,
    /// because it is the point of the helper: a step this small leaves the pose the solver
    /// answers for, which is what makes a jog a pose problem rather than a dead end. The
    /// solver is the kinematics crate's, at the same exact tolerances the window's own step
    /// runs it at.
    #[test]
    fn a_base_axis_offset_changes_one_translation_entry_and_no_rotation_entry() {
        let pose = tool_pose([0.0; 6]);
        let step = 0.01;
        for axis in Axis::ALL {
            for direction in [-1.0, 1.0] {
                let moved = offset_pose_translation(&pose, axis, direction * step);
                assert_eq!(
                    moved.r, pose.r,
                    "{axis:?} direction {direction}: orientation changed"
                );
                for row in 0..3 {
                    let difference = moved.p[row] - pose.p[row];
                    let expected = if row == axis.index() {
                        direction * step
                    } else {
                        0.0
                    };
                    assert!(
                        (difference - expected).abs() < 1e-7,
                        "{axis:?}: translation row {row} moved by {difference}, expected {expected}"
                    );
                }
                let mut set = SolutionSet::<f64>::new();
                solutions(&Geometry::<f64>::shipped(), &moved, &mut set);
                assert!(
                    !set.is_empty(),
                    "{axis:?} direction {direction}: the offset pose is unreachable"
                );
            }
        }
    }

    /// `test_tool_translation_moves_along_the_tool_axis` (`test_kinematics.py:196-209`).
    ///
    /// The per-row expectation `step * pose[row][axis]` is what distinguishes this from
    /// [`offset_pose_translation`]: it is the rotation's *column* `axis`, so a row-indexed
    /// implementation passes only for a pose whose rotation happens to be symmetric.
    #[test]
    fn a_tool_axis_offset_moves_along_a_column_of_the_rotation_block() {
        let pose = tool_pose(TEST_ANGLES);
        let step = 2.5;
        for axis in Axis::ALL {
            let moved = offset_pose_tool_translation(&pose, axis, step);
            assert_eq!(moved.r, pose.r, "{axis:?}: orientation changed");
            for row in 0..3 {
                let difference = moved.p[row] - pose.p[row];
                let expected = step * pose.r.at(row, axis.index());
                assert!(
                    (difference - expected).abs() <= 1e-12,
                    "{axis:?}: translation row {row} moved by {difference}, expected {expected}"
                );
            }
        }
    }

    /// `test_world_rotation_jog_premultiplies_rotation_and_preserves_position`
    /// (`test_kinematics.py:187-194`).
    ///
    /// A quarter turn about Z maps the base x axis onto the base y axis, so row 0 of the
    /// rotation becomes the old row 1 negated and row 1 becomes the old row 0. A
    /// post-multiply would instead permute columns, which is the failure this pins down.
    #[test]
    fn a_world_axis_rotation_premultiplies_and_keeps_the_origin() {
        let pose = tool_pose(TEST_ANGLES);
        let rotated = rotate_pose_world_axis(&pose, Axis::Z, FRAC_PI_2);
        assert_eq!(rotated.p, pose.p, "the origin moved");
        for column in 0..3 {
            assert!(
                (rotated.r.at(0, column) + pose.r.at(1, column)).abs() <= 1e-12,
                "column {column}: row 0 is not the old row 1 negated"
            );
            assert!(
                (rotated.r.at(1, column) - pose.r.at(0, column)).abs() <= 1e-12,
                "column {column}: row 1 is not the old row 0"
            );
            assert!(
                (rotated.r.at(2, column) - pose.r.at(2, column)).abs() <= 1e-12,
                "column {column}: row 2 moved"
            );
        }
    }

    /// `test_tool_rotation_postmultiplies_and_keeps_position`
    /// (`test_kinematics.py:211-222`).
    ///
    /// Turning about the tool's own Z carries its X axis onto its Y axis, so the columns
    /// permute where the rows did above.
    #[test]
    fn a_tool_axis_rotation_postmultiplies_and_keeps_the_origin() {
        let pose = tool_pose(TEST_ANGLES);
        let turned = rotate_pose_tool_axis(&pose, Axis::Z, FRAC_PI_2);
        assert_eq!(turned.p, pose.p, "the origin moved");
        for row in 0..3 {
            assert!(
                (turned.r.at(row, 0) - pose.r.at(row, 1)).abs() <= 1e-12,
                "row {row}: column 0 is not the old column 1"
            );
            assert!(
                (turned.r.at(row, 1) + pose.r.at(row, 0)).abs() <= 1e-12,
                "row {row}: column 1 is not the old column 0 negated"
            );
            assert!(
                (turned.r.at(row, 2) - pose.r.at(row, 2)).abs() <= 1e-12,
                "row {row}: column 2 moved"
            );
        }
    }

    /// `test_tool_rotation_differs_from_world_rotation` (`test_kinematics.py:224-240`).
    ///
    /// The two agree at the base pose only because the tool's Z happens to lie along the
    /// base Z there; everywhere else they are different rotations, and the reverse jog
    /// has to undo the tool one exactly.
    #[test]
    fn tool_and_world_rotations_differ_and_undoing_the_tool_one_restores_the_pose() {
        let pose = tool_pose(TEST_ANGLES);
        let angle = 30.0_f64.to_radians();
        let tool_rotated = rotate_pose_tool_axis(&pose, Axis::Y, angle);
        let world_rotated = rotate_pose_world_axis(&pose, Axis::Y, angle);

        let mut largest_difference = 0.0_f64;
        for row in 0..3 {
            for column in 0..3 {
                let difference =
                    (tool_rotated.r.at(row, column) - world_rotated.r.at(row, column)).abs();
                largest_difference = largest_difference.max(difference);
            }
        }
        assert!(
            largest_difference > 0.1,
            "the two rotations differ by only {largest_difference}"
        );

        let restored = rotate_pose_tool_axis(&tool_rotated, Axis::Y, -angle);
        for row in 0..3 {
            for column in 0..3 {
                assert!(
                    (restored.r.at(row, column) - pose.r.at(row, column)).abs() <= 1e-12,
                    "entry ({row}, {column}) was not restored"
                );
            }
        }
    }

    /// The reference's explicit matrices and the kinematics crate's `rotX`/`rotY`/`rotZ`
    /// are the same three rotations, and this is where that is checked rather than
    /// assumed.
    ///
    /// Bit for bit, not to a tolerance: both sides call `f64`'s own `cos` and `sin` on the
    /// same angle and write the results into the same entries, so there is no rounding at
    /// all between them, and a comparison by `==` would hide a `-0.0` where a `0.0`
    /// belongs.
    #[test]
    fn axis_rotation_agrees_with_the_kinematics_crate_bit_for_bit() {
        for angle in [0.0, 0.7, FRAC_PI_2, -PI, 2.5, 1e-9] {
            let cases: [(Axis, Mat3<f64>); 3] = [
                (Axis::X, Mat3::rot_x(angle)),
                (Axis::Y, Mat3::rot_y(angle)),
                (Axis::Z, Mat3::rot_z(angle)),
            ];
            for (axis, expected) in cases {
                let actual = axis_rotation(axis, angle);
                for row in 0..3 {
                    for column in 0..3 {
                        assert_eq!(
                            actual.at(row, column).to_bits(),
                            expected.at(row, column).to_bits(),
                            "{axis:?} at {angle}: entry ({row}, {column}) differs"
                        );
                    }
                }
            }
        }
    }

    /// The three spellings of one axis agree, including at the ends of the range, so the
    /// status strings (`'XYZ'[axis]`) and the button rows (`for axis in 0..3`) cannot
    /// drift apart.
    #[test]
    fn axis_index_letter_and_lookup_agree() {
        for (index, axis) in Axis::ALL.iter().enumerate() {
            assert_eq!(axis.index(), index);
            assert_eq!(Axis::from_index(index), Some(*axis));
            assert_eq!(axis.letter(), "XYZ".chars().nth(index).unwrap());
        }
        assert_eq!(Axis::ALL.map(Axis::letter), ['X', 'Y', 'Z']);
        assert_eq!(Axis::from_index(3), None);
        assert_eq!(Axis::from_index(usize::MAX), None);
    }
}
