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
//!
//! # Naming a button
//!
//! The panel has fourteen jog buttons, and every one of them means the same thing whether it
//! is clicked once or held down ([`crate::session`] drives both modes through one path).
//! [`JogTarget`] is that meaning as a value: one of the four pose jogs below, or one joint.
//! The split matters because a pose jog needs the geometry and the solver while a joint jog
//! needs neither — a table the pose jogs refuse can still be joint-jogged — so
//! [`PoseJog::offset`] and the joint arithmetic are never mixed up, and the panel builds the
//! same target from the same `(frame, rotating, axis)` triple it uses for the label.

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

/// Which frame a Cartesian jog acts in — the reference's two button groups,
/// `simulator.py:251-256`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum JogFrame {
    Base,
    Tool,
}

impl JogFrame {
    /// The translation button of this group's `axis`, `simulator.py:280-296`.
    pub const fn translation(self, axis: Axis) -> PoseJog {
        match self {
            JogFrame::Base => PoseJog::BaseTranslation(axis),
            JogFrame::Tool => PoseJog::ToolTranslation(axis),
        }
    }

    /// The rotation button of this group's `axis`, the row the reference prefixes with `R`.
    pub const fn rotation(self, axis: Axis) -> PoseJog {
        match self {
            JogFrame::Base => PoseJog::BaseRotation(axis),
            JogFrame::Tool => PoseJog::ToolRotation(axis),
        }
    }
}

/// The four pose jogs: a translation or a rotation, in one of the two frames.
///
/// The translation/rotation split is not cosmetic. A translation moves the pose's origin and a
/// rotation leaves it exactly where it was, which the four functions below already say; and
/// the two read different step fields (`jog_step` against `rotation_step`) and report
/// different verbs ("Moved" against "Rotated").
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum PoseJog {
    BaseTranslation(Axis),
    ToolTranslation(Axis),
    BaseRotation(Axis),
    ToolRotation(Axis),
}

impl PoseJog {
    /// The pose this jog produces `amount` away from `pose`.
    ///
    /// `amount` is a signed length for the translations and a signed **angle in degrees** for
    /// the rotations, which is the unit both step fields, the status line and the held-button
    /// rate all speak. The rotation arms convert after applying the sign, exactly as the
    /// reference's `math.radians(direction * step)` does (`simulator.py:420`, `:429`).
    pub fn offset(self, pose: &Pose<f64>, amount: f64) -> Pose<f64> {
        match self {
            PoseJog::BaseTranslation(axis) => offset_pose_translation(pose, axis, amount),
            PoseJog::ToolTranslation(axis) => offset_pose_tool_translation(pose, axis, amount),
            PoseJog::BaseRotation(axis) => rotate_pose_world_axis(pose, axis, amount.to_radians()),
            PoseJog::ToolRotation(axis) => rotate_pose_tool_axis(pose, axis, amount.to_radians()),
        }
    }

    /// Whether this jog turns the pose rather than moving it — the `R` in the button label, and
    /// the field the amount is read from.
    pub const fn rotates(self) -> bool {
        matches!(self, PoseJog::BaseRotation(_) | PoseJog::ToolRotation(_))
    }
}

/// One jog button's whole meaning: a pose jog or one joint.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum JogTarget {
    Pose(PoseJog),
    Joint(usize),
}

impl JogTarget {
    /// The Cartesian button of `frame`'s group, `rotating` selecting the `R` row.
    ///
    /// The label and the target both come from this one `(frame, rotating, axis)` triple at
    /// the call site, so the sign and the row a button advertises cannot drift from the jog it
    /// performs.
    pub const fn cartesian(frame: JogFrame, rotating: bool, axis: Axis) -> Self {
        JogTarget::Pose(if rotating {
            frame.rotation(axis)
        } else {
            frame.translation(axis)
        })
    }
}

/// Which of the two jog modes the panel's radio pair selects.
///
/// A field of [`crate::session::Session`] rather than a resource of its own: it is a jog
/// control like the three step fields, and the handlers are what it steers.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub enum JogMode {
    /// One click is one step — the reference's only mode (`simulator.py:399-433`).
    #[default]
    Step,
    /// One second of holding a button is one step, measured from the press.
    Continuous,
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

    /// [`PoseJog::offset`] is the four helpers the reference spells out, with each rotation's
    /// signed amount converted to radians in the same place the handler converted it. The
    /// comparison is bit for bit: this must not become arithmetic of its own.
    #[test]
    fn a_pose_jog_offsets_the_pose_the_way_its_helper_does() {
        let pose = tool_pose(TEST_ANGLES);
        for amount in [-2.5, 0.0, 0.5, 1.0] {
            let cases: [(PoseJog, Pose<f64>); 4] = [
                (
                    PoseJog::BaseTranslation(Axis::X),
                    offset_pose_translation(&pose, Axis::X, amount),
                ),
                (
                    PoseJog::ToolTranslation(Axis::Y),
                    offset_pose_tool_translation(&pose, Axis::Y, amount),
                ),
                (
                    PoseJog::BaseRotation(Axis::Z),
                    rotate_pose_world_axis(&pose, Axis::Z, amount.to_radians()),
                ),
                (
                    PoseJog::ToolRotation(Axis::X),
                    rotate_pose_tool_axis(&pose, Axis::X, amount.to_radians()),
                ),
            ];
            for (jog, expected) in cases {
                let actual = jog.offset(&pose, amount);
                for row in 0..3 {
                    for column in 0..3 {
                        assert_eq!(
                            actual.r.at(row, column).to_bits(),
                            expected.r.at(row, column).to_bits(),
                            "{jog:?} at {amount}: rotation entry ({row}, {column})"
                        );
                    }
                    assert_eq!(
                        actual.p[row].to_bits(),
                        expected.p[row].to_bits(),
                        "{jog:?} at {amount}: translation row {row}"
                    );
                }
            }
        }
    }

    /// A frame's two rows name the four pose jogs, and the `rotating` flag the panel builds
    /// its target from is the same bit as the `R` it puts in the label.
    #[test]
    fn a_frame_builds_the_four_pose_jogs_it_carries() {
        for axis in Axis::ALL {
            assert_eq!(
                JogFrame::Base.translation(axis),
                PoseJog::BaseTranslation(axis)
            );
            assert_eq!(
                JogFrame::Tool.translation(axis),
                PoseJog::ToolTranslation(axis)
            );
            assert_eq!(JogFrame::Base.rotation(axis), PoseJog::BaseRotation(axis));
            assert_eq!(JogFrame::Tool.rotation(axis), PoseJog::ToolRotation(axis));

            for rotating in [false, true] {
                let JogTarget::Pose(pose) = JogTarget::cartesian(JogFrame::Tool, rotating, axis)
                else {
                    panic!("a Cartesian button is a pose jog");
                };
                assert_eq!(pose.rotates(), rotating);
                let label = crate::ui::jog_button_label(axis, -1, rotating);
                assert_eq!(label.starts_with('R'), rotating, "{axis:?}: {label}");
            }
        }
    }

    /// The reference's mode is the default, so an upgrade does not change what a click does.
    #[test]
    fn the_default_mode_is_the_reference_one_step_per_click() {
        assert_eq!(JogMode::default(), JogMode::Step);
    }
}
