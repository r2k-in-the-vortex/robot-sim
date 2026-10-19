//! Per-joint physical motion limits.
//!
//! These are the arm's own limits, not a motion command's. A command may ask for
//! any speed it likes; the planner takes the tighter of the command's request and the
//! joint's physical limit, component by component, so a command that stays below the
//! physical limits is left alone and one that reaches past them is capped.
//!
//! The units are the document's: degrees and seconds. They are the units the planner
//! consumes directly, since its arithmetic is unit-agnostic.

use robot_kinematics::JOINT_COUNT;

/// The velocity a joint gets when the document says nothing, in degrees per second.
pub const DEFAULT_VELOCITY_DEG_S: f64 = 90.0;

/// The acceleration a joint gets when the document says nothing, in degrees per second
/// squared.
pub const DEFAULT_ACCELERATION_DEG_S2: f64 = 180.0;

/// The jerk a joint gets when the document says nothing, in degrees per second cubed.
pub const DEFAULT_JERK_DEG_S3: f64 = 360.0;

/// One joint's physical velocity, acceleration and jerk ceiling.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct JointMotionLimits {
    /// Degrees per second.
    pub velocity_deg_s: f64,
    /// Degrees per second squared.
    pub acceleration_deg_s2: f64,
    /// Degrees per second cubed.
    pub jerk_deg_s3: f64,
}

impl JointMotionLimits {
    pub const fn new(velocity_deg_s: f64, acceleration_deg_s2: f64, jerk_deg_s3: f64) -> Self {
        Self {
            velocity_deg_s,
            acceleration_deg_s2,
            jerk_deg_s3,
        }
    }

    /// Whether every component is a finite positive number.
    ///
    /// The planner rejects a non-positive limit, and a document that carries one is a
    /// typo rather than a request to stop the joint, so the file's reader refuses it.
    pub fn is_positive_finite(self) -> bool {
        [
            self.velocity_deg_s,
            self.acceleration_deg_s2,
            self.jerk_deg_s3,
        ]
        .iter()
        .all(|value| value.is_finite() && *value > 0.0)
    }
}

impl Default for JointMotionLimits {
    fn default() -> Self {
        Self::new(
            DEFAULT_VELOCITY_DEG_S,
            DEFAULT_ACCELERATION_DEG_S2,
            DEFAULT_JERK_DEG_S3,
        )
    }
}

/// The physical limits of all six joints, in joint order.
///
/// One row per joint because the joints move different masses through different gearboxes;
/// a uniform table is only the default, not the shape.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct MotionLimits {
    pub joints: [JointMotionLimits; JOINT_COUNT],
}

impl MotionLimits {
    pub const fn new(joints: [JointMotionLimits; JOINT_COUNT]) -> Self {
        Self { joints }
    }

    /// Whether every joint's limits are finite and positive.
    pub fn is_positive_finite(self) -> bool {
        self.joints.iter().all(|joint| joint.is_positive_finite())
    }
}

impl Default for MotionLimits {
    fn default() -> Self {
        Self::new([JointMotionLimits::default(); JOINT_COUNT])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_defaults_are_positive_and_finite() {
        assert!(MotionLimits::default().is_positive_finite());
        let row = JointMotionLimits::default();
        assert_eq!(row.velocity_deg_s, DEFAULT_VELOCITY_DEG_S);
        assert_eq!(row.acceleration_deg_s2, DEFAULT_ACCELERATION_DEG_S2);
        assert_eq!(row.jerk_deg_s3, DEFAULT_JERK_DEG_S3);
    }

    #[test]
    fn a_zero_negative_or_non_finite_component_is_invalid() {
        for row in [
            JointMotionLimits::new(0.0, 1.0, 1.0),
            JointMotionLimits::new(1.0, -1.0, 1.0),
            JointMotionLimits::new(1.0, 1.0, f64::INFINITY),
            JointMotionLimits::new(f64::NAN, 1.0, 1.0),
        ] {
            assert!(!row.is_positive_finite(), "{row:?}");
        }
    }
}
