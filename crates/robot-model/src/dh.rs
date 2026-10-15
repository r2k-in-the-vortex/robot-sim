//! The DH table and the conversions out of it.

use robot_kinematics::{FRAME_COUNT, Geometry, GeometryError, JOINT_COUNT, Pose, units};

/// One row of the DH table, in the units the document stores.
///
/// The angle is a **static offset**: `robot_parameters.json` never stores the runtime
/// joint angle, and saving deliberately drops it (`simulator.py`, README "DH Parameters").
/// Runtime angles start at zero on every launch.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct DhRow {
    /// The joint's zero-position angle, in degrees, added to the runtime angle.
    pub theta_offset_deg: f64,
    /// Link offset along the previous frame's z axis.
    pub d: f64,
    /// Link length along this frame's x axis.
    pub a: f64,
    /// Twist of the next z axis about this frame's x axis, in degrees.
    pub alpha_deg: f64,
}

impl DhRow {
    /// A row with no rotation and no offset: the identity transform.
    pub const ZERO: Self = Self {
        theta_offset_deg: 0.0,
        d: 0.0,
        a: 0.0,
        alpha_deg: 0.0,
    };

    pub const fn new(theta_offset_deg: f64, d: f64, a: f64, alpha_deg: f64) -> Self {
        Self {
            theta_offset_deg,
            d,
            a,
            alpha_deg,
        }
    }
}

/// The six DH rows, in the order `robot_parameters.json` lists them.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct DHParameters {
    pub joints: [DhRow; JOINT_COUNT],
}

impl DHParameters {
    pub const fn new(joints: [DhRow; JOINT_COUNT]) -> Self {
        Self { joints }
    }

    /// The table `robot_parameters.json` ships, matching `DEFAULT_DH_VALUES` in
    /// `simulator.py` lines 30-37.
    ///
    /// These are illustrative starter dimensions, not measurements of a specific robot.
    pub const fn shipped() -> Self {
        Self::new([
            DhRow::new(0.0, 40.0, 10.0, 90.0),
            DhRow::new(90.0, 0.0, 40.0, 0.0),
            DhRow::new(0.0, 0.0, 0.0, 90.0),
            DhRow::new(0.0, 40.0, 0.0, 90.0),
            DhRow::new(0.0, 0.0, 0.0, -90.0),
            DhRow::new(0.0, 10.0, 0.0, 0.0),
        ])
    }

    /// The total DH angles, in radians, for a set of runtime joint angles in degrees.
    ///
    /// This is the boundary the crate exists to hold: the document and the UI work in
    /// degrees with the offset kept separate, and the kinematics core works in radians
    /// with the offset already folded in. `units::total_angle` does the fold, matching
    /// `compose_dh_parameters` in `kinematics.py`.
    pub fn total_angles_rad(&self, runtime_deg: &[f64; JOINT_COUNT]) -> [f64; JOINT_COUNT] {
        core::array::from_fn(|joint| {
            units::total_angle(self.joints[joint].theta_offset_deg, runtime_deg[joint])
        })
    }

    /// The arm's free dimensions, if this table describes the supported arm.
    ///
    /// The kinematics core fixes the structure — `alpha` of `90, 0, 90, 90, -90, 0` with
    /// `a3 = a4 = a5 = a6 = 0` and `d2 = d3 = d5 = 0` — and [`Geometry`] is the evidence
    /// that a table is that arm. A table that departs from it still draws and still jogs
    /// joint by joint (README, "Inverse kinematics"): the arm's own link lengths are not
    /// checked here, only the five that stay free.
    ///
    /// `geometry` maps the rows the way `joint_transforms_cs` reads them: joint 1 supplies
    /// `d1` and `a1`, joint 2 supplies the first link length as `a2`, joint 4 supplies the
    /// second as `d4`, and joint 6 supplies the tool offset `d6`.
    pub fn geometry(&self) -> Result<Geometry<f64>, GeometryError> {
        Geometry::new(
            self.joints[0].a,
            self.joints[0].d,
            self.joints[1].a,
            self.joints[3].d,
            self.joints[5].d,
        )
    }

    /// The seven cumulative frame poses `⁰T_0 … ⁰T_6` for a set of runtime angles.
    ///
    /// This is `forward_kinematics` in `simulator.py` (line 865) and what the 3D view
    /// draws. `None` when the table is not the supported arm — the renderer falls back to
    /// the frame origins it can still compute.
    pub fn carrier_pose(
        &self,
        runtime_deg: &[f64; JOINT_COUNT],
    ) -> Result<[Pose<f64>; FRAME_COUNT], GeometryError> {
        let geometry = self.geometry()?;
        let theta = self.total_angles_rad(runtime_deg);
        Ok(robot_kinematics::carrier_pose(&geometry, &theta))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_shipped_table_is_the_supported_arm() {
        let geometry = DHParameters::shipped().geometry().expect("shipped table");
        // Geometry::shipped documents exactly these five numbers.
        assert_eq!(geometry.a1, 10.0);
        assert_eq!(geometry.d1, 40.0);
        assert_eq!(geometry.link_one, 40.0);
        assert_eq!(geometry.link_two, 40.0);
        assert_eq!(geometry.tool_offset, 10.0);
    }

    #[test]
    fn the_theta_offset_is_folded_into_the_total_angle() {
        // Joint 2's static offset is 90 degrees, so zero runtime angles are *not* the
        // zero angle vector. This is the trap the offset exists to represent.
        let theta = DHParameters::shipped().total_angles_rad(&[0.0; JOINT_COUNT]);
        assert!((theta[0] - 0.0).abs() < 1e-15);
        assert!((theta[1] - core::f64::consts::FRAC_PI_2).abs() < 1e-15);
        for joint in [2, 3, 4, 5] {
            assert!(theta[joint].abs() < 1e-15);
        }
    }

    #[test]
    fn zero_runtime_angles_reproduce_the_documented_frame_origins() {
        // The same numbers as the kinematics core's own test and as
        // `doc/main_window_image.png`: the arm lies along +x with the tool 60 units out.
        let tower = DHParameters::shipped()
            .carrier_pose(&[0.0; JOINT_COUNT])
            .expect("shipped table");
        let expected = [
            (0.0, 0.0, 0.0),
            (10.0, 0.0, 40.0),
            (10.0, 0.0, 80.0),
            (10.0, 0.0, 80.0),
            (50.0, 0.0, 80.0),
            (50.0, 0.0, 80.0),
            (60.0, 0.0, 80.0),
        ];
        for (frame, (x, y, z)) in tower.iter().zip(expected) {
            assert!((frame.p.x() - x).abs() < 1e-12, "frame origin x");
            assert!((frame.p.y() - y).abs() < 1e-12, "frame origin y");
            assert!((frame.p.z() - z).abs() < 1e-12, "frame origin z");
        }
    }

    #[test]
    fn a_degenerate_arm_is_reported_rather_than_drawn_wrong() {
        // A table whose first link is zero has no Geometry, so forward kinematics has
        // nothing to say; the view keeps working on the origins alone.
        let mut parameters = DHParameters::shipped();
        parameters.joints[1].a = 0.0;
        assert_eq!(
            parameters.geometry(),
            Err(GeometryError::LinkOneNotPositive)
        );
        assert!(parameters.carrier_pose(&[0.0; JOINT_COUNT]).is_err());
    }
}
