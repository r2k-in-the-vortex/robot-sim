//! Orbit camera and reference-grid arithmetic for the 3D viewport.
//!
//! This is the pure-math half of the view: a target point, an orbit angle pair and an
//! orthographic half-span, all in plain `f64`. No Bevy type appears here, so the framing
//! can be tested without a window, a GPU or an event loop; the scene code maps
//! [`OrbitCamera`] onto a `Transform` and an `OrthographicProjection`.
//!
//! Every rule below reproduces `simulator.py`, the matplotlib view this port has to match,
//! and the comments cite the line being matched.
//!
//! The world is Z-up, because the DH model, the STL meshes and the ground grid at
//! `simulator.py:827-856` all are. Bevy's Y-up habit is deliberately not followed: nothing
//! here simulates gravity, and matching the reference view matters more than matching an
//! engine default. Elevation is therefore measured from the XY plane, exactly as
//! matplotlib's `elev` is.
use crate::mesh::Bounds;

/// Degrees of orbit per pixel dragged (`simulator.py:1062-1063`).
const ORBIT_DEG_PER_PIXEL: f64 = 0.5;

/// matplotlib is kept off the poles by the same `view_init` call.
const ELEV_LIMIT_DEG: f64 = 85.0;

/// `simulator.py:1094-1095`: one wheel notch is 120 units and scales the span by 0.88.
const WHEEL_NOTCH: f64 = 120.0;
const WHEEL_FACTOR: f64 = 0.88;

/// `simulator.py:1114`: a zoom landing outside these bounds is dropped, never saturated.
const MIN_HALF_SPAN: f64 = 0.025;
const MAX_HALF_SPAN: f64 = 1e9;

/// `simulator.py:915-916`: radius floor of 0.5, then a 45% margin around the fitted box.
const RADIUS_FLOOR: f64 = 0.5;
const FIT_MARGIN: f64 = 1.45;

/// The framing `fit` gives a point-like scene at the origin: the degenerate bound.
const DEFAULT_HALF_SPAN: f64 = RADIUS_FLOOR * FIT_MARGIN;

/// `simulator.py:836`: the grid aims at about five divisions across the fitted radius.
const GRID_DIVISIONS: f64 = 5.0;

/// Floor on the raw grid spacing, so a sub-micron scene cannot ask for a zero step.
const MIN_GRID_RAW_SPACING: f64 = 1e-9;

/// How the 3D view is framed: a target point, an orbit angle and an orthographic half-span.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct OrbitCamera {
    pub target: [f64; 3],
    pub elev_deg: f64,
    pub azim_deg: f64,
    /// Half the height of the orthographic view volume, in model units.
    pub half_span: f64,
}

impl OrbitCamera {
    /// The literal matplotlib uses (`simulator.py:863`), kept untruncated from the Python
    /// even though the exact isometric elevation is 35.26438968... degrees: the reference
    /// view and `test_kinematics.py:508` both compare against this number.
    pub const DEFAULT_ELEV_DEG: f64 = 35.264;
    pub const DEFAULT_AZIM_DEG: f64 = -45.0;

    /// The isometric default the simulator opens with (`simulator.py:863-864`).
    ///
    /// The framing starts at the degenerate fit — a point-like scene at the origin — and
    /// the caller re-fits once the frame origins and mesh boxes are known.
    pub fn isometric() -> Self {
        Self {
            target: [0.0; 3],
            elev_deg: Self::DEFAULT_ELEV_DEG,
            azim_deg: Self::DEFAULT_AZIM_DEG,
            half_span: DEFAULT_HALF_SPAN,
        }
    }

    /// Left-drag orbit (`simulator.py:1060-1064`).
    ///
    /// `delta_y` is `current_y - previous_y`, so it grows downward and a downward drag
    /// raises the camera. Only elevation is clamped, at the poles; azimuth runs on past
    /// any number of turns because matplotlib never wraps it.
    pub fn orbit(&mut self, delta_x: f64, delta_y: f64) {
        self.elev_deg =
            (self.elev_deg + delta_y * ORBIT_DEG_PER_PIXEL).clamp(-ELEV_LIMIT_DEG, ELEV_LIMIT_DEG);
        self.azim_deg -= delta_x * ORBIT_DEG_PER_PIXEL;
    }

    /// Right-drag pan (`simulator.py:1069-1089`).
    ///
    /// `viewport_pixels` is the pixel count the view volume's height is spread over: the
    /// reference's `min(bbox.width, bbox.height)` (`simulator.py:1072`), floored at one
    /// pixel. A caller whose projection pins the vertical span passes the viewport height
    /// instead, which is the denominator that keeps a drag matched to the scene beneath it.
    /// The Python shifts the axis limits rather than the target, which moves the camera the
    /// other way by the same amount, so the visible motion is identical.
    pub fn pan(&mut self, delta_x: f64, delta_y: f64, viewport_pixels: f64) {
        // All three axes carry the fitted half-span (`simulator.py:917-919`), so the
        // largest of the three spans is just the full height of the view volume.
        let units_per_pixel = (2.0 * self.half_span) / viewport_pixels.max(1.0);
        let right = self.right();
        let up = self.up();
        let shift =
            [0, 1, 2].map(|axis| -(delta_x * right[axis] + delta_y * up[axis]) * units_per_pixel);
        self.target = [0, 1, 2].map(|axis| self.target[axis] + shift[axis]);
    }

    /// Scroll-wheel zoom (`simulator.py:1091-1103`).
    ///
    /// `delta` is the raw wheel delta, 120 to a notch. A partial notch still counts as a
    /// whole step because `steps` has a floor of one. A zero delta is the empty wheel
    /// event `simulator.py:1093` drops, and must not zoom either way.
    pub fn wheel_zoom(&mut self, delta: f64) {
        if delta == 0.0 {
            return;
        }
        let steps = (delta.abs() / WHEEL_NOTCH).max(1.0);
        let factor = if delta > 0.0 {
            WHEEL_FACTOR.powf(steps)
        } else {
            (1.0 / WHEEL_FACTOR).powf(steps)
        };
        self.zoom(factor);
    }

    /// Scale the half-span about the target (`simulator.py:1105-1116`).
    ///
    /// A zoom that would leave `[0.025, 1e9]` is discarded outright rather than clipped:
    /// the reference re-checks the new span every time, so scrolling into a bound parks
    /// the span there instead of creeping along it.
    pub fn zoom(&mut self, factor: f64) {
        let half_span = self.half_span * factor;
        if (MIN_HALF_SPAN..=MAX_HALF_SPAN).contains(&half_span) {
            self.half_span = half_span;
        }
    }

    /// Frame `bounds`, the union of every frame origin and every placed mesh box
    /// (`simulator.py:908-919`).
    ///
    /// The target becomes the center of that box and the half-span half its largest extent
    /// plus the margin `simulator.py:916` leaves around it. The orbit angles are left
    /// alone: refitting moves the viewpoint, it does not reorient it.
    ///
    /// Bounds holding nothing — no origins, no placed meshes, or a corrupt one — leave a
    /// point-like framing at the origin rather than a NaN one. `simulator.py:908` always
    /// has the base origin (0, 0, 0) in its list, so that case cannot arise there. Either
    /// way `half_span == fit_radius(bounds) * 1.45` holds afterwards, which is what keeps
    /// this camera and the grid (`simulator.py:920-926`) agreeing on the scene's size.
    pub fn fit(&mut self, bounds: Bounds) {
        self.target = fit_center(bounds).unwrap_or([0.0; 3]);
        self.half_span = fit_radius(bounds) * FIT_MARGIN;
    }

    /// The unit direction from the target toward the eye.
    ///
    /// This is `right × up` for the screen basis below, which reduces to
    /// `(cos e cos a, cos e sin a, sin e)`.
    pub fn view_direction(&self) -> [f64; 3] {
        let (elev, azim) = self.angles();
        [elev.cos() * azim.cos(), elev.cos() * azim.sin(), elev.sin()]
    }

    /// The camera's world position: target + view_direction * distance.
    ///
    /// Under an orthographic projection this is not a perspective distance — it only has
    /// to put the near and far planes clear of the model.
    pub fn eye(&self, distance: f64) -> [f64; 3] {
        let direction = self.view_direction();
        [0, 1, 2].map(|axis| self.target[axis] + direction[axis] * distance)
    }

    /// The screen-space right axis (`simulator.py:1076`).
    ///
    /// It agrees with the right axis a Z-up look-at basis produces, so panning slides
    /// along the same axes the renderer draws.
    pub fn right(&self) -> [f64; 3] {
        let (_, azim) = self.angles();
        [-azim.sin(), azim.cos(), 0.0]
    }

    /// The screen-space up axis (`simulator.py:1077-1081`); it tilts away from world +Z as
    /// elevation grows.
    pub fn up(&self) -> [f64; 3] {
        let (elev, azim) = self.angles();
        [
            -elev.sin() * azim.cos(),
            -elev.sin() * azim.sin(),
            elev.cos(),
        ]
    }

    /// Elevation and azimuth in radians, which is what every formula here works in.
    fn angles(&self) -> (f64, f64) {
        (self.elev_deg.to_radians(), self.azim_deg.to_radians())
    }
}

/// The radius [`OrbitCamera::fit`] frames `bounds` with: half its largest axis extent,
/// floored at 0.5 so even a point-like scene gets a view volume (`simulator.py:915`).
///
/// The grid takes its spacing from this same radius (`simulator.py:920-926`) rather than
/// from the half-span, so the two consumers of the scene's size share one definition.
/// Bounds holding nothing come back as the floor, never as a NaN.
pub fn fit_radius(bounds: Bounds) -> f64 {
    if let Some((min, max)) = bounds_corners(bounds) {
        let extents = [max[0] - min[0], max[1] - min[1], max[2] - min[2]];
        let largest_extent = extents.into_iter().fold(f64::NEG_INFINITY, f64::max);
        let radius = (largest_extent / 2.0).max(RADIUS_FLOOR);
        if radius.is_finite() {
            return radius;
        }
    }
    RADIUS_FLOOR
}

/// The midpoint of `bounds`, or `None` when there is no box to take it from.
fn fit_center(bounds: Bounds) -> Option<[f64; 3]> {
    let (min, max) = bounds_corners(bounds)?;
    let center = [
        (min[0] + max[0]) / 2.0,
        (min[1] + max[1]) / 2.0,
        (min[2] + max[2]) / 2.0,
    ];
    center.iter().all(|axis| axis.is_finite()).then_some(center)
}

/// `bounds` widened to `f64` corners, or `None` when it holds no box. `Bounds` is
/// `f32`-based, so this is the one place the camera crosses into it and back.
fn bounds_corners(bounds: Bounds) -> Option<([f64; 3], [f64; 3])> {
    if bounds.is_empty() {
        return None;
    }
    let min = bounds.min.map(f64::from);
    let max = bounds.max.map(f64::from);
    let finite = |corner: &[f64; 3]| corner.iter().all(|axis| axis.is_finite());
    (finite(&min) && finite(&max)).then_some((min, max))
}

/// The scale-adaptive grid spacing for a fitted radius (`simulator.py:836-842`).
///
/// The raw target of `radius / 5` is rounded up to the first of `1, 2, 5, 10` times the
/// power of ten below it, so the grid keeps roughly five divisions at any scene size.
pub fn grid_spacing(radius: f64) -> f64 {
    // `f64::max` returns the non-NaN operand, so a corrupt bound still leaves a usable
    // grid instead of a NaN spacing.
    let raw = (radius / GRID_DIVISIONS).max(MIN_GRID_RAW_SPACING);
    let magnitude = 10f64.powf(raw.log10().floor());
    [1.0, 2.0, 5.0, 10.0]
        .into_iter()
        .map(|multiplier| multiplier * magnitude)
        .find(|spacing| *spacing >= raw)
        .unwrap_or(10.0 * magnitude)
}

/// The integer multiples of `spacing` between `min` and `max`, inclusive
/// (`simulator.py:843-846`).
///
/// Indices rather than world coordinates, so callers multiply instead of accumulating
/// floats and the far end of a long run cannot drift. A range holding no multiple comes
/// back with `last < first`, and `first..=last` then yields nothing — the same set of
/// lines `simulator.py:847`'s `np.arange` draws.
pub fn grid_line_indices(min: f64, max: f64, spacing: f64) -> (i64, i64) {
    (
        (min / spacing).ceil() as i64,
        (max / spacing).floor() as i64,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Dot product, spelled out so the tests do not lean on the module's arithmetic.
    fn dot(left: [f64; 3], right: [f64; 3]) -> f64 {
        left[0] * right[0] + left[1] * right[1] + left[2] * right[2]
    }

    fn cross(left: [f64; 3], right: [f64; 3]) -> [f64; 3] {
        [
            left[1] * right[2] - left[2] * right[1],
            left[2] * right[0] - left[0] * right[2],
            left[0] * right[1] - left[1] * right[0],
        ]
    }

    fn subtract(left: [f64; 3], right: [f64; 3]) -> [f64; 3] {
        [left[0] - right[0], left[1] - right[1], left[2] - right[2]]
    }

    fn length(vector: [f64; 3]) -> f64 {
        dot(vector, vector).sqrt()
    }

    fn close(actual: f64, expected: f64, tolerance: f64, what: &str) {
        assert!(
            (actual - expected).abs() <= tolerance,
            "{what}: got {actual}, expected {expected}"
        );
    }

    fn box_bounds(min: [f32; 3], max: [f32; 3]) -> Bounds {
        Bounds { min, max }
    }

    #[test]
    fn isometric_matches_the_reference_default_view() {
        let camera = OrbitCamera::isometric();
        // test_kinematics.py:508-509 asserts these two numbers against the Python view.
        assert_eq!(camera.elev_deg, 35.264);
        assert_eq!(camera.azim_deg, -45.0);
        assert_eq!(camera.target, [0.0, 0.0, 0.0]);

        // At that elevation and azimuth the eye sits on the (1, -1, 1) diagonal.
        let component = 1.0 / 3f64.sqrt();
        let expected = [component, -component, component];
        for (actual, expected) in camera.view_direction().into_iter().zip(expected) {
            close(actual, expected, 1e-5, "view direction");
        }
    }

    #[test]
    fn orbit_clamps_elevation_but_not_azimuth() {
        let mut camera = OrbitCamera::isometric();
        camera.orbit(0.0, 10_000.0);
        assert_eq!(camera.elev_deg, 85.0);
        camera.orbit(0.0, -10_000.0);
        assert_eq!(camera.elev_deg, -85.0);

        // Azimuth is free to run past any number of turns; it is never wrapped.
        let mut camera = OrbitCamera::isometric();
        for _ in 0..400 {
            camera.orbit(-720.0, 0.0); // -720 px * 0.5 deg = a full turn per pass
        }
        assert_eq!(camera.azim_deg, -45.0 + 400.0 * 360.0);
    }

    #[test]
    fn orbit_directions_follow_the_drag() {
        let mut camera = OrbitCamera::isometric();
        camera.orbit(2.0, 0.0);
        assert!(camera.azim_deg < OrbitCamera::DEFAULT_AZIM_DEG);
        close(
            camera.azim_deg,
            -45.0 - 1.0,
            1e-12,
            "azimuth after a rightward drag",
        );

        let mut camera = OrbitCamera::isometric();
        camera.orbit(0.0, 2.0);
        assert!(camera.elev_deg > OrbitCamera::DEFAULT_ELEV_DEG);
        close(
            camera.elev_deg,
            35.264 + 1.0,
            1e-12,
            "elevation after a downward drag",
        );
    }

    #[test]
    fn wheel_zoom_applies_the_notch_factor() {
        let mut camera = OrbitCamera::isometric();
        let start = camera; // copy, so every case below compares against the same span

        camera.wheel_zoom(120.0);
        assert!(
            camera.half_span < start.half_span,
            "scrolling up must zoom in"
        );
        close(
            camera.half_span,
            start.half_span * 0.88,
            1e-12,
            "one notch in",
        );

        let zoomed_in = camera;
        camera.wheel_zoom(-120.0);
        close(
            camera.half_span,
            start.half_span,
            1e-12,
            "one notch back out",
        );
        assert_ne!(camera, zoomed_in);

        camera.wheel_zoom(240.0);
        close(
            camera.half_span,
            start.half_span * 0.88_f64.powf(2.0),
            1e-12,
            "two notches",
        );

        // A partial notch is still a whole step: `steps` floors at one (`simulator.py:1094`).
        let mut camera = OrbitCamera::isometric();
        camera.wheel_zoom(60.0);
        close(
            camera.half_span,
            start.half_span * 0.88,
            1e-12,
            "half a notch",
        );

        // A negative delta has to divide, not multiply by 0.88.
        let mut camera = OrbitCamera::isometric();
        camera.wheel_zoom(-120.0);
        close(
            camera.half_span,
            start.half_span / 0.88,
            1e-12,
            "one notch out",
        );

        // delta 0 is the empty wheel event `simulator.py:1093` ignores.
        let mut camera = OrbitCamera::isometric();
        camera.wheel_zoom(0.0);
        assert_eq!(camera, start);
    }

    #[test]
    fn zoom_ignores_half_spans_outside_the_reference_range() {
        let mut camera = OrbitCamera::isometric();

        // 0.03 * 0.5 = 0.015, below the floor: dropped, not clipped to 0.025.
        camera.half_span = 0.03;
        camera.zoom(0.5);
        assert_eq!(camera.half_span, 0.03);

        // Landing exactly on the floor is allowed (`simulator.py:1114` is inclusive).
        camera.half_span = 0.05;
        camera.zoom(0.5);
        assert_eq!(camera.half_span, 0.025);

        // One step short of the ceiling, and exactly on it.
        camera.half_span = 5e8;
        camera.zoom(2.0);
        assert_eq!(camera.half_span, 1e9);

        // Just past the ceiling: the span must stay put rather than saturate at 1e9.
        camera.half_span = 6e8;
        camera.zoom(2.0);
        assert_eq!(camera.half_span, 6e8);

        // A span already outside the range never comes back in on a neutral zoom.
        camera.half_span = 0.02;
        camera.zoom(1.0);
        assert_eq!(camera.half_span, 0.02);

        // Wheel-driven, end to end: the last legal notch lands, the next one is refused.
        let mut camera = OrbitCamera::isometric();
        camera.half_span = 0.03;
        camera.wheel_zoom(120.0);
        close(camera.half_span, 0.03 * 0.88, 1e-12, "last legal notch");
        let at_floor = camera.half_span;
        camera.wheel_zoom(120.0); // would be 0.0232, under the floor
        assert_eq!(camera.half_span, at_floor);
    }

    #[test]
    fn grid_spacing_follows_the_one_two_five_ladder() {
        // Each radius straddles the raw spacing where the ladder steps up.
        let cases = [
            (5.0, 1.0),
            (5.1, 2.0),
            (10.0, 2.0),
            (25.0, 5.0),
            (25.1, 10.0),
            (50.0, 10.0),
            (50.1, 20.0),
            (125.1, 50.0),
            (250.1, 100.0),
            (1000.0, 200.0),
            (2500.0, 500.0),
        ];
        for (radius, expected) in cases {
            assert_eq!(grid_spacing(radius), expected, "radius {radius}");
        }

        // Sub-unit magnitudes too, where `magnitude` is not 1 or 10.
        close(grid_spacing(0.1), 0.02, 1e-15, "radius 0.1");
        close(grid_spacing(0.5), 0.1, 1e-15, "radius 0.5");
    }

    #[test]
    fn grid_spacing_stays_usable_for_tiny_radii() {
        // `radius / 5` underflows for a sub-micron scene; the 1e-9 floor
        // (`simulator.py:836`) has to keep the spacing positive and finite.
        for radius in [0.0, 1e-12, 1e-9, -1.0] {
            let spacing = grid_spacing(radius);
            assert!(spacing > 0.0, "radius {radius} gave {spacing}");
            assert!(spacing.is_finite(), "radius {radius} gave {spacing}");
        }
        close(grid_spacing(0.0), 1e-9, 1e-15, "spacing for a zero radius");

        // Unlike Python's `max`, `f64::max` drops a NaN, so a corrupt bound still grids.
        assert!(grid_spacing(f64::NAN) > 0.0);
    }

    /// Walk the multiples of `spacing` across `min..=max` by value and keep the ones that
    /// land inside, the way `simulator.py:847-852` leaves it to `np.arange`.
    fn scan_line_indices(min: f64, max: f64, spacing: f64) -> Vec<i64> {
        let reach = ((max - min) / spacing).ceil() as i64 + 2;
        let middle = ((min + max) / 2.0 / spacing).round() as i64;
        (middle - reach..=middle + reach)
            .filter(|index| {
                let value = *index as f64 * spacing;
                value >= min && value <= max
            })
            .collect()
    }

    #[test]
    fn grid_line_indices_match_a_floating_point_scan() {
        let cases = [
            (-10.0, 10.0, 2.5),
            (2.3, 7.1, 1.0),   // min above zero: needs ceil, not truncation
            (-7.1, -2.3, 1.0), // max below zero: needs floor, not truncation
            (-3.75, 4.6, 0.5),
            (0.0, 100.0, 20.0),
            (-0.5, 0.5, 0.25),
        ];
        for (min, max, spacing) in cases {
            let (first, last) = grid_line_indices(min, max, spacing);
            assert_eq!(
                (first..=last).collect::<Vec<_>>(),
                scan_line_indices(min, max, spacing),
                "{min}..={max} step {spacing}"
            );
        }
    }

    #[test]
    fn grid_line_indices_tile_the_range_without_drift() {
        let (first, last) = grid_line_indices(-10.0, 10.0, 2.5);
        assert_eq!((first, last), (-4, 4));
        // Exact multiples: a caller multiplying never accumulates the error that stepping
        // in floats would (`simulator.py:847` needs a half-step slack to cope with it).
        assert_eq!(first as f64 * 2.5, -10.0);
        assert_eq!(last as f64 * 2.5, 10.0);
        assert_eq!((last - first) as usize + 1, 9);
    }

    #[test]
    fn grid_line_indices_come_back_empty_when_no_multiple_is_in_range() {
        let (first, last) = grid_line_indices(0.5, 1.5, 2.0);
        assert_eq!((first, last), (1, 0));
        assert!(last < first);
        assert_eq!((first..=last).count(), 0);

        // Same on the negative side, and a range holding exactly one multiple.
        let (first, last) = grid_line_indices(-1.5, -0.5, 2.0);
        assert!(
            last < first,
            "expected an empty range, got {first}..={last}"
        );
        assert_eq!(grid_line_indices(-2.0, -2.0, 1.0), (-2, -2));
        assert_eq!(grid_line_indices(1.0, 1.0, 1.0), (1, 1));
    }

    #[test]
    fn pan_moves_the_target_perpendicular_to_the_view() {
        let mut camera = OrbitCamera::isometric();
        camera.half_span = 5.0; // a view volume 10 units tall
        let before = camera.target;

        camera.pan(10.0, 0.0, 600.0);

        // units_per_pixel = 10 / 600; at azim -45 the screen-right axis is (1, 1, 0)/sqrt(2)
        // and the target moves against the drag (`simulator.py:1082-1085`).
        let units_per_pixel = 10.0 / 600.0;
        let step = 10.0 * std::f64::consts::FRAC_1_SQRT_2 * units_per_pixel;
        close(camera.target[0], before[0] - step, 1e-12, "pan x");
        close(camera.target[1], before[1] - step, 1e-12, "pan y");
        close(camera.target[2], before[2], 1e-12, "pan z");

        let shift = subtract(camera.target, before);
        close(length(shift), 10.0 * units_per_pixel, 1e-12, "pan distance");
        close(
            dot(shift, camera.view_direction()),
            0.0,
            1e-12,
            "pan stays in the screen plane",
        );
    }

    #[test]
    fn pan_honors_the_screen_up_basis() {
        let mut camera = OrbitCamera::isometric();
        camera.half_span = 5.0;
        let before = camera.target;

        camera.pan(0.0, 10.0, 600.0); // downward drag: the target follows -up

        let shift = subtract(camera.target, before);
        // At azim -45 the up axis is mirror-symmetric in x and y, so the same must hold of
        // the shift; a downward drag has to pull the target down in world z.
        close(
            shift[0],
            -shift[1],
            1e-12,
            "up axis symmetry about azim -45",
        );
        assert!(shift[2] < 0.0, "downward drag moved z by {}", shift[2]);
        close(
            dot(shift, camera.right()),
            0.0,
            1e-12,
            "leak into screen-right",
        );
        close(length(shift), 10.0 * (10.0 / 600.0), 1e-12, "pan distance");
    }

    #[test]
    fn fit_centers_and_frames_the_bounds() {
        let mut camera = OrbitCamera::isometric();
        camera.fit(box_bounds([-10.0, -10.0, 0.0], [10.0, 10.0, 30.0]));

        assert_eq!(camera.target, [0.0, 0.0, 15.0]);
        // Largest extent 30, radius 15, then `simulator.py:916`'s 1.45 margin.
        close(camera.half_span, 15.0 * 1.45, 1e-9, "fitted half-span");
        // Refitting the bounds must not disturb the orbit.
        assert_eq!(camera.elev_deg, OrbitCamera::DEFAULT_ELEV_DEG);
        assert_eq!(camera.azim_deg, OrbitCamera::DEFAULT_AZIM_DEG);

        // The largest extent is not always the z one.
        camera.fit(box_bounds([-1.0, -1.0, -1.0], [9.0, 1.0, 1.0]));
        assert_eq!(camera.target, [4.0, 0.0, 0.0]);
        close(camera.half_span, 5.0 * 1.45, 1e-9, "widest axis is x");
    }

    #[test]
    fn fit_radius_drives_both_the_span_and_the_grid() {
        let bounds = box_bounds([-10.0, -10.0, 0.0], [10.0, 10.0, 30.0]);
        close(fit_radius(bounds), 15.0, 1e-9, "half the largest extent");

        let mut camera = OrbitCamera::isometric();
        camera.fit(bounds);
        close(
            camera.half_span,
            fit_radius(bounds) * 1.45,
            1e-12,
            "span follows the radius",
        );

        // Nothing to measure: the floor keeps the span and the grid both finite.
        let nothing = box_bounds([f32::INFINITY; 3], [f32::NEG_INFINITY; 3]);
        close(
            fit_radius(nothing),
            0.5,
            1e-9,
            "radius floor for empty bounds",
        );
        assert!(grid_spacing(fit_radius(nothing)).is_finite());
    }

    #[test]
    fn fit_applies_the_radius_floor_to_a_point_like_box() {
        let mut camera = OrbitCamera::isometric();
        camera.fit(box_bounds([4.0, -2.0, 7.0], [4.0, -2.0, 7.0]));

        assert_eq!(camera.target, [4.0, -2.0, 7.0]);
        // Zero extent, so the radius floor of 0.5 (`simulator.py:915`) decides the span.
        close(camera.half_span, 0.5 * 1.45, 1e-9, "floored half-span");
    }

    #[test]
    fn fit_keeps_a_sane_framing_for_empty_bounds() {
        let mut camera = OrbitCamera::isometric();
        camera.target = [3.0, 4.0, 5.0];
        camera.half_span = 1.0;
        // The usual empty box: min above max on every axis.
        camera.fit(box_bounds([f32::INFINITY; 3], [f32::NEG_INFINITY; 3]));

        assert!(
            camera.target.iter().all(|axis| axis.is_finite()),
            "{camera:?}"
        );
        assert!(
            camera.half_span.is_finite() && camera.half_span >= 0.025,
            "{camera:?}"
        );
        assert_eq!(camera, OrbitCamera::isometric());
    }

    #[test]
    fn eye_offsets_the_target_along_the_view_direction() {
        let mut camera = OrbitCamera::isometric();
        camera.target = [1.0, 2.0, 3.0];

        let distance = camera.half_span;
        let eye = camera.eye(distance);
        let offset = subtract(eye, camera.target);
        for (actual, expected) in offset.into_iter().zip(camera.view_direction()) {
            close(actual, expected * distance, 1e-12, "eye offset");
        }
        close(length(offset), distance, 1e-12, "eye distance");
    }

    #[test]
    fn screen_basis_is_orthonormal_and_the_world_is_z_up() {
        let views = [
            (35.264, -45.0),
            (0.0, 0.0),
            (85.0, 200.0),
            (-85.0, -120.0),
            (12.5, 47.5),
        ];
        for (elev_deg, azim_deg) in views {
            let camera = OrbitCamera {
                target: [1.0, -2.0, 3.0],
                elev_deg,
                azim_deg,
                half_span: 2.0,
            };
            let right = camera.right();
            let up = camera.up();
            let direction = camera.view_direction();
            let what = format!("elev {elev_deg}, azim {azim_deg}");
            close(length(right), 1.0, 1e-12, &what);
            close(length(up), 1.0, 1e-12, &what);
            close(length(direction), 1.0, 1e-12, &what);
            close(dot(right, up), 0.0, 1e-12, &what);
            close(dot(right, direction), 0.0, 1e-12, &what);
            close(dot(up, direction), 0.0, 1e-12, &what);
            // The cross product has to point at the eye, not away from it.
            for (facing, axis) in cross(right, up).into_iter().zip(direction) {
                close(facing, axis, 1e-12, &what);
            }
            // Z-up: the screen's up axis stays above the horizon at every legal elevation,
            // which is what stops the view from ever rendering upside down.
            assert!(up[2] > 0.0, "{what}");
        }
    }
}
