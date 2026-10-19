//! The polynomial layer: a profile is a start state plus fixed-capacity cubic segments.
//!
//! Everything here is generic over [`robot_kinematics::Field`]. The same code therefore
//! runs over `f64` in production and over `robot_golden::Ratio` in the exact tests; the
//! arithmetic uses `one()/from_f64(6.0)` rather than `from_f64(1.0/6.0)` so the `1/6` is
//! exact over the rationals.
//!
//! Evaluation follows the later-segment rule at a boundary and clamps outside
//! `[0, total_time]`. Zero-duration segments are retained in the stored list (they make
//! the Lean, Rust and golden lists structurally identical) and are skipped by `eval`.

use crate::error::{PlanError, ProfileError};
use robot_kinematics::Field;

/// The fixed capacity proved in Lean: stop (4) + rest-to-rest middle (7) + start (4).
pub const MAX_PHASES: usize = 15;

/// A joint state: position, velocity, acceleration.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct State<S = f64> {
    pub q: S,
    pub v: S,
    pub a: S,
}

impl<S> State<S> {
    pub const fn new(q: S, v: S, a: S) -> Self {
        Self { q, v, a }
    }
}

impl<S: Field> State<S> {
    /// Advance by constant `jerk` for `duration`.
    pub fn advance(self, jerk: S, duration: S) -> Self {
        let two = S::from_f64(2.0);
        let six = S::from_f64(6.0);
        let d2 = duration * duration;
        let d3 = d2 * duration;
        Self {
            q: self.q + self.v * duration + self.a * d2 / two + jerk * d3 / six,
            v: self.v + self.a * duration + jerk * d2 / two,
            a: self.a + jerk * duration,
        }
    }

    pub fn is_finite(self) -> bool {
        self.q.is_finite() && self.v.is_finite() && self.a.is_finite()
    }
}

/// Symmetric kinematic limits.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Limits<S = f64> {
    vmax: S,
    amax: S,
    jmax: S,
}

impl<S: Field> Limits<S> {
    pub fn new(vmax: S, amax: S, jmax: S) -> Result<Self, PlanError> {
        let zero = S::zero();
        if !vmax.is_finite() || !amax.is_finite() || !jmax.is_finite() {
            return Err(PlanError::NonPositiveLimit);
        }
        if vmax <= zero || amax <= zero || jmax <= zero {
            return Err(PlanError::NonPositiveLimit);
        }
        Ok(Self { vmax, amax, jmax })
    }

    pub fn vmax(self) -> S {
        self.vmax
    }

    pub fn amax(self) -> S {
        self.amax
    }

    pub fn jmax(self) -> S {
        self.jmax
    }
}

/// One constant-jerk segment.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Segment<S = f64> {
    pub dur: S,
    pub jerk: S,
}

impl<S: Field> Segment<S> {
    fn empty() -> Self {
        Self {
            dur: S::zero(),
            jerk: S::zero(),
        }
    }
}

/// Which planner shape produced a profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanKind {
    ZeroMotion,
    Conservative,
    Cruise,
    PeakNoCruise,
    Triangular,
    General,
}

/// A piecewise-cubic trajectory.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Profile<S = f64> {
    start: State<S>,
    end: State<S>,
    segments: [Segment<S>; MAX_PHASES],
    starts: [State<S>; MAX_PHASES],
    len: usize,
    total_time: S,
    kind: PlanKind,
}

impl<S: Field> Profile<S> {
    /// The empty profile at `start`.
    pub fn constant(start: State<S>) -> Self {
        Self::constant_with_kind(start, PlanKind::ZeroMotion)
    }

    fn constant_with_kind(start: State<S>, kind: PlanKind) -> Self {
        let state = State::new(S::zero(), S::zero(), S::zero());
        Self {
            start,
            end: start,
            segments: [Segment::empty(); MAX_PHASES],
            starts: [state; MAX_PHASES],
            len: 0,
            total_time: S::zero(),
            kind,
        }
    }

    /// Build from a start state and a slice of segments; the phase starts are derived.
    pub fn from_parts(start: State<S>, segments: &[Segment<S>]) -> Result<Self, ProfileError> {
        Self::from_parts_with_kind(start, segments, PlanKind::General)
    }

    pub fn from_parts_with_kind(
        start: State<S>,
        segments: &[Segment<S>],
        kind: PlanKind,
    ) -> Result<Self, ProfileError> {
        if !start.is_finite() {
            return Err(ProfileError::NonFinite);
        }
        if segments.len() > MAX_PHASES {
            return Err(ProfileError::TooManySegments);
        }
        let mut p = Self::constant_with_kind(start, kind);
        for &seg in segments {
            p.try_push(seg)?;
        }
        p.kind = kind;
        Ok(p)
    }

    /// Append one segment, validating it and the capacity.
    pub fn try_push(&mut self, seg: Segment<S>) -> Result<(), ProfileError> {
        if self.len == MAX_PHASES {
            return Err(ProfileError::TooManySegments);
        }
        if !seg.dur.is_finite() || !seg.jerk.is_finite() {
            return Err(ProfileError::NonFinite);
        }
        if seg.dur < S::zero() {
            return Err(ProfileError::NegativeDuration);
        }
        self.push_unchecked(seg);
        Ok(())
    }

    /// Caller has already checked capacity, finiteness and non-negative duration.
    fn push_unchecked(&mut self, seg: Segment<S>) {
        let entry = self.end;
        self.starts[self.len] = entry;
        self.segments[self.len] = seg;
        self.len += 1;
        self.total_time = self.total_time + seg.dur;
        self.end = entry.advance(seg.jerk, seg.dur);
    }

    pub fn start(&self) -> State<S> {
        self.start
    }

    pub fn end(&self) -> State<S> {
        self.end
    }

    pub fn total_time(&self) -> S {
        self.total_time
    }

    pub fn kind(&self) -> PlanKind {
        self.kind
    }

    pub fn segments(&self) -> &[Segment<S>] {
        &self.segments[..self.len]
    }

    pub fn phase_start(&self, index: usize) -> Option<State<S>> {
        if index < self.len {
            Some(self.starts[index])
        } else {
            None
        }
    }

    /// State at `t`, clamped to `[0, total_time]`; later segment at a boundary.
    pub fn eval(&self, t: S) -> State<S> {
        if t <= S::zero() {
            return self.start;
        }
        if t >= self.total_time {
            return self.end;
        }
        let mut acc = S::zero();
        for i in 0..self.len {
            let next = acc + self.segments[i].dur;
            if t < next {
                return phase_at(self.starts[i], self.segments[i], t - acc);
            }
            acc = next;
        }
        self.end
    }

    /// Reference at scaled progress `s`, with clock rate and rate derivative.
    ///
    /// `v = p.v(s) rate`, `a = p.a(s) rate^2 + p.v(s) rate_dot`. The supervisor uses
    /// `rate_dot = 0`; the general form is the `comp_bounds` composition.
    pub fn eval_scaled(&self, s: S, rate: S, rate_dot: S) -> State<S> {
        let st = self.eval(s);
        State {
            q: st.q,
            v: st.v * rate,
            a: st.a * rate * rate + st.v * rate_dot,
        }
    }

    /// Affine time stretch `q(t) -> q(t / factor)`. Requires `factor >= 1`.
    pub fn stretch(&self, factor: S) -> Result<Self, ProfileError> {
        if !factor.is_finite() || factor < S::one() {
            return Err(ProfileError::InvalidStretch);
        }
        let f2 = factor * factor;
        let f3 = f2 * factor;
        let start = State {
            q: self.start.q,
            v: self.start.v / factor,
            a: self.start.a / f2,
        };
        let mut p = Self::constant_with_kind(start, self.kind);
        for i in 0..self.len {
            let seg = self.segments[i];
            p.try_push(Segment {
                dur: seg.dur * factor,
                jerk: seg.jerk / f3,
            })?;
        }
        Ok(p)
    }

    /// Shift the position coordinate by `dq`.
    pub fn translate(&self, dq: S) -> Self {
        let start = State {
            q: self.start.q + dq,
            ..self.start
        };
        let mut p = Self::constant_with_kind(start, self.kind);
        for i in 0..self.len {
            p.push_unchecked(self.segments[i]);
        }
        p
    }

    /// Negate velocity, acceleration and jerk (mirror about the start position).
    pub fn mirror(&self) -> Self {
        let start = State {
            q: self.start.q,
            v: -self.start.v,
            a: -self.start.a,
        };
        let mut p = Self::constant_with_kind(start, self.kind);
        for i in 0..self.len {
            let seg = self.segments[i];
            p.push_unchecked(Segment {
                dur: seg.dur,
                jerk: -seg.jerk,
            });
        }
        p
    }

    /// Concatenate; `next.start` must equal `self.end`.
    pub fn append(&self, next: &Profile<S>) -> Result<Self, ProfileError> {
        if next.start != self.end {
            return Err(ProfileError::JunctionMismatch);
        }
        if self.len + next.len > MAX_PHASES {
            return Err(ProfileError::TooManySegments);
        }
        let mut p = Self::constant_with_kind(self.start, PlanKind::General);
        for i in 0..self.len {
            p.push_unchecked(self.segments[i]);
        }
        for i in 0..next.len {
            p.push_unchecked(next.segments[i]);
        }
        Ok(p)
    }

    /// Time reversal: `q(t) -> q(T - t)`; starts at the old end with velocity negated.
    pub fn reverse(&self) -> Self {
        let start = State {
            q: self.end.q,
            v: -self.end.v,
            a: self.end.a,
        };
        let mut p = Self::constant_with_kind(start, PlanKind::General);
        for i in 0..self.len {
            let seg = self.segments[self.len - 1 - i];
            p.push_unchecked(Segment {
                dur: seg.dur,
                jerk: -seg.jerk,
            });
        }
        p
    }
}

fn phase_at<S: Field>(entry: State<S>, seg: Segment<S>, t: S) -> State<S> {
    let two = S::from_f64(2.0);
    let six = S::from_f64(6.0);
    let t2 = t * t;
    let t3 = t2 * t;
    State {
        q: entry.q + entry.v * t + entry.a * t2 / two + seg.jerk * t3 / six,
        v: entry.v + entry.a * t + seg.jerk * t2 / two,
        a: entry.a + seg.jerk * t,
    }
}

/// A group of joints evaluated on one common time axis.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct JointProfile<const N: usize, S = f64> {
    joints: [Profile<S>; N],
    total_time: S,
}

impl<const N: usize, S: Field> JointProfile<N, S> {
    /// Build from profiles that share `total_time` (the synchronizer guarantees this).
    pub fn new(joints: [Profile<S>; N], total_time: S) -> Self {
        Self { joints, total_time }
    }

    pub fn joints(&self) -> &[Profile<S>; N] {
        &self.joints
    }

    pub fn joint(&self, index: usize) -> Option<&Profile<S>> {
        self.joints.get(index)
    }

    pub fn total_time(&self) -> S {
        self.total_time
    }

    pub fn eval(&self, t: S) -> [State<S>; N] {
        core::array::from_fn(|i| self.joints[i].eval(t))
    }

    pub fn eval_scaled(&self, s: S, rate: S, rate_dot: S) -> [State<S>; N] {
        core::array::from_fn(|i| self.joints[i].eval_scaled(s, rate, rate_dot))
    }
}
