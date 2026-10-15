//! The inverse solver's candidate configuration, and the buffer it is returned in.

use crate::scalar::{Field, Scalar};

/// The most candidates the closed form can produce: the `2 × 2 × 2` branches of
/// `mathematics.md` §2, bounded by `length_solutions_le_eight` in Lean.
///
/// This is a proved bound, not an estimate, which is what lets the solver return a
/// fixed-capacity buffer and keep the control path allocation-free.
pub const MAX_SOLUTIONS: usize = 8;

/// One configuration the solver offers for a target pose. Lean's
/// `InverseKinematics.Solution`.
///
/// The angles are total DH angles, as everywhere in the Lean development: the joint's
/// static theta offset is already folded in. `kinematics.py` reports
/// `wrap(total - offset)` instead; that conversion belongs at the API boundary, in
/// [`crate::units`], not here.
///
/// The wrist branch is deliberately *not* recorded, because Lean's `Solution` does not
/// record it either: it is a property of how the candidate was built, not of the
/// candidate, and the pose it reproduces is the same either way.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Solution<S> {
    /// The six total joint angles, `Fin 6 → ℝ` in Lean.
    pub angles: [S; 6],
    /// `+1` or `-1`, Lean's `Solution.shoulder`: which of the two planes through the
    /// base axis the arm is solved in.
    pub shoulder: i8,
    /// `+1` or `-1`, Lean's `Solution.elbow`: which side the elbow bends to.
    pub elbow: i8,
}

impl<S: Field> Solution<S> {
    /// The placeholder a buffer slot is initialised with. Never observable: the set's
    /// length is what a caller reads.
    #[inline]
    fn zeroed() -> Self {
        Self {
            angles: [S::zero(); 6],
            shoulder: 1,
            elbow: 1,
        }
    }

    /// The `i`-th total angle.
    #[inline]
    pub fn angle(&self, joint: usize) -> S {
        self.angles[joint]
    }

    /// Whether every angle is finite.
    #[inline]
    pub fn is_finite(&self) -> bool {
        self.angles.iter().all(|angle| angle.is_finite())
    }
}

/// The operations that need a transcendental, and therefore cannot be evaluated over an
/// arbitrary field.
impl<S: Scalar> Solution<S> {
    /// The squared wrapped distance to another configuration, in the norm
    /// `_pose_jog` minimises to keep branch continuity between successive jogs.
    ///
    /// Each difference is wrapped through `atan2 (sin, cos)`, the same reduction
    /// `Atan2.wrap` performs, so a joint sitting at `π` and one at `-π` count as zero
    /// apart rather than a full turn.
    pub fn wrapped_distance_sq(&self, other: &Self) -> S {
        let mut total = S::zero();
        for joint in 0..6 {
            let delta = crate::units::wrap_angle(self.angles[joint] - other.angles[joint]);
            total = total + delta * delta;
        }
        total
    }
}

/// A fixed-capacity list of candidates, sized by [`MAX_SOLUTIONS`].
///
/// Overflow sets a flag instead of panicking or growing: the bound is a theorem, so an
/// overflow means the Rust has diverged from the specification, and a control loop must
/// not be brought down by discovering that at runtime. Check [`SolutionSet::overflowed`]
/// in tests; production can ignore it.
#[derive(Copy, Clone, Debug)]
pub struct SolutionSet<S> {
    entries: [Solution<S>; MAX_SOLUTIONS],
    len: usize,
    overflowed: bool,
}

impl<S: Field> SolutionSet<S> {
    #[inline]
    pub fn new() -> Self {
        Self {
            entries: [Solution::zeroed(); MAX_SOLUTIONS],
            len: 0,
            overflowed: false,
        }
    }

    /// Append a candidate. Beyond [`MAX_SOLUTIONS`] the candidate is dropped and
    /// [`SolutionSet::overflowed`] is set.
    #[inline]
    pub fn push(&mut self, solution: Solution<S>) {
        if self.len < MAX_SOLUTIONS {
            self.entries[self.len] = solution;
            self.len += 1;
        } else {
            self.overflowed = true;
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
        self.overflowed = false;
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether more than [`MAX_SOLUTIONS`] candidates were offered. Always false for a
    /// solver that agrees with `length_solutions_le_eight`.
    #[inline]
    pub fn overflowed(&self) -> bool {
        self.overflowed
    }

    #[inline]
    pub fn as_slice(&self) -> &[Solution<S>] {
        &self.entries[..self.len]
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<&Solution<S>> {
        self.as_slice().get(index)
    }

    pub fn iter(&self) -> core::slice::Iter<'_, Solution<S>> {
        self.as_slice().iter()
    }

}

impl<S: Scalar> SolutionSet<S> {
    /// The candidate closest to `reference` in wrapped joint space, which is how the
    /// application keeps branch continuity across successive jogs.
    pub fn nearest_to(&self, reference: &Solution<S>) -> Option<&Solution<S>> {
        self.iter().reduce(|best, candidate| {
            if candidate.wrapped_distance_sq(reference) < best.wrapped_distance_sq(reference) {
                candidate
            } else {
                best
            }
        })
    }
}

impl<S: Field> Default for SolutionSet<S> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, S: Field> IntoIterator for &'a SolutionSet<S> {
    type Item = &'a Solution<S>;
    type IntoIter = core::slice::Iter<'a, Solution<S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solution(angle: f64) -> Solution<f64> {
        Solution {
            angles: [angle; 6],
            shoulder: 1,
            elbow: 1,
        }
    }

    #[test]
    fn a_ninth_candidate_sets_the_overflow_flag_rather_than_panicking() {
        let mut set = SolutionSet::new();
        for i in 0..MAX_SOLUTIONS {
            set.push(solution(i as f64));
        }
        assert_eq!(set.len(), MAX_SOLUTIONS);
        assert!(!set.overflowed());

        set.push(solution(99.0));
        assert_eq!(set.len(), MAX_SOLUTIONS);
        assert!(set.overflowed());
    }

    #[test]
    fn wrapped_distance_treats_a_full_turn_as_zero() {
        let near_pi = solution(core::f64::consts::PI - 1e-9);
        let near_minus_pi = solution(-core::f64::consts::PI + 1e-9);
        assert!(near_pi.wrapped_distance_sq(&near_minus_pi) < 1e-15);
    }

    #[test]
    fn nearest_selects_the_closest_configuration() {
        let mut set = SolutionSet::new();
        set.push(solution(0.0));
        set.push(solution(1.0));
        set.push(solution(3.0));
        let reference = solution(1.1);
        let nearest = set.nearest_to(&reference).expect("non-empty");
        assert_eq!(nearest.angles[0], 1.0);
    }
}
