module
-- These are `public import`s because the declarations below are exported
-- (`@[expose] public section`): everything their types and bodies mention has to
-- be part of this module's public interface, or importers cannot use them.
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

open Complex

noncomputable section

@[expose] public section

/-!
# `atan2`, `hypot` and the angle algebra of the planar solve

`kinematics.py`'s closed-form solver reads its planar target through `math.atan2` and
`math.hypot` - thirteen `atan2` call sites - and Mathlib has no two-argument arctangent over
the reals. This file supplies it, with the C and Python convention exactly, together with
`hypot` and the rotation identities the planar solve is built out of.
`InverseKinematics.lean` states that solve against these names.

`atan2` is `Complex.arg` of the point `(x, y)`. That is not a substitute convention but the
same one: `Complex.arg` *is* `math.atan2` on the plane. Its range is `(-π, π]` and
`arg 0 = 0`, which is what `math.atan2` documents, boundary included (`atan2(+0, -0) = π` is
`-π < arg`, not `≤`). Defining it this way puts the whole real library a change of
coordinates away from Mathlib's complex one, and in particular gives
`Complex.arg_mul_coe_angle` - `atan2`-angles add when the points multiply - which is what
the two rotation lemmas at the end are proved from.

The convention, spelled out because the sign of an angle is easy to lose:

* `atan2 y x` is the angle of the point with coordinates `(x, y)` - the cosine component
  first, as in `math.atan2(y, x)` and in `Complex.mk`'s field order;
* it lies in `(-π, π]`, with `atan2 0 0 = 0`, and `atan2 y 0 = ±π/2` for `y ≠ 0`;
* `atan2` is *total*. Only the lemmas that genuinely need a direction carry a
  non-vanishing hypothesis `(x, y) ≠ (0, 0)`, and the two planar lemmas carry none: there
  `u = v = 0` forces `q = h = 0`, and both sides of the identity are `0`.

`hypot` is `Real.sqrt (x ^ 2 + y ^ 2)`, which is the value `math.hypot` computes; its scaled
implementation only avoids intermediate overflow.

`wrap` is `kinematics.py`'s `_wrap_angle`. It is here to record what the development drops:
the solver returns joint angles normalised into `(-π, π]`, while every statement about it is
modulo a full turn - an equality in `Real.Angle` - so the normalisation itself never has to
appear in a proof. `wrap_coe_angle` is that observation.

`nearestRepresentative` and `turnIndex` put the dropped winding back, which is what a joint
jog needs: the angle a solver returns is defined modulo a full turn, the joint it is about to
be sent to is not, and the difference between the two is a whole turn of motion. They are
`crates/robot-kinematics`'s `units::nearest_representative` and `units::turn_index`, and
`Solution::representative_near` lifts the first from one angle to a whole configuration.
-/

namespace RealAtan2

/-! ## The three functions -/

/-- `math.hypot`: the Euclidean norm of the pair. -/
def hypot (x y : ℝ) : ℝ := Real.sqrt (x ^ 2 + y ^ 2)

/-- Two-argument arctangent, `math.atan2`'s convention exactly: the angle of the
point `(x, y)`, in `(-π, π]`, with `atan2 0 0 = 0`. -/
def atan2 (y x : ℝ) : ℝ := Complex.arg (⟨x, y⟩ : ℂ)

/-- `kinematics.py`'s `_wrap_angle`: the representative of `θ` in `(-π, π]`. The
solver never normalises (every statement is modulo a full turn); this exists so
the module docstring can say what was dropped. -/
def wrap (θ : ℝ) : ℝ := atan2 (Real.sin θ) (Real.cos θ)

/-! ## `hypot`

The name the solver uses for the Euclidean length, and the bridge to the norm `Complex.arg`
is stated with. -/

/-- `math.hypot` is a square root, hence nonnegative; every division by it below is
therefore legitimate. -/
theorem hypot_nonneg (x y : ℝ) : 0 ≤ hypot x y := Real.sqrt_nonneg _

/-- Squaring `hypot` recovers the Pythagorean sum - the radicand is a sum of squares, so the
square root cancels - which is how a `hypot`-equality is turned into an algebraic one. -/
theorem hypot_sq (x y : ℝ) : hypot x y ^ 2 = x ^ 2 + y ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))

/-- `hypot` depends on the pair only up to sign, so `atan2`'s sign flips can be tracked
without touching the length. -/
theorem hypot_neg (x y : ℝ) : hypot (-x) (-y) = hypot x y := by
  rw [hypot, hypot, show (-x) ^ 2 + (-y) ^ 2 = x ^ 2 + y ^ 2 by ring]

/-- The Euclidean length of a pair is the norm of the corresponding complex number: this is
what lets `atan2`'s theorems be the complex ones read through `Complex.mk`. Stated with
`Complex.mk` rather than `Complex.ofReal` because `atan2`'s own arguments are the two
coordinates. -/
theorem norm_mk (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ = hypot x y := by
  rw [Complex.norm_def, Complex.normSq_mk, hypot,
    show x * x + y * y = x ^ 2 + y ^ 2 by ring]

/-- Scaling a `(cos θ, sin θ)` pair scales its length by `|c|`: the factor squares out of the
sum of squares, and `cos² + sin²` leaves `c²`, whose square root is `|c|`. The absolute value
is not a technicality - a length cannot remember the sign of the factor - and it is what makes
the solver's radial distance, a `hypot` of a link vector multiplied by `(cos θ, sin θ)`,
collapse to the length of that vector. -/
theorem hypot_mul_cos_sin (c θ : ℝ) :
    hypot (c * Real.cos θ) (c * Real.sin θ) = |c| := by
  rw [hypot, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one,
    Real.sqrt_sq_eq_abs]

/-! ## Reading `atan2` off `Complex.arg` -/

/-- The non-vanishing hypotheses below are all written on the *pair* `(x, y)`, because that
is how `atan2` is called, while the `Complex.arg` lemmas behind them are stated for a
nonzero complex number. This is the translation: a pair is the origin exactly when the
point it names is `0`. -/
theorem mk_ne_zero {x y : ℝ} (h : (x, y) ≠ (0, 0)) : (⟨x, y⟩ : ℂ) ≠ 0 := by
  rintro h0
  exact h (Prod.ext (by simpa using congrArg Complex.re h0)
    (by simpa using congrArg Complex.im h0))

/-- The sine of the angle of `(x, y)`: the `y` coordinate divided by the length. Total -
at the origin both sides are `0` - because `Complex.sin_arg` is. -/
theorem sin_atan2 (y x : ℝ) : Real.sin (atan2 y x) = y / hypot x y := by
  simp only [atan2, Complex.sin_arg, norm_mk]

/-- The cosine of the angle of `(x, y)`: the `x` coordinate divided by the length. Unlike
the sine this needs `(x, y) ≠ (0, 0)`, since `0 / 0 = 0` would report the wrong cosine at
the origin - `Complex.cos_arg` carries the same hypothesis. -/
theorem cos_atan2 {y x : ℝ} (h : (x, y) ≠ (0, 0)) : Real.cos (atan2 y x) = x / hypot x y := by
  simp only [atan2, Complex.cos_arg (mk_ne_zero h), norm_mk]

/-- The origin has no direction, so `math.atan2` picks one, and so does `Complex.arg`:
the angle of the origin is `0`. This is what makes the two planar lemmas below total. -/
theorem atan2_zero : atan2 0 0 = 0 := by
  rw [atan2, show (⟨(0 : ℝ), (0 : ℝ)⟩ : ℂ) = 0 from rfl, Complex.arg_zero]

/-! ## The range, and the round trip through it -/

/-- The angle is strictly above `-π`: the negative half-turn is `atan2`'s excluded end, so
the point `(-1, 0)` reads as `π` and not as `-π`. -/
theorem neg_pi_lt_atan2 (y x : ℝ) : -Real.pi < atan2 y x := by
  rw [atan2]
  exact Complex.neg_pi_lt_arg _

/-- The angle is at most `π`: the positive half-turn is included, which is the other half
of `math.atan2`'s `(-π, π]`. -/
theorem atan2_le_pi (y x : ℝ) : atan2 y x ≤ Real.pi := by
  rw [atan2]
  exact Complex.arg_le_pi _

/-- The two range facts together, in the form a hypothesis wants them: the angle of any
point is in `(-π, π]`. -/
theorem atan2_mem_Ioc (y x : ℝ) : atan2 y x ∈ Set.Ioc (-Real.pi) Real.pi := by
  rw [atan2]
  exact Complex.arg_mem_Ioc _

/-- The round trip: the point at angle `θ` has angle `θ`, for the angles `atan2` can
return. Together with `atan2_mem_Ioc` this says `atan2`'s range is exactly `(-π, π]` and
that `(sin, cos)` inverts it there - the uniqueness statement an angle solving needs. -/
theorem atan2_eq_of_mem_Ioc {θ : ℝ} (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    atan2 (Real.sin θ) (Real.cos θ) = θ := by
  rw [atan2, Complex.mk_eq_add_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I hθ

/-! ## The unit circle, in the spelling `atan2` takes -/

/-- The point of the unit circle at angle `θ` has angle `θ`, read as a `Real.Angle` - the
modulo-a-full-turn home of every angle statement in the solver. This is the bridge between
`atan2`'s `(cos θ, sin θ)` spelling and `Real.Angle`'s `cos`/`sin`, which are the real ones
by definition; `Complex.arg_cos_add_sin_mul_I_coe_angle` is stated for an `Angle` argument
and this lemma feeds it a real one. -/
theorem arg_cos_sin_mk_coe_angle (θ : ℝ) :
    (Complex.arg (⟨Real.cos θ, Real.sin θ⟩ : ℂ) : Real.Angle) = (θ : Real.Angle) := by
  rw [Complex.mk_eq_add_mul_I, ← Real.Angle.cos_coe θ, ← Real.Angle.sin_coe θ]
  exact Complex.arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle)

/-- The unit-circle point at angle `θ` has norm `1`. In particular it is a nonzero complex
number, which is what lets the argument of a product with it be split -
`Complex.arg_mul_coe_angle`'s non-vanishing hypothesis. -/
theorem norm_cos_sin_mk (θ : ℝ) : ‖(⟨Real.cos θ, Real.sin θ⟩ : ℂ)‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_mk, ← sq, ← sq, Real.cos_sq_add_sin_sq, Real.sqrt_one]

/-! ## `wrap`

`kinematics.py`'s normalisation, and the proof that it is invisible to everything stated
over `Real.Angle`. -/

/-- The normalisation is a no-op modulo a full turn: `wrap θ` and `θ` are the same angle,
which is why no solver statement mentions `wrap`. -/
theorem wrap_coe_angle (θ : ℝ) : (wrap θ : Real.Angle) = (θ : Real.Angle) := by
  rw [wrap, atan2]
  exact arg_cos_sin_mk_coe_angle θ

/-- Consequently `wrap` does not move the cosine: a solver stated through `cos`/`sin` reads
the same value before and after normalisation. -/
theorem cos_wrap (θ : ℝ) : Real.cos (wrap θ) = Real.cos θ := by
  rw [← Real.Angle.cos_coe (wrap θ), wrap_coe_angle θ, Real.Angle.cos_coe θ]

/-- The sine half of `cos_wrap`. -/
theorem sin_wrap (θ : ℝ) : Real.sin (wrap θ) = Real.sin θ := by
  rw [← Real.Angle.sin_coe (wrap θ), wrap_coe_angle θ, Real.Angle.sin_coe θ]

/-! ## The nearest representative, and the turn index

`wrap` is a *canonical* form: it throws away the winding an angle carries. That is the right
thing for a solver result - defined modulo a full turn - and the wrong thing for the joint it
is about to be sent to. `simulator.py`'s `_jog_joint` accumulates
(`joint_angles[joint_index] += direction * step`), so a joint on the arm can sit several turns
from zero, and handing it the canonical representative costs it every turn it has wound: a J6
held at 400 degrees would spin the whole turn down to the solver's 40, which is a whole-turn
joint motion manufactured out of a jog of a fraction of a turn.

`nearestRepresentative` places the answer back beside the joint instead, moving it by at most
a half turn, and `turnIndex` names the turns the placement carries - the winding `wrap`
discarded. The two are `crates/robot-kinematics`'s `units::nearest_representative` and
`units::turn_index`. What a Cartesian jog rests on is the pair `nearestRepresentative_sub_le`
(among the representatives of a solved angle, the one placed is the one that moves the joint
least) and `nearestRepresentative_coe_angle` (the placement cannot change the arm), with
`turnIndex_spec` making the decomposition exact: an angle is so many whole turns plus its
representative, and nothing is left over. -/

/-- `wrap`'s image is exactly `(-π, π]`: `atan2_mem_Ioc` read through `wrap`'s definition, and
the range every comparison below is made against. -/
theorem wrap_mem_Ioc (θ : ℝ) : wrap θ ∈ Set.Ioc (-Real.pi) Real.pi := by
  rw [wrap]
  exact atan2_mem_Ioc _ _

/-- Every angle is its own representative plus a whole number of turns. `wrap_coe_angle` says
the two are the same `Real.Angle`; this is that fact over `ℝ`, where the difference of two
reals with the same angle is an integer multiple of `2π` and nothing else. The integer it
produces is what `turnIndex` names. -/
theorem exists_eq_wrap_add_int_mul_two_pi (θ : ℝ) : ∃ k : ℤ, θ = wrap θ + k * (2 * Real.pi) := by
  have h0 : ((θ - wrap θ : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub, wrap_coe_angle θ, sub_self]
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp h0
  rw [zsmul_eq_mul] at hk
  exact ⟨k, by rw [hk]; ring⟩

/-- How many whole turns `θ` carries: `(θ - wrap θ) / (2π)` rounded to an integer. The Lean
`units::turn_index` of `crates/robot-kinematics`.

The quotient is an integer by construction - `exists_eq_wrap_add_int_mul_two_pi` - so the
rounding step only ever sees an integer, and the tie rule, Rust's and this one's alike, is
never reached. Reading the count off the difference from what `wrap` returned, rather than off
`θ` alone, is what keeps the branch cut out of it: `θ ≡ π` is where a formula like
`⌊(θ + π)/(2π)⌋` mis-assigns a turn, because the positive half turn is already inside `wrap`'s
range `(-π, π]`, and subtracting the representative first resolves that boundary before the
division.

An index is a *representation*, not a constraint: nothing here limits how far a joint may
wind, it only names where on its winding the joint is, and a joint past a full turn is exactly
the case it exists for. -/
def turnIndex (θ : ℝ) : ℤ := round ((θ - wrap θ) / (2 * Real.pi))

/-- The decomposition `turnIndex` is named for: `θ` is that many whole turns past its own
representative. The index is not a label attached to the angle but a count: the two terms on
the left reconstitute `θ` exactly, over `ℝ` and with no tolerance, so the turns the rounding
recovers are exactly the turns the decomposition needs. -/
theorem turnIndex_spec (θ : ℝ) : (turnIndex θ : ℝ) * (2 * Real.pi) + wrap θ = θ := by
  obtain ⟨k, hk⟩ := exists_eq_wrap_add_int_mul_two_pi θ
  have hk' : (θ - wrap θ) / (2 * Real.pi) = (k : ℝ) := by
    rw [show θ - wrap θ = (k : ℝ) * (2 * Real.pi) by linarith [hk]]
    exact mul_div_cancel_right₀ _ (by positivity)
  rw [turnIndex, hk', round_intCast]
  simpa [add_comm] using hk.symm

/-- `turnIndex_spec` read back the other way: what `wrap` discards is exactly that many whole
turns, and the pair `(turnIndex θ, wrap θ)` is the whole-turns part and the residual of `θ`
with nothing left over. -/
theorem wrap_sub_turnIndex_mem (θ : ℝ) : wrap θ = θ - (turnIndex θ : ℝ) * (2 * Real.pi) := by
  linarith [turnIndex_spec θ]

/-- The representative of `a` nearest the reference `r`: `r + wrap (a - r)`, the
`units::nearest_representative` of `crates/robot-kinematics`.

`a` here is an angle a solver returned, so it is defined modulo a full turn; `r` is the joint
it is about to be sent to, which is not. Handing the joint the canonical representative
`wrap a` would move it by the whole winding it dropped; this places the answer where the joint
already is, a half turn or less away. `nearestRepresentative_sub` reads the implied motion off
the definition, `abs_nearestRepresentative_sub_le_pi` bounds it by the half turn,
`nearestRepresentative_sub_le` says no other representative does better, and
`nearestRepresentative_coe_angle` says the arm cannot tell which representative it was given.

The Rust names the same function with the arguments the other way round
(`nearest_representative (angle, reference)`), and `Solution::representative_near` applies it
joint by joint across a whole configuration. -/
def nearestRepresentative (r a : ℝ) : ℝ := r + wrap (a - r)

/-- Choosing a representative does not change the arm: the placed angle is the same
`Real.Angle` as the one it was placed from. A pose sees each joint angle only through its
cosine and sine (`fk_congr` in `Kinematics.lean`), and the two angles differ by a whole number
of turns, so the placement cannot change what the solver solved for - it decides where on the
winding to carry out a pose, not which pose that is. -/
theorem nearestRepresentative_coe_angle (r a : ℝ) :
    (nearestRepresentative r a : Real.Angle) = (a : Real.Angle) := by
  rw [nearestRepresentative, Real.Angle.coe_add, wrap_coe_angle (a - r), Real.Angle.coe_sub,
    add_sub_cancel]

/-- The motion a placement implies, which is the whole cost of choosing a representative:
exactly the wrapped difference between the solved angle and the joint's own. It is what the
placement is defined by, and what every bound below is a statement about. -/
theorem nearestRepresentative_sub (r a : ℝ) : nearestRepresentative r a - r = wrap (a - r) := by
  rw [nearestRepresentative]
  ring

/-- The placement never moves a joint further than a half turn: the motion is a `wrap`, so it
lies in `(-π, π]` whatever the reference and whatever the joint's winding. This is the bound
that makes a placement safe on a joint whose winding nobody tracked - no reference is far
enough from an angle for the move to become a whole turn. -/
theorem abs_nearestRepresentative_sub_le_pi (r a : ℝ) :
    |nearestRepresentative r a - r| ≤ Real.pi := by
  rw [nearestRepresentative_sub]
  exact abs_le.mpr ⟨(wrap_mem_Ioc (a - r)).1.le, (wrap_mem_Ioc (a - r)).2⟩

/-- Among the whole-turn translates of a real, the one in `(-π, π]` is the one of least
absolute value. Every translate differs from it by a whole number `n` of turns, and the bounds
of the range do the rest: a turn in either direction already reaches `π` in magnitude or past
it, and each further turn only adds. This is why `wrap` is the right reduction to measure
distances against a reference with, and it is what `nearestRepresentative_sub_le` runs on. -/
theorem abs_le_abs_add_int_mul_two_pi {w : ℝ} (hw : w ∈ Set.Ioc (-Real.pi) Real.pi) (n : ℤ) :
    |w| ≤ |w + n * (2 * Real.pi)| := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · -- A whole turn or more backwards: `w + n·2π` is past the negative half turn, so its
    -- distance from `0` is `-(w + n·2π)`, and `w ≤ π` together with `n·2π ≤ -2π` puts both
    -- `w` and `-w` below that.
    have hn1 : (n : ℝ) ≤ -1 := by
      exact_mod_cast (show n ≤ -1 by omega)
    have hc : (n : ℝ) * (2 * Real.pi) ≤ -2 * Real.pi := by
      calc (n : ℝ) * (2 * Real.pi) ≤ (-1 : ℝ) * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right hn1 (by linarith [Real.pi_pos])
        _ = -2 * Real.pi := by ring
    have hneg : w + (n : ℝ) * (2 * Real.pi) < 0 := by linarith [hw.2, hc, Real.pi_pos]
    rw [abs_of_neg hneg]
    exact abs_le.mpr ⟨by linarith [hc, Real.pi_pos], by linarith [hw.2, hc, Real.pi_pos]⟩
  · -- No turn at all: the two sides are the same number.
    subst hn
    simp
  · -- A whole turn or more forwards, the mirror of the first case: `w + n·2π` is past the
    -- positive half turn, and `w > -π` together with `n·2π ≥ 2π` puts both `w` and `-w` below
    -- it.
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    have hc : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
      calc 2 * Real.pi = (1 : ℝ) * (2 * Real.pi) := by ring
        _ ≤ (n : ℝ) * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right hn1 (by linarith [Real.pi_pos])
    have hpos : 0 < w + (n : ℝ) * (2 * Real.pi) := by linarith [hw.1, hc, Real.pi_pos]
    rw [abs_of_pos hpos]
    exact abs_le.mpr ⟨by linarith [hw.1, hc, Real.pi_pos], by linarith [hc, Real.pi_pos]⟩

/-- `wrap` is the representative of `θ` nearest the origin, in the form a caller can use:
`wrap θ` is at least as close to `0` as `θ` shifted by any whole number of turns. The shift is
`exists_eq_wrap_add_int_mul_two_pi`'s, after which `θ` has dropped out of the comparison and
what is left is `abs_le_abs_add_int_mul_two_pi`'s statement about `wrap`'s own range. -/
theorem abs_wrap_le_abs_add_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    |wrap θ| ≤ |θ + k * (2 * Real.pi)| := by
  obtain ⟨m, hm⟩ := exists_eq_wrap_add_int_mul_two_pi θ
  have h : θ + (k : ℝ) * (2 * Real.pi) = wrap θ + ((m + k : ℤ) : ℝ) * (2 * Real.pi) := by
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [h]
  exact abs_le_abs_add_int_mul_two_pi (wrap_mem_Ioc θ) (m + k)

/-- **Among the representatives of a solved angle, the one placed is the one that moves the
joint least.** The right-hand side is the distance from the joint's own angle `r` to the `k`-th
representative `a + k·2π` of the solved angle, so the statement is the placement's defining
property, and it holds for every integer `k` at once: the nearest representative is canonical,
not one convention among several that happen to agree on the common cases.

Over `ℝ` the comparison is exact and needs no tolerance. Both sides are `wrap`'s to decide:
the left is `|wrap (a - r)|` by `nearestRepresentative_sub`, and the right is
`|(a - r) + k·2π|`, which is `abs_wrap_le_abs_add_int_mul_two_pi` with `θ = a - r` - so the
whole turn `k` is spent before the comparison starts, and what is left is a statement about
one number's distance from zero against its own whole-turn translates. -/
theorem nearestRepresentative_sub_le (r a : ℝ) (k : ℤ) :
    |nearestRepresentative r a - r| ≤ |a + k * (2 * Real.pi) - r| := by
  rw [nearestRepresentative_sub,
    show a + (k : ℝ) * (2 * Real.pi) - r = (a - r) + (k : ℝ) * (2 * Real.pi) by ring]
  exact abs_wrap_le_abs_add_int_mul_two_pi (a - r) k

/-! ## Reflection: the second-order interaction of `atan2` with negation -/

/-- Negating both coordinates adds a half turn to the angle - the reflection a `±` branch
of the solver flips between. As an `Angle` statement, because the sum leaves `(-π, π]`; the
non-vanishing hypothesis is needed on both sides: at the origin `arg` has no direction and
the right-hand side would be `π`. -/
theorem atan2_neg_coe_angle {y x : ℝ} (h : (x, y) ≠ (0, 0)) :
    (atan2 (-y) (-x) : Real.Angle) = (atan2 y x : Real.Angle) + Real.pi := by
  rw [atan2, atan2, show (⟨-x, -y⟩ : ℂ) = -(⟨x, y⟩ : ℂ) from rfl,
    Complex.arg_neg_coe_angle (mk_ne_zero h)]

/-! ## The planar solve

The wrist centre's planar offset `(q, h)` is the link vector `(u, v)` turned by the joint
angle. Read backwards, that fixes the joint angle as `atan2 h q - atan2 v u`, and the two
lemmas below are the two components of the rotation it performs: from
`q² + h² = u² + v²` alone, `(u, v)` turned by that difference *is* `(q, h)`. This is what
`InverseKinematics.lean`'s closed form is checked against.
-/

/-- The rotation law both planar components come from, in complex form: when the two points
have the same length, `(u, v)` turned by `atan2 h q - atan2 v u` lands exactly on `(q, h)`.

The proof is `Complex.ext_norm_arg_iff`: the lengths agree because multiplying by a point of
the unit circle does not change the length and `hn` says the two points have the same one,
and the arguments agree because `Complex.arg_mul_coe_angle` turns the product's argument
into a sum, in which `atan2 v u` cancels. -/
theorem mul_cos_sin_sub_eq {q h u v : ℝ} (hn : q ^ 2 + h ^ 2 = u ^ 2 + v ^ 2) :
    (⟨u, v⟩ : ℂ) * (⟨Real.cos (atan2 h q - atan2 v u), Real.sin (atan2 h q - atan2 v u)⟩ : ℂ)
      = (⟨q, h⟩ : ℂ) := by
  set c : ℂ := ⟨Real.cos (atan2 h q - atan2 v u), Real.sin (atan2 h q - atan2 v u)⟩ with hc
  set w : ℂ := (⟨u, v⟩ : ℂ) * c with hw
  have hc_norm : ‖c‖ = 1 := by
    rw [hc]
    exact norm_cos_sin_mk _
  have hw_norm : ‖w‖ = ‖(⟨q, h⟩ : ℂ)‖ := by
    rw [hw, Complex.norm_mul, hc_norm, mul_one, norm_mk, norm_mk, hypot, hypot, hn]
  have hw_arg : Complex.arg w = Complex.arg (⟨q, h⟩ : ℂ) := by
    -- Read as angles: the product's argument is the sum of the factors' arguments, which
    -- `Complex.arg_mul_coe_angle` supplies only away from the origin, and at the origin
    -- both sides of the identity are `arg 0 = 0` anyway.
    rw [← Complex.arg_coe_angle_eq_iff]
    rcases eq_or_ne (u, v) (0, 0) with huv | huv
    · -- `(u, v)` is the origin, so `hn` forces `(q, h)` there too and both angles are `0`.
      have hu : u = 0 := by simpa using congrArg Prod.fst huv
      have hv : v = 0 := by simpa using congrArg Prod.snd huv
      have hn0 : q ^ 2 + h ^ 2 = 0 := by
        rw [hu, hv] at hn
        simpa using hn
      have hq : q = 0 := by
        have h2 : q ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg h, hn0]) (sq_nonneg q)
        simpa using h2
      have hh : h = 0 := by
        have h2 : h ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg q, hn0]) (sq_nonneg h)
        simpa using h2
      rw [hw, show (⟨u, v⟩ : ℂ) = 0 from by rw [hu, hv]; rfl,
        show (⟨q, h⟩ : ℂ) = 0 from by rw [hq, hh]; rfl, zero_mul, Complex.arg_zero]
    · -- Away from the origin the arguments add, and `atan2 h q - atan2 v u` cancels.
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hc_norm
        exact one_ne_zero hc_norm.symm
      rw [hw, Complex.arg_mul_coe_angle (mk_ne_zero huv) hc0, hc,
        arg_cos_sin_mk_coe_angle (atan2 h q - atan2 v u),
        show Complex.arg (⟨u, v⟩ : ℂ) = atan2 v u from rfl,
        show Complex.arg (⟨q, h⟩ : ℂ) = atan2 h q from rfl, ← Real.Angle.coe_add,
        show atan2 v u + (atan2 h q - atan2 v u) = atan2 h q by ring]
  rw [show w = (⟨q, h⟩ : ℂ) from by
    rw [Complex.ext_norm_arg_iff]
    exact ⟨hw_norm, hw_arg⟩]

/-- The `q` component of the rotation law: `(u, v)` turned by `atan2 h q - atan2 v u` has
first coordinate `q`. Total: at the origin the hypothesis forces `q = 0` and both sides
are `0`. -/
theorem cos_atan2_sub_mul {q h u v : ℝ} (hn : q ^ 2 + h ^ 2 = u ^ 2 + v ^ 2) :
    Real.cos (atan2 h q - atan2 v u) * u - Real.sin (atan2 h q - atan2 v u) * v = q := by
  have hre := congrArg Complex.re (mul_cos_sin_sub_eq hn)
  simp only [Complex.mul_re] at hre
  calc Real.cos (atan2 h q - atan2 v u) * u - Real.sin (atan2 h q - atan2 v u) * v
      = u * Real.cos (atan2 h q - atan2 v u) - v * Real.sin (atan2 h q - atan2 v u) := by
        ring
    _ = q := hre

/-- The `h` component of the rotation law: `(u, v)` turned by `atan2 h q - atan2 v u` has
second coordinate `h`. The same statement as `cos_atan2_sub_mul`, read on the imaginary
part. -/
theorem sin_atan2_sub_mul {q h u v : ℝ} (hn : q ^ 2 + h ^ 2 = u ^ 2 + v ^ 2) :
    Real.sin (atan2 h q - atan2 v u) * u + Real.cos (atan2 h q - atan2 v u) * v = h := by
  have him := congrArg Complex.im (mul_cos_sin_sub_eq hn)
  simp only [Complex.mul_im] at him
  calc Real.sin (atan2 h q - atan2 v u) * u + Real.cos (atan2 h q - atan2 v u) * v
      = u * Real.sin (atan2 h q - atan2 v u) + v * Real.cos (atan2 h q - atan2 v u) := by
        ring
    _ = h := him

/-- The rotation law at the level of angles, which is the form a completeness statement
wants: if `(q, h)` is `(u, v)` turned by `θ` in the coordinates, then the `atan2` of
`(q, h)` is `θ` plus the `atan2` of `(u, v)` - modulo a full turn, since one real angle
cannot carry the sign of `cos θ` and `sin θ` separately.

This is the two scalar laws read as a statement about the rotation itself: turning
`(u, v)` by `θ` reaches `(q, h)` by the two component hypotheses, and turning it by
`atan2 h q - atan2 v u` reaches the same point by `mul_cos_sin_sub_eq` - which is the one
place `hn` is needed. The two turns are therefore the same angle modulo a full turn, and
`atan2 v u` moves to the other side. -/
theorem atan2_rotate_coe_angle {q h u v θ : ℝ} (hu : (u, v) ≠ (0, 0))
    (hn : q ^ 2 + h ^ 2 = u ^ 2 + v ^ 2)
    (hc : q = u * Real.cos θ - v * Real.sin θ) (hs : h = u * Real.sin θ + v * Real.cos θ) :
    (atan2 h q : Real.Angle) = (θ : Real.Angle) + (atan2 v u : Real.Angle) := by
  have hrot : (⟨u, v⟩ : ℂ) * (⟨Real.cos θ, Real.sin θ⟩ : ℂ) = (⟨q, h⟩ : ℂ) := by
    apply Complex.ext
    · rw [Complex.mul_re, hc]
    · rw [Complex.mul_im, hs]
  have hcancel : (⟨Real.cos (atan2 h q - atan2 v u), Real.sin (atan2 h q - atan2 v u)⟩ : ℂ)
      = (⟨Real.cos θ, Real.sin θ⟩ : ℂ) :=
    mul_left_cancel₀ (mk_ne_zero hu) (by rw [mul_cos_sin_sub_eq hn, hrot])
  have hangle : ((atan2 h q - atan2 v u : ℝ) : Real.Angle) = (θ : Real.Angle) := by
    rw [← arg_cos_sin_mk_coe_angle (atan2 h q - atan2 v u), hcancel, arg_cos_sin_mk_coe_angle θ]
  rw [Real.Angle.coe_sub] at hangle
  rw [← hangle, sub_add_cancel]

/-! ## Scaling the pair, and the round trips that read an angle back

The closed-form solver never holds an angle it did not read off a pair of coordinates, and it
reads them through a link length: a positive factor has to leave the angle alone, a negative
one has to cost exactly a half turn, and a pair that really is `(cos θ, sin θ)` has to give `θ`
back. `Real.arccos` closes the same loop for the elbow, where the solver computes a cosine and
has to recover the angle it came from, sign included; the last two lemmas are that pair of
signs.
-/

/-- Multiplying both coordinates by a positive constant does not move the angle of the pair: a
positive factor is a stretch with no direction of its own, so as a complex factor it
contributes `arg c = 0` to the argument of the product. No non-vanishing hypothesis is needed -
unlike `atan2_neg_coe_angle` there is no reflection here whose direction the origin could fail
to have, and at the origin both sides are `atan2 0 0 = 0`. This is what lets the solver read an
angle off a pair that has been multiplied by a link length. -/
theorem atan2_pos_mul_coe_angle {y x c : ℝ} (hc : 0 < c) :
    (atan2 (c * y) (c * x) : Real.Angle) = (atan2 y x : Real.Angle) := by
  rcases eq_or_ne (x, y) (0, 0) with h0 | h0
  · -- At the origin both sides are `atan2 0 0 = 0`, so there is nothing to add a half turn to.
    have hx : x = 0 := by simpa using congrArg Prod.fst h0
    have hy : y = 0 := by simpa using congrArg Prod.snd h0
    rw [hx, hy, mul_zero]
  · -- The scaled pair is `(c : ℂ)` times the pair, and `arg` of a product is the sum of the
    -- factors' arguments, of which `c`'s is `0`.
    rw [atan2, atan2,
      show (⟨c * x, c * y⟩ : ℂ) = (c : ℂ) * (⟨x, y⟩ : ℂ) from by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im],
      Complex.arg_mul_coe_angle (Complex.ofReal_ne_zero.mpr (ne_of_gt hc)) (mk_ne_zero h0),
      Complex.arg_ofReal_of_nonneg hc.le]
    exact zero_add _

/-- Multiplying both coordinates by a negative constant is the positive stretch of `-c`
followed by the reflection through the origin, so the angle comes back with a half turn added.
The hypothesis on the pair is genuinely needed here, in a way its positive twin does not need
it: at the origin the right-hand side would be `π` while `atan2 0 0 = 0`, the reflection having
no direction to preserve. -/
theorem atan2_neg_mul_coe_angle {y x c : ℝ} (hc : c < 0) (h : (x, y) ≠ (0, 0)) :
    (atan2 (c * y) (c * x) : Real.Angle) = (atan2 y x : Real.Angle) + Real.pi := by
  have hc' : 0 < -c := neg_pos.mpr hc
  -- `c * y = -((-c) * y)` turns the negative scale into the positive one followed by
  -- `atan2_neg_coe_angle`, whose own hypothesis `((-c) * x, (-c) * y) ≠ (0, 0)` follows from
  -- `h` and `-c ≠ 0`.
  have hne : ((-c) * x, (-c) * y) ≠ (0, 0) := by
    intro h0
    refine h (Prod.ext ?_ ?_)
    · exact (mul_eq_zero.mp (by simpa using congrArg Prod.fst h0)).resolve_left (ne_of_gt hc')
    · exact (mul_eq_zero.mp (by simpa using congrArg Prod.snd h0)).resolve_left (ne_of_gt hc')
  rw [show c * y = -((-c) * y) by ring, show c * x = -((-c) * x) by ring,
    atan2_neg_coe_angle hne, atan2_pos_mul_coe_angle hc']

/-- A pair that really is `(cos θ, sin θ)` reads back as `θ`: the pair is the unit-circle point
at angle `θ`, whose `Complex.arg` is `θ` modulo a full turn. This is `wrap_coe_angle` in the
spelling the solver uses - the normalisation it drops has nothing to correct - stated for a
caller that never mentions `wrap`. -/
theorem atan2_cos_sin_coe_angle (θ : ℝ) :
    (atan2 (Real.sin θ) (Real.cos θ) : Real.Angle) = (θ : Real.Angle) := by
  rw [atan2]
  exact arg_cos_sin_mk_coe_angle θ

/-- `arccos (cos ψ)` is the angle in `[0, π]` that `ψ` reduces to modulo a full turn, so it is
`ψ` or `-ψ` there, and the sign of `sin ψ` decides which: with `sin ψ ≥ 0` the arccos lands on
`ψ` itself. The closed form's elbow step is literally `ε * Real.arccos (elbowCosine …)` with
`ε = ±1`, so this is what turns the `ε = +1` branch back into the direction it was meant to
name. -/
theorem arccos_cos_coe_angle_of_nonneg {ψ : ℝ} (h : 0 ≤ Real.sin ψ) :
    (Real.arccos (Real.cos ψ) : Real.Angle) = (ψ : Real.Angle) := by
  -- The arccos has the cosine of `ψ` by definition, and its sine is `√(1 - cos²ψ)`, which is
  -- `√(sin²ψ)`: the hypothesis says that root is `sin ψ` and not `|sin ψ|`. With the sine and
  -- the cosine both matched, the `(cos, sin)` pair is the pair of `ψ`, and a `(cos, sin)` pair
  -- reads back as its own angle.
  have hcos : Real.cos (Real.arccos (Real.cos ψ)) = Real.cos ψ :=
    Real.cos_arccos (Real.neg_one_le_cos ψ) (Real.cos_le_one ψ)
  have hsin : Real.sin (Real.arccos (Real.cos ψ)) = Real.sin ψ := by
    rw [Real.sin_arccos,
      show 1 - Real.cos ψ ^ 2 = Real.sin ψ ^ 2 by
        rw [← Real.sin_sq_add_cos_sq ψ]; ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg h]
  rw [← atan2_cos_sin_coe_angle (Real.arccos (Real.cos ψ)), hcos, hsin,
    atan2_cos_sin_coe_angle ψ]

/-- The other sign of the elbow's round trip: with `sin ψ ≤ 0` the arccos has to be negated to
land back on `ψ`, which is the `ε = -1` branch of the solver's elbow step. The proof runs the
nonnegative-sine lemma on `-ψ`, where the sine flips sign and the cosine does not, so the `-`
the arccos would have dropped reappears in front of it. That `-arccos (cos ψ)` reaches `-π`
when `ψ` is an odd multiple of `π` - a value `atan2` never returns - is exactly why the
statement is one about `Real.Angle`, where the two ends of the range are the same angle.

The hypotheses of this lemma and of `arccos_cos_coe_angle_of_nonneg` overlap at `sin ψ = 0`:
both hold there and both statements are true, as they must be, since a zero sine carries no
sign for the branch to select. -/
theorem arccos_cos_coe_angle_of_nonpos {ψ : ℝ} (h : Real.sin ψ ≤ 0) :
    (-Real.arccos (Real.cos ψ) : Real.Angle) = (ψ : Real.Angle) := by
  have h' : 0 ≤ Real.sin (-ψ) := by
    rw [Real.sin_neg]
    exact neg_nonneg.mpr h
  -- `arccos (cos ψ) = -ψ` as angles, since `cos (-ψ) = cos ψ` and the pair of real angles
  -- `-ψ` and `ψ` coerce to opposite angles. The goal's negation is the one of `Real.Angle`
  -- (the ascription in the statement is what puts it there), so negating h2 twice is the step
  -- that removes it.
  have h2 := arccos_cos_coe_angle_of_nonneg (ψ := -ψ) h'
  rw [Real.cos_neg, Real.Angle.coe_neg] at h2
  rw [h2, neg_neg]

end RealAtan2
