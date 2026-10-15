module
-- These are `public import`s because the declarations below are exported
-- (`@[expose] public section`): everything their types and bodies mention has to
-- be part of this module's public interface, or importers cannot use them.
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
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

end RealAtan2
