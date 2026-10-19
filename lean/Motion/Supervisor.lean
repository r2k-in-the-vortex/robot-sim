module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

noncomputable section

@[expose] public section

/-!
# Supervisor-side kinematic lemma

`docs/motion_control.md` §5.4's provable half of stall detection. If the measured position
is clamped from `t0` on and the reference keeps moving at least at `v_min > 0`, the
tracking error grows at least linearly and crosses any finite abort threshold in finite
time. The saturation conjunct of the supervisor's `Stall` decision is a simulation
property, not part of this lemma.
-/

namespace Motion

/-- Under a position clamp and a reference moving at least at `v_min`, the error
`q_ref - q_meas` grows at least linearly from its value at `t0`. -/
theorem stall_error_grows (q_meas q_ref : ℝ → ℝ) (t0 v_min : ℝ)
    (hclamp : ∀ t ≥ t0, q_meas t = q_meas t0)
    (href : ∀ t ≥ t0, q_ref t ≥ q_ref t0 + v_min * (t - t0))
    (_hv : 0 < v_min) :
    ∀ t ≥ t0, q_ref t - q_meas t ≥ (q_ref t0 - q_meas t0) + v_min * (t - t0) := by
  intro t ht
  rw [hclamp t ht]
  linarith [href t ht]

/-- The error provably reaches any threshold above its current value in finite time. -/
theorem stall_error_crosses (q_meas q_ref : ℝ → ℝ) (t0 v_min eps : ℝ)
    (hclamp : ∀ t ≥ t0, q_meas t = q_meas t0)
    (href : ∀ t ≥ t0, q_ref t ≥ q_ref t0 + v_min * (t - t0))
    (hv : 0 < v_min) (heps : q_ref t0 - q_meas t0 < eps) :
    ∃ t ≥ t0, eps ≤ q_ref t - q_meas t := by
  let dt : ℝ := (eps - (q_ref t0 - q_meas t0)) / v_min
  have hdt0 : 0 ≤ dt := div_nonneg (sub_nonneg.mpr heps.le) hv.le
  refine ⟨t0 + dt, by linarith, ?_⟩
  have hgrow := stall_error_grows q_meas q_ref t0 v_min hclamp href hv (t0 + dt) (by linarith)
  have hdt : v_min * dt = eps - (q_ref t0 - q_meas t0) := by
    unfold dt
    field_simp [hv.ne']
  linarith

end Motion
