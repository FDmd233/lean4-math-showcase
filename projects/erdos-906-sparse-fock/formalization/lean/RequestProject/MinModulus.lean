import Mathlib

/-!
# A minimum-modulus zero-detection principle

This file contains the complex-analytic input that replaces Rouché's theorem in the
localisation argument of Section 3 of the paper *Zeros of high derivatives of sparse
Fock series*.

If `f` is holomorphic on a neighbourhood of a closed disc and the modulus of `f` at the
centre of the disc is strictly smaller than a lower bound `M` for `‖f‖` on the bounding
circle, then `f` has a zero in the closed disc.  This is the minimum-modulus principle,
obtained by applying the maximum-modulus principle to `1 / f`.
-/

namespace SparseFock

open Metric

/-- **Minimum modulus principle / zero detection.**  If `f` is entire, `r > 0`,
`‖f z‖ ≥ M` on the circle of radius `r` about `z₀` and `‖f z₀‖ < M`, then `f` vanishes
somewhere in the closed disc of radius `r` about `z₀`. -/
theorem exists_zero_of_norm_lt_on_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z₀ : ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ z ∈ Metric.sphere z₀ r, M ≤ ‖f z‖) (h0 : ‖f z₀‖ < M) :
    ∃ z ∈ Metric.closedBall z₀ r, f z = 0 := by
  by_contra hcon
  push_neg at hcon
  -- `g = 1/f` is holomorphic on the closed disc.
  have hMpos : 0 < M := lt_of_le_of_lt (norm_nonneg _) h0
  set g : ℂ → ℂ := fun z => (f z)⁻¹ with hg_def
  have hgdiff : DiffContOnCl ℂ g (Metric.ball z₀ r) := by
    constructor
    · intro z hz
      have hz' : z ∈ Metric.closedBall z₀ r := Metric.ball_subset_closedBall hz
      exact (((hf z).inv (hcon z hz')).differentiableWithinAt)
    · rw [closure_ball z₀ (ne_of_gt hr)]
      intro z hz
      exact (((hf z).inv (hcon z hz)).continuousAt).continuousWithinAt
  have hfront : ∀ z ∈ frontier (Metric.ball z₀ r), ‖g z‖ ≤ 1 / M := by
    intro z hz
    rw [frontier_ball z₀ (ne_of_gt hr)] at hz
    have h1 : M ≤ ‖f z‖ := hM z hz
    rw [hg_def]
    simp only [inv_eq_one_div, norm_div, norm_one]
    exact one_div_le_one_div_of_le hMpos h1
  have hz₀ : z₀ ∈ closure (Metric.ball z₀ r) := by
    rw [closure_ball z₀ (ne_of_gt hr)]
    simp [Metric.mem_closedBall, hr.le]
  have hkey := Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball) hgdiff hfront hz₀
  have hf0 : f z₀ ≠ 0 := hcon z₀ (by simp [Metric.mem_closedBall, hr.le])
  rw [hg_def] at hkey
  simp only [norm_inv] at hkey
  have hnorm0 : 0 < ‖f z₀‖ := norm_pos_iff.2 hf0
  rw [inv_le_iff_one_le_mul₀ hnorm0] at hkey
  · have hlt : 1 / M * ‖f z₀‖ < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one hMpos]
      exact h0
    linarith
