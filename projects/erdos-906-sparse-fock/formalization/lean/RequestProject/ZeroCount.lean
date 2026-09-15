import Mathlib

/-!
# Uniqueness and simplicity of the zero of a dominant two-term model

The complex-analytic argument below upgrades the *existence* statement of
`TwoTerm.lean` (a zero of `f` near a model zero) to an exact local zero **count**.

The situation is the one of Proposition 3.2 ("Rouché transfer") of the manuscript.  Near a
model center `z₀` with `‖z₀‖ = ρ` the function `f` is approximated by the two-term model

`H(z) = A z^m (1 - (z/z₀)^q)`,

whose only zero in a small disc around `z₀` is the simple zero `z₀` itself.  If the error
`f - H` is at most `‖A‖ ‖z‖^m K` on a slightly larger disc, with `K` small compared with
`q s`, then `f` has **at most one** zero in `closedBall z₀ (ρ s)`, and every zero of `f`
there is **simple** (`deriv f ≠ 0`).

Together with the existence statement this gives exactly one zero counted with
multiplicity.  The argument is elementary and quantitative: a Cauchy estimate for the
derivative of the normalised error, plus the mean value inequality on the (convex) disc.
No argument principle or Rouché theorem from `Mathlib` is used (neither is available).
-/

namespace SparseFock

open Metric

/-- `‖t ^ i - 1‖ ≤ (1 + ‖t - 1‖) ^ i - 1`. -/
theorem norm_pow_sub_one_le (t : ℂ) : ∀ i : ℕ, ‖t ^ i - 1‖ ≤ (1 + ‖t - 1‖) ^ i - 1 := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      have hd : (0:ℝ) ≤ ‖t - 1‖ := norm_nonneg _
      have ht : ‖t‖ ≤ 1 + ‖t - 1‖ := by
        have := norm_add_le (t - 1) (1 : ℂ)
        simpa [add_comm] using this
      have hstep : t ^ (i + 1) - 1 = t * (t ^ i - 1) + (t - 1) := by ring
      have hpow : (0:ℝ) ≤ (1 + ‖t - 1‖) ^ i - 1 := by
        have : (1:ℝ) ≤ (1 + ‖t - 1‖) ^ i := one_le_pow₀ (by linarith)
        linarith
      calc ‖t ^ (i + 1) - 1‖ = ‖t * (t ^ i - 1) + (t - 1)‖ := by rw [hstep]
        _ ≤ ‖t * (t ^ i - 1)‖ + ‖t - 1‖ := norm_add_le _ _
        _ = ‖t‖ * ‖t ^ i - 1‖ + ‖t - 1‖ := by rw [norm_mul]
        _ ≤ (1 + ‖t - 1‖) * ((1 + ‖t - 1‖) ^ i - 1) + ‖t - 1‖ := by
            have h1 : ‖t‖ * ‖t ^ i - 1‖ ≤ (1 + ‖t - 1‖) * ((1 + ‖t - 1‖) ^ i - 1) :=
              mul_le_mul ht ih (norm_nonneg _) (by linarith)
            linarith
        _ = (1 + ‖t - 1‖) ^ (i + 1) - 1 := by ring

/-- `exp (1/8) ≤ 8/7`. -/
theorem exp_one_eighth_le : Real.exp (1/8) ≤ 8/7 := by
  have h : (1:ℝ) - 1/8 ≤ Real.exp (-(1/8)) := by
    have := Real.add_one_le_exp (-(1/8) : ℝ)
    linarith
  have hpos : (0:ℝ) < Real.exp (-(1/8)) := Real.exp_pos _
  have hmul : Real.exp (-(1/8)) * Real.exp (1/8) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1/8 : ℝ)]

/-- If `‖t - 1‖ ≤ s` and `(q:ℝ) * s ≤ 1/8`, then `t ^ (q-1)` is within `1/7` of `1`. -/
theorem norm_pow_pred_sub_one_le {t : ℂ} {s : ℝ} {q : ℕ} (hs : 0 < s)
    (hqs : (q : ℝ) * s ≤ 1/8) (ht : ‖t - 1‖ ≤ s) :
    ‖t ^ (q - 1) - 1‖ ≤ 1/7 := by
  have hd : (0:ℝ) ≤ ‖t - 1‖ := norm_nonneg _
  have h1 : ‖t ^ (q - 1) - 1‖ ≤ (1 + ‖t - 1‖) ^ (q - 1) - 1 := norm_pow_sub_one_le t _
  have h2 : (1 + ‖t - 1‖) ^ (q - 1) ≤ (1 + s) ^ (q - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h3 : (1 + s) ^ (q - 1) ≤ Real.exp (s * ((q : ℝ) - 1)) ∨ q = 0 := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · exact Or.inr hq0
    · left
      have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        have : 1 ≤ q := hq0
        push_cast [Nat.cast_sub this]
        ring
      have h4 : (1 + s) ^ (q - 1) ≤ (Real.exp s) ^ (q - 1) := by
        refine pow_le_pow_left₀ (by linarith) ?_ _
        have := Real.add_one_le_exp s
        linarith
      calc (1 + s) ^ (q - 1) ≤ (Real.exp s) ^ (q - 1) := h4
        _ = Real.exp (s * ((q : ℝ) - 1)) := by
            rw [← Real.exp_nat_mul, hcast]; ring_nf
  rcases h3 with h3 | hq0
  · have h5 : s * ((q : ℝ) - 1) ≤ 1/8 := by nlinarith
    have h6 : Real.exp (s * ((q : ℝ) - 1)) ≤ Real.exp (1/8) := Real.exp_le_exp.2 h5
    have h7 := exp_one_eighth_le
    linarith
  · subst hq0
    simp

/-- **At most one zero, and it is simple.**  Under a two-term domination on the disc of
radius `2 ρ s` about `z₀` with a sufficiently small relative error `K`, the function `f`
has at most one zero in `closedBall z₀ (ρ s)`, and every zero of `f` there is simple. -/
theorem unique_zero_of_two_term
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ A : ℂ} {ρ s K : ℝ} {m q : ℕ}
    (hz₀ : ‖z₀‖ = ρ) (hρ : 0 < ρ) (hA : A ≠ 0) (hq : 1 ≤ q)
    (hs : 0 < s) (hqs : (q : ℝ) * s ≤ 1/8) (hK : 0 ≤ K)
    (hdom : ∀ z : ℂ, ‖z - z₀‖ ≤ 2 * ρ * s →
        ‖f z - A * z ^ m * (1 - (z / z₀) ^ q)‖ ≤ ‖A‖ * ‖z‖ ^ m * K)
    (hKs : K < (q : ℝ) * s / 2) :
    (∀ z₁ z₂ : ℂ, ‖z₁ - z₀‖ ≤ ρ * s → ‖z₂ - z₀‖ ≤ ρ * s →
        f z₁ = 0 → f z₂ = 0 → z₁ = z₂) ∧
      (∀ z : ℂ, ‖z - z₀‖ ≤ ρ * s → f z = 0 → deriv f z ≠ 0) := by
  classical
  have hz₀ne : z₀ ≠ 0 := by
    intro h; rw [h] at hz₀; simp at hz₀; exact absurd hz₀.symm (ne_of_gt hρ)
  have hqR : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : s ≤ 1/8 := by nlinarith
  -- the region in the `t = z / z₀` variable
  have hball_ne : ∀ t : ℂ, ‖t - 1‖ ≤ 2 * s → t ≠ 0 := by
    intro t ht h0
    rw [h0] at ht
    simp at ht
    linarith
  -- the normalised function
  set G : ℂ → ℂ := fun t => f (z₀ * t) * (A * (z₀ * t) ^ m)⁻¹ with hG
  set E : ℂ → ℂ := fun t => G t - (1 - t ^ q) with hE
  -- differentiability away from the origin
  have hGdiff : ∀ t : ℂ, t ≠ 0 → DifferentiableAt ℂ G t := by
    intro t ht
    have hne : A * (z₀ * t) ^ m ≠ 0 := by
      refine mul_ne_zero hA (pow_ne_zero _ (mul_ne_zero hz₀ne ht))
    have h1 : DifferentiableAt ℂ (fun t : ℂ => f (z₀ * t)) t :=
      (hf (z₀ * t)).comp t ((differentiable_id.const_mul z₀) t)
    have h2 : DifferentiableAt ℂ (fun t : ℂ => (A * (z₀ * t) ^ m)⁻¹) t := by
      refine DifferentiableAt.inv ?_ hne
      exact ((differentiable_id.const_mul z₀).pow m).const_mul A |>.differentiableAt
    exact h1.mul h2
  have hEdiff : ∀ t : ℂ, t ≠ 0 → DifferentiableAt ℂ E t := by
    intro t ht
    refine (hGdiff t ht).sub ?_
    exact (differentiable_const (1:ℂ)).sub (differentiable_pow q) |>.differentiableAt
  -- the error bound
  have hEbound : ∀ t : ℂ, ‖t - 1‖ ≤ 2 * s → ‖E t‖ ≤ K := by
    intro t ht
    have htne : t ≠ 0 := hball_ne t ht
    have hzne : z₀ * t ≠ 0 := mul_ne_zero hz₀ne htne
    have hdist : ‖z₀ * t - z₀‖ ≤ 2 * ρ * s := by
      have : z₀ * t - z₀ = z₀ * (t - 1) := by ring
      rw [this, norm_mul, hz₀]
      calc ρ * ‖t - 1‖ ≤ ρ * (2 * s) := by
            exact mul_le_mul_of_nonneg_left ht hρ.le
        _ = 2 * ρ * s := by ring
    have hquot : (z₀ * t) / z₀ = t := by field_simp
    have h := hdom (z₀ * t) hdist
    rw [hquot] at h
    have hAne : A * (z₀ * t) ^ m ≠ 0 := mul_ne_zero hA (pow_ne_zero _ hzne)
    have hEeq : E t = (f (z₀ * t) - A * (z₀ * t) ^ m * (1 - t ^ q)) * (A * (z₀ * t) ^ m)⁻¹ := by
      rw [hE, hG]
      field_simp
    rw [hEeq, norm_mul, norm_inv]
    have hnorm : ‖A * (z₀ * t) ^ m‖ = ‖A‖ * ‖z₀ * t‖ ^ m := by
      rw [norm_mul, norm_pow]
    have hpos : 0 < ‖A * (z₀ * t) ^ m‖ := norm_pos_iff.2 hAne
    rw [mul_inv_le_iff₀ hpos, hnorm]
    calc ‖f (z₀ * t) - A * (z₀ * t) ^ m * (1 - t ^ q)‖
        ≤ ‖A‖ * ‖z₀ * t‖ ^ m * K := h
      _ = K * (‖A‖ * ‖z₀ * t‖ ^ m) := by ring
  -- Cauchy estimate for the derivative of the error
  have hEderiv : ∀ t₀ : ℂ, ‖t₀ - 1‖ ≤ s → ‖deriv E t₀‖ ≤ K / s := by
    intro t₀ ht₀
    have hsub : ∀ t : ℂ, t ∈ closedBall t₀ s → ‖t - 1‖ ≤ 2 * s := by
      intro t ht
      have h1 : ‖t - t₀‖ ≤ s := by simpa [Metric.mem_closedBall, dist_eq_norm] using ht
      calc ‖t - 1‖ = ‖(t - t₀) + (t₀ - 1)‖ := by ring_nf
        _ ≤ ‖t - t₀‖ + ‖t₀ - 1‖ := norm_add_le _ _
        _ ≤ 2 * s := by linarith
    have hdc : DiffContOnCl ℂ E (ball t₀ s) := by
      constructor
      · intro t ht
        exact (hEdiff t (hball_ne t (hsub t (ball_subset_closedBall ht)))).differentiableWithinAt
      · rw [closure_ball t₀ (ne_of_gt hs)]
        intro t ht
        exact ((hEdiff t (hball_ne t (hsub t ht))).continuousAt).continuousWithinAt
    have hsph : ∀ t ∈ sphere t₀ s, ‖E t‖ ≤ K := by
      intro t ht
      exact hEbound t (hsub t (sphere_subset_closedBall ht))
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs hdc hsph
  -- lower bound for the derivative of the model
  have hmodel : ∀ t : ℂ, ‖t - 1‖ ≤ s → (6 * (q:ℝ) / 7) ≤ ‖(q : ℂ) * t ^ (q - 1)‖ := by
    intro t ht
    have h := norm_pow_pred_sub_one_le (q := q) hs hqs ht
    have h1 : (1:ℝ) - 1/7 ≤ ‖t ^ (q - 1)‖ := by
      have h2 := norm_sub_norm_le (1 : ℂ) (t ^ (q-1))
      rw [norm_sub_rev (1:ℂ)] at h2
      simp only [norm_one] at h2
      linarith
    rw [norm_mul, Complex.norm_natCast]
    have hqpos : (0:ℝ) ≤ (q:ℝ) := by linarith
    nlinarith
  -- mean value estimate for the model: `‖t₁^q - t₂^q‖ ≥ (6q/7) ‖t₁ - t₂‖`
  have hpowdiff : ∀ t₁ t₂ : ℂ, ‖t₁ - 1‖ ≤ s → ‖t₂ - 1‖ ≤ s →
      (6 * (q:ℝ) / 7) * ‖t₁ - t₂‖ ≤ ‖t₁ ^ q - t₂ ^ q‖ := by
    intro t₁ t₂ h1 h2
    set ψ : ℂ → ℂ := fun t => t ^ q - (q : ℂ) * t with hψ
    have hconv : Convex ℝ (closedBall (1 : ℂ) s) := convex_closedBall _ _
    have hψd : ∀ t ∈ closedBall (1:ℂ) s, DifferentiableAt ℂ ψ t := by
      intro t _
      exact (differentiable_pow q t).sub ((differentiable_id.const_mul ((q:ℂ))) t)
    have hψderiv : ∀ t ∈ closedBall (1:ℂ) s, ‖deriv ψ t‖ ≤ (q:ℝ) / 7 := by
      intro t ht
      have htn : ‖t - 1‖ ≤ s := by simpa [Metric.mem_closedBall, dist_eq_norm] using ht
      have hd : deriv ψ t = (q : ℂ) * t ^ (q - 1) - (q : ℂ) := by
        have h1 : HasDerivAt (fun u : ℂ => u ^ q) ((q : ℂ) * t ^ (q - 1)) t := hasDerivAt_pow q t
        have h2 : HasDerivAt (fun u : ℂ => (q : ℂ) * u) ((q : ℂ)) t := by
          simpa using (hasDerivAt_id t).const_mul ((q : ℂ))
        exact (h1.sub h2).deriv
      rw [hd]
      have hsub : (q : ℂ) * t ^ (q - 1) - (q : ℂ) = (q : ℂ) * (t ^ (q - 1) - 1) := by ring
      rw [hsub, norm_mul, Complex.norm_natCast]
      have := norm_pow_pred_sub_one_le (q := q) hs hqs htn
      have hqpos : (0:ℝ) ≤ (q:ℝ) := by linarith
      nlinarith
    have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hψd hψderiv
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using h2)
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
    have hval : ψ t₁ - ψ t₂ = (t₁ ^ q - t₂ ^ q) - (q : ℂ) * (t₁ - t₂) := by rw [hψ]; ring
    rw [hval] at hmvt
    have hqn : ‖(q : ℂ) * (t₁ - t₂)‖ = (q:ℝ) * ‖t₁ - t₂‖ := by
      rw [norm_mul, Complex.norm_natCast]
    have hstep : (q:ℝ) * ‖t₁ - t₂‖ - ‖t₁ ^ q - t₂ ^ q‖ ≤ (q:ℝ)/7 * ‖t₁ - t₂‖ := by
      have h3 := norm_sub_norm_le ((q : ℂ) * (t₁ - t₂)) (t₁ ^ q - t₂ ^ q)
      have h4 : ‖(q : ℂ) * (t₁ - t₂) - (t₁ ^ q - t₂ ^ q)‖
          = ‖(t₁ ^ q - t₂ ^ q) - (q : ℂ) * (t₁ - t₂)‖ := by
        rw [norm_sub_rev]
      rw [h4] at h3
      rw [hqn] at h3
      linarith
    linarith
  -- mean value estimate for the error
  have hEdiffbd : ∀ t₁ t₂ : ℂ, ‖t₁ - 1‖ ≤ s → ‖t₂ - 1‖ ≤ s →
      ‖E t₁ - E t₂‖ ≤ (K / s) * ‖t₁ - t₂‖ := by
    intro t₁ t₂ h1 h2
    have hconv : Convex ℝ (closedBall (1 : ℂ) s) := convex_closedBall _ _
    have hd : ∀ t ∈ closedBall (1:ℂ) s, DifferentiableAt ℂ E t := by
      intro t ht
      have htn : ‖t - 1‖ ≤ s := by simpa [Metric.mem_closedBall, dist_eq_norm] using ht
      exact hEdiff t (hball_ne t (by linarith))
    have hb : ∀ t ∈ closedBall (1:ℂ) s, ‖deriv E t‖ ≤ K / s := by
      intro t ht
      exact hEderiv t (by simpa [Metric.mem_closedBall, dist_eq_norm] using ht)
    exact hconv.norm_image_sub_le_of_norm_deriv_le hd hb
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using h2)
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
  -- translation between `z` and `t`
  have htrans : ∀ z : ℂ, ‖z - z₀‖ ≤ ρ * s → ‖z / z₀ - 1‖ ≤ s := by
    intro z hz
    have : z / z₀ - 1 = (z - z₀) / z₀ := by field_simp
    rw [this, norm_div, hz₀, div_le_iff₀ hρ]
    linarith [hz, mul_comm ρ s]
  have hzrec : ∀ z : ℂ, z₀ * (z / z₀) = z := by intro z; field_simp
  have hKs' : K / s < 6 * (q:ℝ) / 7 := by
    rw [div_lt_iff₀ hs]
    nlinarith
  constructor
  · intro z₁ z₂ h1 h2 hz1 hz2
    set t₁ := z₁ / z₀
    set t₂ := z₂ / z₀
    have ht1 : ‖t₁ - 1‖ ≤ s := htrans z₁ h1
    have ht2 : ‖t₂ - 1‖ ≤ s := htrans z₂ h2
    have hG1 : G t₁ = 0 := by rw [hG]; simp only; rw [hzrec z₁, hz1, zero_mul]
    have hG2 : G t₂ = 0 := by rw [hG]; simp only; rw [hzrec z₂, hz2, zero_mul]
    have hE1 : E t₁ = t₁ ^ q - 1 := by rw [hE]; simp only; rw [hG1]; ring
    have hE2 : E t₂ = t₂ ^ q - 1 := by rw [hE]; simp only; rw [hG2]; ring
    have hkey : ‖t₁ ^ q - t₂ ^ q‖ = ‖E t₁ - E t₂‖ := by rw [hE1, hE2]; congr 1; ring
    have hlow := hpowdiff t₁ t₂ ht1 ht2
    have hup := hEdiffbd t₁ t₂ ht1 ht2
    rw [← hkey] at hup
    have hzero : ‖t₁ - t₂‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖t₁ - t₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith
    have : t₁ = t₂ := sub_eq_zero.1 (norm_eq_zero.1 hzero)
    have h3 : z₁ = z₀ * t₁ := (hzrec z₁).symm
    have h4 : z₂ = z₀ * t₂ := (hzrec z₂).symm
    rw [h3, h4, this]
  · intro z hz hfz
    set t := z / z₀ with hts
    have ht : ‖t - 1‖ ≤ s := htrans z hz
    have htne : t ≠ 0 := hball_ne t (by linarith)
    have hzt : z₀ * t = z := hzrec z
    have hzne : z ≠ 0 := by
      rw [← hzt]; exact mul_ne_zero hz₀ne htne
    have hG0 : G t = 0 := by rw [hG]; simp only; rw [hzt, hfz, zero_mul]
    -- `deriv G t ≠ 0`
    have hEd : E = fun u => G u - (1 - u ^ q) := hE
    have hderivE : deriv E t = deriv G t - deriv (fun u : ℂ => 1 - u ^ q) t := by
      rw [hEd]
      exact deriv_sub (hGdiff t htne)
        ((differentiable_const (1:ℂ)).sub (differentiable_pow q) |>.differentiableAt)
    have hderivmod : deriv (fun u : ℂ => 1 - u ^ q) t = -((q : ℂ) * t ^ (q - 1)) := by
      exact ((hasDerivAt_pow q t).const_sub (1 : ℂ)).deriv
    rw [hderivmod] at hderivE
    have hGd : deriv G t = deriv E t - (q : ℂ) * t ^ (q - 1) := by linear_combination -hderivE
    have hlow := hmodel t ht
    have hup := hEderiv t ht
    have hGdne : deriv G t ≠ 0 := by
      intro h0
      rw [h0] at hGd
      have heq : (q : ℂ) * t ^ (q - 1) = deriv E t := by linear_combination hGd
      have : ‖(q : ℂ) * t ^ (q - 1)‖ = ‖deriv E t‖ := by rw [heq]
      linarith [hlow, hup, hKs']
    -- transfer to `deriv f z`
    intro hfd
    apply hGdne
    have hcomp : DifferentiableAt ℂ (fun u : ℂ => f (z₀ * u)) t :=
      (hf (z₀ * t)).comp t ((differentiable_id.const_mul z₀) t)
    have hinvd : DifferentiableAt ℂ (fun u : ℂ => (A * (z₀ * u) ^ m)⁻¹) t := by
      refine DifferentiableAt.inv ?_ (mul_ne_zero hA (pow_ne_zero _ (mul_ne_zero hz₀ne htne)))
      exact ((differentiable_id.const_mul z₀).pow m).const_mul A |>.differentiableAt
    have hprod : deriv G t
        = deriv (fun u : ℂ => f (z₀ * u)) t * (A * (z₀ * t) ^ m)⁻¹
          + f (z₀ * t) * deriv (fun u : ℂ => (A * (z₀ * u) ^ m)⁻¹) t := by
      rw [hG]
      exact deriv_mul hcomp hinvd
    have hfz0 : f (z₀ * t) = 0 := by rw [hzt, hfz]
    have hchain : deriv (fun u : ℂ => f (z₀ * u)) t = z₀ * deriv f (z₀ * t) := by
      have h1 : HasDerivAt (fun u : ℂ => z₀ * u) z₀ t := by
        simpa using (hasDerivAt_id t).const_mul z₀
      have h3 : HasDerivAt (fun u : ℂ => f (z₀ * u)) (deriv f (z₀ * t) * z₀) t := by
        simpa [Function.comp_def] using ((hf (z₀ * t)).hasDerivAt.comp t h1)
      rw [h3.deriv]; ring
    rw [hprod, hfz0, zero_mul, add_zero, hchain, hzt, hfd, mul_zero, zero_mul]

end SparseFock
