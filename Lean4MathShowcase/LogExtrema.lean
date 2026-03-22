import Mathlib

open Real

/-
  f(x) = (a+1)x - (x+1) ln x   for x > 0

  Part 1: When a = 0, the tangent line at (1, f(1)) is y = 2 - x  (i.e. x + y - 2 = 0).
  Part 2: When f has two extreme points x₁ < x₂, prove 2 < x₁ + x₂ < 3e^(a-1) - 1.
-/

noncomputable def f (a : ℝ) (x : ℝ) : ℝ := (a + 1) * x - (x + 1) * Real.log x

/-- Part 1: When a = 0, f(1) = 1 and f'(1) = -1.
    Therefore, the tangent line at (1, f(1)) is y - 1 = -1·(x - 1), i.e., y = 2 - x,
    equivalently x + y - 2 = 0. -/
theorem part1_tangent_line :
    f 0 1 = 1 ∧ HasDerivAt (f 0) (-1) 1 := by
  unfold f; norm_num;
  convert HasDerivAt.sub ( hasDerivAt_id ( 1 : ℝ ) ) ( HasDerivAt.mul ( HasDerivAt.add ( hasDerivAt_id ( 1 : ℝ ) ) ( hasDerivAt_const _ _ ) ) ( Real.hasDerivAt_log _ ) ) using 1 <;> norm_num

/-
  For Part 2, the critical points satisfy a = ln x + 1/x.
  Define g(x) = ln x + 1/x. Then g'(x) = (x-1)/x².
  g is strictly decreasing on (0,1) and increasing on (1,∞), with minimum g(1) = 1.
  For a > 1, g(x) = a has two solutions x₁ < 1 < x₂.
  We prove: 2 < x₁ + x₂ < 3·e^(a-1) - 1.
-/

noncomputable def g (x : ℝ) : ℝ := Real.log x + 1 / x

lemma g_one : g 1 = 1 := by simp [g, Real.log_one]

lemma g_deriv (x : ℝ) (hx : x ≠ 0) : HasDerivAt g ((x - 1) / x ^ 2) x := by
  convert HasDerivAt.add ( Real.hasDerivAt_log hx ) ( HasDerivAt.div ( hasDerivAt_const _ _ ) ( hasDerivAt_id x ) hx ) using 1 ; ring!;
  norm_num [ sq, hx ]

lemma g_strictAntiOn : StrictAntiOn g (Set.Ioo 0 1) := by
  have h_deriv_neg : ∀ x ∈ Set.Ioo 0 1, deriv g x < 0 := by
    intro x hx; rw [ show deriv g x = ( x - 1 ) / x ^ 2 from HasDerivAt.deriv ( g_deriv x hx.1.ne' ) ] ; exact div_neg_of_neg_of_pos ( by linarith [ hx.2 ] ) ( sq_pos_of_pos hx.1 ) ;
  intros x hx y hy hxy;
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv g c = (g y - g x) / (y - x) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact continuousOn_of_forall_continuousAt fun z hz => HasDerivAt.continuousAt ( g_deriv z <| by linarith [ hx.1, hy.1, hz.1 ] );
    · exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv_neg z ⟨ by linarith [ hz.1, hx.1 ], by linarith [ hz.2, hy.2 ] ⟩ ) ) );
  have := h_deriv_neg c ⟨ by linarith [ hc.1.1, hx.1 ], by linarith [ hc.1.2, hy.2 ] ⟩ ; rw [ hc.2, div_lt_iff₀ ] at this <;> linarith;

lemma g_strictMonoOn : StrictMonoOn g (Set.Ioi 1) := by
  have hg'_pos : ∀ x > 1, deriv g x > 0 := by
    intros x hx; rw [ show deriv g x = ( x - 1 ) / x ^ 2 from HasDerivAt.deriv ( g_deriv x ( by linarith ) ) ] ; exact div_pos ( by linarith ) ( sq_pos_of_pos ( by linarith ) ) ;
  intros x hx y hy hxy;
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv g c = (g y - g x) / (y - x) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact continuousOn_of_forall_continuousAt fun z hz => DifferentiableAt.continuousAt <| by exact differentiableAt_of_deriv_ne_zero <| ne_of_gt <| hg'_pos z <| lt_of_lt_of_le hx.out hz.1;
    · exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( hg'_pos z ( by linarith [ hz.1, hx.out ] ) ) ) );
  have := hg'_pos c ( lt_trans hx.out hc.1.1 ) ; rw [ hc.2, gt_iff_lt ] at this; rw [ lt_div_iff₀ ] at this <;> linarith;

/-- If g(x₁) = g(x₂) with 0 < x₁ < x₂, then x₁ < 1 < x₂. -/
lemma g_eq_implies_straddle (x₁ x₂ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hlt : x₁ < x₂) (heq : g x₁ = g x₂) :
    x₁ < 1 ∧ 1 < x₂ := by
  by_cases h₂ : x₂ ≤ 1;
  · have h_decreasing : StrictAntiOn g (Set.Ioo 0 1) := by
      exact?;
    cases eq_or_lt_of_le h₂ <;> simp_all +decide [ StrictAntiOn ];
    · unfold g at * ; norm_num at *;
      nlinarith [ inv_mul_cancel₀ hx₁.ne', Real.log_inv x₁ ▸ Real.log_lt_sub_one_of_pos ( inv_pos.mpr hx₁ ) ( by nlinarith [ inv_mul_cancel₀ hx₁.ne' ] ) ];
    · linarith [ h_decreasing hx₁ ( by linarith ) hx₂ ( by linarith ) hlt ];
  · refine ⟨ ?_, lt_of_not_ge h₂ ⟩;
    by_cases h₃ : x₁ > 1;
    · exact absurd heq ( ne_of_lt ( g_strictMonoOn ( by norm_num; linarith ) ( by norm_num; linarith ) hlt ) );
    · contrapose! heq;
      norm_num [ show x₁ = 1 by linarith ] at *;
      exact ne_of_lt ( by exact ( show g 1 < g x₂ from by exact ( show Real.log 1 + 1 / 1 < Real.log x₂ + 1 / x₂ from by have := Real.log_lt_sub_one_of_pos ( inv_pos.mpr hx₂ ) ( by nlinarith [ mul_inv_cancel₀ ( ne_of_gt hx₂ ) ] ) ; norm_num at * ; nlinarith [ mul_inv_cancel₀ ( ne_of_gt hx₂ ) ] ) ) )

lemma g_gt_one (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) : g x > 1 := by
  unfold g; ring_nf; replace := Real.log_lt_sub_one_of_pos ( inv_pos.mpr hx ) ; aesop;

/-- g(2 - t) < g(t) for t ∈ (0,1). Key lemma for the lower bound. -/
lemma g_comparison_lower (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    g (2 - t) < g t := by
  set h : ℝ → ℝ := fun t => g t - g (2 - t)
  have h_deriv_neg : ∀ t ∈ Set.Ioo 0 1, deriv h t < 0 := by
    have h_deriv : ∀ t ∈ Set.Ioo 0 1, deriv h t = (t - 1) / t^2 - (t - 1) / (2 - t)^2 := by
      intro t ht; erw [ deriv_sub ] <;> norm_num [ g ];
      · convert congr_arg₂ _ ( g_deriv t ht.1.ne' |> HasDerivAt.deriv ) ( HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.log ( hasDerivAt_id' t |> HasDerivAt.const_sub 2 ) ( by linarith [ ht.1, ht.2 ] ) ) ( HasDerivAt.inv ( hasDerivAt_id' t |> HasDerivAt.const_sub 2 ) ( by linarith [ ht.1, ht.2 ] ) ) ) ) using 1 ; norm_num ; ring;
        grind;
      · exact DifferentiableAt.add ( Real.differentiableAt_log ht.1.ne' ) ( DifferentiableAt.div ( differentiableAt_const _ ) differentiableAt_id ht.1.ne' );
      · exact DifferentiableAt.add ( DifferentiableAt.log ( differentiableAt_id.const_sub _ ) ( by linarith [ ht.1, ht.2 ] ) ) ( DifferentiableAt.inv ( differentiableAt_id.const_sub _ ) ( by linarith [ ht.1, ht.2 ] ) );
    intro t ht; rw [ h_deriv t ht ] ; rw [ div_sub_div, div_lt_iff₀ ] <;> nlinarith [ ht.1, ht.2, mul_pos ht.1 ( sub_pos.mpr ht.2 ) ] ;
  have h_mvt : ∃ c ∈ Set.Ioo t 1, deriv h c = (h 1 - h t) / (1 - t) := by
    apply_rules [ exists_deriv_eq_slope ];
    · refine' ContinuousOn.sub _ _;
      · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.add ( Real.continuousAt_log ( by linarith [ hx.1 ] ) ) ( ContinuousAt.div continuousAt_const continuousAt_id ( by linarith [ hx.1 ] ) ) ;
      · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.comp ( show ContinuousAt g ( 2 - x ) from by exact ContinuousAt.add ( Real.continuousAt_log ( by linarith [ hx.1, hx.2 ] ) ) ( ContinuousAt.div continuousAt_const continuousAt_id ( by linarith [ hx.1, hx.2 ] ) ) ) ( continuousAt_const.sub continuousAt_id );
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv_neg x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ) ) );
  norm_num +zetaDelta at *;
  obtain ⟨ c, ⟨ h₁, h₂ ⟩, h₃ ⟩ := h_mvt; have := h_deriv_neg c ( by linarith ) ( by linarith ) ; rw [ h₃, div_lt_iff₀ ] at this <;> linarith;

/-- Part 2a: Lower bound x₁ + x₂ > 2. -/
theorem part2_lower_bound (a x₁ x₂ : ℝ)
    (hx₁_pos : 0 < x₁) (hx₂_pos : 0 < x₂)
    (hlt : x₁ < x₂)
    (h₁ : g x₁ = a) (h₂ : g x₂ = a) :
    2 < x₁ + x₂ := by
  have h_strict : g (2 - x₁) < g x₂ := by
    convert g_comparison_lower x₁ hx₁_pos _ using 1 ; aesop;
    exact g_eq_implies_straddle x₁ x₂ hx₁_pos hx₂_pos hlt ( h₁.trans h₂.symm ) |>.1;
  contrapose! h_strict;
  apply_rules [ g_strictMonoOn.monotoneOn ] <;> norm_num [ h_strict ] <;> linarith [ g_eq_implies_straddle x₁ x₂ hx₁_pos hx₂_pos hlt <| by linarith ] ;

/-
  Upper bound proof:
  Let u = 1/x₁ > 1. Then a = u - ln u, e^(a-1) = e^(u-1)/u.
  Let m = 3e^(u-1) - u - 1. We show x₂ < m/u by proving g(m/u) > a.
  This reduces to F(u) := ln m + u/m - u > 0.
  F(1) = 0 and F'(u) = (m - u²)/m². Since G(u) = 3e^(u-1) - u² - u - 1 > 0 for u > 1
  (because G(1) = G'(1) = 0 and G''(u) = 3e^(u-1) - 2 > 0), F' > 0, hence F > 0.
-/

/-- 3e^(u-1) > u² + u + 1 for u > 1 -/
lemma aux_G_pos (u : ℝ) (hu : u > 1) :
    3 * Real.exp (u - 1) > u ^ 2 + u + 1 := by
  suffices h_exp : Real.exp (u - 1) > (u^2 + u + 1) / 3 by
    linarith;
  rw [ Real.exp_eq_exp_ℝ ] at *;
  rw [ NormedSpace.exp_eq_tsum_div ];
  refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( Finset.range ( 5 : ℕ ) ) ( fun _ _ => by exact div_nonneg ( pow_nonneg ( sub_nonneg.mpr hu.le ) _ ) ( Nat.cast_nonneg _ ) ) ( by simpa using Real.summable_pow_div_factorial _ ) ) ; norm_num [ Finset.sum_range_succ, Nat.factorial ] ; nlinarith [ pow_pos ( sub_pos.mpr hu ) 3, pow_pos ( sub_pos.mpr hu ) 4 ] ;

set_option maxHeartbeats 400000 in
/-- ln m + u/m > u for u > 1, where m = 3e^(u-1) - u - 1. -/
lemma aux_F_pos (u : ℝ) (hu : u > 1) :
    let m := 3 * Real.exp (u - 1) - u - 1
    Real.log m + u / m - u > 0 := by
  -- We'll use that $F(u)$ is differentiable and its derivative is positive for $u > 1$.
  have h_deriv_pos : ∀ u > 1, 0 < (deriv (fun u => Real.log (3 * Real.exp (u - 1) - u - 1) + u / (3 * Real.exp (u - 1) - u - 1) - u)) u := by
    intro u hu
    have hm : 3 * Real.exp (u - 1) - u - 1 > u^2 := by
      have := aux_G_pos u hu; linarith;
    have h_pos : 0 < (3 * Real.exp (u - 1) - u - 1 - u^2) / (3 * Real.exp (u - 1) - u - 1)^2 := by
      exact div_pos ( by linarith ) ( sq_pos_of_pos ( by nlinarith ) )
    simp [h_pos];
    convert h_pos using 1;
    norm_num [ show 3 * Real.exp ( u - 1 ) - u - 1 ≠ 0 by nlinarith ] ; ring;
    grind;
  -- Since $F(u)$ is differentiable and its derivative is positive for $u > 1$, we can apply the Mean Value Theorem to $F$ on the interval $(1, u)$.
  have h_mvt : ∃ c ∈ Set.Ioo 1 u, deriv (fun u => Real.log (3 * Real.exp (u - 1) - u - 1) + u / (3 * Real.exp (u - 1) - u - 1) - u) c = (Real.log (3 * Real.exp (u - 1) - u - 1) + u / (3 * Real.exp (u - 1) - u - 1) - u - (Real.log (3 * Real.exp (1 - 1) - 1 - 1) + 1 / (3 * Real.exp (1 - 1) - 1 - 1) - 1)) / (u - 1) := by
    apply_rules [ exists_deriv_eq_slope ];
    · refine' ContinuousOn.sub ( ContinuousOn.add ( ContinuousOn.log _ _ ) ( ContinuousOn.div continuousOn_id _ _ ) ) continuousOn_id;
      · exact Continuous.continuousOn ( by continuity );
      · exact fun x hx => by linarith [ hx.1, hx.2, Real.add_one_le_exp ( x - 1 ) ] ;
      · exact Continuous.continuousOn ( by continuity );
      · exact fun x hx => by nlinarith [ hx.1, hx.2, Real.add_one_le_exp ( x - 1 ) ] ;
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( h_deriv_pos x hx.1 ) ) );
  obtain ⟨ c, ⟨ hc1, hc2 ⟩, hc3 ⟩ := h_mvt; have := h_deriv_pos c hc1; rw [ hc3, lt_div_iff₀ ] at this <;> norm_num at * <;> linarith;

/-- Part 2b: Upper bound x₁ + x₂ < 3e^(a-1) - 1. -/
theorem part2_upper_bound (a x₁ x₂ : ℝ)
    (hx₁_pos : 0 < x₁) (hx₂_pos : 0 < x₂)
    (hlt : x₁ < x₂)
    (h₁ : g x₁ = a) (h₂ : g x₂ = a) :
    x₁ + x₂ < 3 * Real.exp (a - 1) - 1 := by
  -- Let u = 1/x₁ > 1. Then a = g(1/u) = u - ln u and e^(a-1) = e^(u-1)/u.
  set u := 1 / x₁
  have hu : u > 1 := by
    -- Since $x₁ < 1$, we have $1/x₁ > 1$.
    have hx₁_lt_1 : x₁ < 1 := by
      exact g_eq_implies_straddle x₁ x₂ hx₁_pos hx₂_pos hlt ( h₁.trans h₂.symm ) |>.1.trans_le ( by norm_num ) ;
    exact one_lt_one_div hx₁_pos hx₁_lt_1
  have ha : a = u - Real.log u := by
    simp +zetaDelta at *;
    unfold g at h₁; ring_nf at *; aesop;
  have h_exp : Real.exp (a - 1) = Real.exp (u - 1) / u := by
    rw [ ha, Real.exp_sub, Real.exp_sub ] ; ring;
    norm_num [ Real.exp_add, Real.exp_neg, Real.exp_log ( zero_lt_one.trans hu ) ] ; ring;
  have hm : 3 * Real.exp (a - 1) - 1 - x₁ = (3 * Real.exp (u - 1) - u - 1) / u := by
    grind +ring
  set m := 3 * Real.exp (u - 1) - u - 1
  have hm_pos : m > 0 := by
    exact sub_pos_of_lt ( by have := Real.add_one_lt_exp ( show u - 1 ≠ 0 by linarith ) ; linarith )
  have hm_u : m / u > 1 := by
    simp +zetaDelta at *;
    have := aux_G_pos ( x₁⁻¹ ) hu; nlinarith [ mul_inv_cancel₀ hx₁_pos.ne' ] ;
  have hm_x2 : x₂ < m / u := by
    -- We need to show that $g(m/u) > g(x₂) = a$.
    have h_gmu_gt_a : g (m / u) > a := by
      have hg_m_u_simplified : g (m / u) = Real.log m - Real.log u + u / m := by
        unfold g; rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring;
        norm_num [ mul_comm ];
      linarith [ aux_F_pos u hu ];
    contrapose! h_gmu_gt_a;
    rw [ ← h₂ ] ; exact ( g_strictMonoOn.le_iff_le ( by norm_num; linarith ) ( by norm_num; linarith ) ) |>.2 h_gmu_gt_a;
  have h_final : x₁ + x₂ < 3 * Real.exp (a - 1) - 1 := by
    linarith
  exact h_final

/-- Part 2: Two-sided estimate on the sum of extreme points.

If 0 < x₁ < x₂ and both satisfy g(xᵢ) = ln(xᵢ) + 1/xᵢ = a
(equivalently, f'(xᵢ) = 0), then 2 < x₁ + x₂ < 3·e^(a-1) - 1. -/
theorem part2_extreme_point_sum (a x₁ x₂ : ℝ)
    (hx₁_pos : 0 < x₁) (hx₂_pos : 0 < x₂)
    (hlt : x₁ < x₂)
    (h₁ : g x₁ = a) (h₂ : g x₂ = a) :
    2 < x₁ + x₂ ∧ x₁ + x₂ < 3 * Real.exp (a - 1) - 1 :=
  ⟨part2_lower_bound a x₁ x₂ hx₁_pos hx₂_pos hlt h₁ h₂,
   part2_upper_bound a x₁ x₂ hx₁_pos hx₂_pos hlt h₁ h₂⟩
