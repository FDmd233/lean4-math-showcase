/-!
# 对数函数极值示例

这里研究函数 `f(x) = (a + 1)x - (x + 1) log x`。
文件包含两部分内容：`a = 0` 时的切线结论，以及当函数出现两个极值点时它们和的双边估计。
-/

import Mathlib

namespace LeanShowcase.LogExtrema

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of the function f(x) = (a+1)x - (x+1)ln(x).
-/
noncomputable def f (a : ℝ) (x : ℝ) : ℝ := (a + 1) * x - (x + 1) * Real.log x

/-
When a=0, the equation of the tangent line to the curve y=f(x) at the point (1, f(1)) is x + y - 2 = 0 (or y = 2 - x).
-/
def tangent_line_y (x : ℝ) : ℝ := 2 - x

theorem part1 :
  let a := 0
  (f a 1 = tangent_line_y 1) ∧ (deriv (f a) 1 = deriv tangent_line_y 1) := by
    unfold f tangent_line_y;
    norm_num [ sub_eq_add_neg ]

/-
Definition of g(x) = ln(x) + 1/x and its derivative.
-/
noncomputable def g (x : ℝ) : ℝ := Real.log x + 1 / x

lemma g_deriv (x : ℝ) (hx : 0 < x) : deriv g x = (x - 1) / (x ^ 2) := by
  unfold g;
  norm_num [ hx.ne', differentiableAt_inv ] ; ring;
  norm_num [ sq, hx.ne' ]

/-
g(x) is decreasing on (0, 1).
-/
lemma g_decreasing_on_0_1 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : deriv g x < 0 := by
  exact g_deriv x hx0 ▸ div_neg_of_neg_of_pos ( by linarith ) ( sq_pos_of_pos hx0 )

/-
g(x) is increasing on (1, infinity).
-/
lemma g_increasing_on_1_inf (x : ℝ) (hx : 1 < x) : deriv g x > 0 := by
  rw [ show g = fun x => Real.log x + 1 / x from rfl ] ; norm_num [ div_eq_mul_inv, Real.differentiableAt_log, differentiableAt_inv, show x ≠ 0 by linarith ] ; ring ; nlinarith [ inv_mul_cancel₀ ( show x ≠ 0 by linarith ), inv_pos.2 ( show 0 < x by linarith ) ] ;

/-
At a local extremum x of f(a), g(x) = a.
-/
lemma critical_point_value (a : ℝ) (x : ℝ) (hx : 0 < x) (h : IsLocalExtr (f a) x) : g x = a := by
  -- By definition of $f$, we know that its derivative is $f'(x) = (a+1) - \left(\ln(x) + \frac{x+1}{x}\right)$.
  have h_deriv : deriv (f a) x = (a + 1) - (Real.log x + (x + 1) / x) := by
    convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.const_mul ( a + 1 ) ( hasDerivAt_id x ) ) ( HasDerivAt.mul ( HasDerivAt.add ( hasDerivAt_id x ) ( hasDerivAt_const _ _ ) ) ( Real.hasDerivAt_log hx.ne.symm ) ) ) using 1 ; ring!;
    simpa using by ring;
  have := h.deriv_eq_zero; unfold g at *; ring_nf at *; nlinarith [ mul_inv_cancel₀ hx.ne' ] ;

/-
x1 < 1 and x2 > 1.
-/
lemma x1_lt_1_lt_x2 (a : ℝ) (x₁ x₂ : ℝ) (h₁ : 0 < x₁) (h₂ : 0 < x₂) (h_order : x₁ < x₂)
  (hx1 : IsLocalExtr (f a) x₁) (hx2 : IsLocalExtr (f a) x₂) :
  x₁ < 1 ∧ 1 < x₂ := by
    -- By Lemma~\ref{lem:c1}, g(x1) = a and g(x2) = a.
    have h_gx1 : g x₁ = a := by
      exact critical_point_value a x₁ h₁ hx1
    have h_gx2 : g x₂ = a := by
      apply_rules [ critical_point_value ];
    -- Since $g(x)$ is strictly decreasing on $(0, 1)$ and strictly increasing on $(1, \infty)$, we have $x₁ < 1$ and $x₂ > 1$.
    have h_g_decreasing : ∀ x y : ℝ, 0 < x → x < y → y ≤ 1 → g x > g y := by
      field_simp;
      intros x y hx hy hxy; exact (by
      -- By the Mean Value Theorem, there exists some $c \in (x, y)$ such that $g'(c) = (g(y) - g(x)) / (y - x)$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv g c = (g y - g x) / (y - x) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact continuousOn_of_forall_continuousAt fun z hz => by exact ContinuousAt.add ( Real.continuousAt_log ( by linarith [ hz.1 ] ) ) ( ContinuousAt.div continuousAt_const continuousAt_id ( by linarith [ hz.1 ] ) ) ;
        · exact fun u hu => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( Real.differentiableAt_log ( by linarith [ hu.1 ] ) ) ( DifferentiableAt.div ( differentiableAt_const _ ) differentiableAt_id ( by linarith [ hu.1 ] ) ) );
      -- Since $g'(c) = (c - 1) / c^2$ and $c \in (x, y)$ with $x < y \leq 1$, we have $g'(c) < 0$.
      have h_deriv_neg : deriv g c < 0 := by
        exact g_decreasing_on_0_1 c ( by linarith [ hc.1.1 ] ) ( by linarith [ hc.1.2 ] );
      rw [ hc.2, div_lt_iff₀ ] at h_deriv_neg <;> linarith)
    have h_g_increasing : ∀ x y : ℝ, 1 ≤ x → x < y → g x < g y := by
      intros x y hx hy; exact (by
      -- Apply the mean value theorem to the interval $[x, y]$.
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv g c = (g y - g x) / (y - x) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact continuousOn_of_forall_continuousAt fun z hz => by exact ContinuousAt.add ( Real.continuousAt_log ( by linarith [ hz.1 ] ) ) ( continuousAt_const.div continuousAt_id ( by linarith [ hz.1 ] ) ) ;
        · exact fun u hu => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( Real.differentiableAt_log ( by linarith [ hu.1 ] ) ) ( DifferentiableAt.div ( differentiableAt_const _ ) differentiableAt_id ( by linarith [ hu.1 ] ) ) );
      have := g_increasing_on_1_inf c ( by linarith [ hc.1.1 ] ) ; rw [ hc.2, div_eq_mul_inv ] at this; nlinarith [ inv_mul_cancel₀ ( by linarith : ( y - x ) ≠ 0 ) ] ;);
    constructor <;> contrapose! h_g_increasing;
    · exact ⟨ x₁, x₂, h_g_increasing, h_order, by linarith ⟩;
    · linarith [ h_g_decreasing x₁ x₂ h₁ h_order h_g_increasing ]

/-
For 1 < x < 2, g(x) < g(2-x).
-/
lemma g_symmetry_inequality (x : ℝ) (hx1 : 1 < x) (hx2 : x < 2) : g x < g (2 - x) := by
  -- By definition of $h(x)$, we know that $h(x) = g(x) - g(2-x)$.
  set h : ℝ → ℝ := fun x => g x - g (2 - x) with hh_def
  have h_deriv : ∀ x, 1 < x ∧ x < 2 → deriv h x < 0 := by
    -- By definition of $h(x)$, we know that its derivative is $h'(x) = (x-1)/x^2 - (x-1)/(2-x)^2$.
    have h_deriv_def : ∀ x, 1 < x ∧ x < 2 → deriv h x = (x - 1) / x^2 - (x - 1) / (2 - x)^2 := by
      intros x hx
      have h_deriv_def : deriv h x = deriv g x - deriv g (2 - x) * (-1) := by
        convert HasDerivAt.deriv ( HasDerivAt.sub ( hasDerivAt_deriv_iff.mpr _ ) ( HasDerivAt.comp x ( hasDerivAt_deriv_iff.mpr _ ) ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) ) ) using 1 ; ring_nf ; (
        rfl);
        · exact DifferentiableAt.add ( Real.differentiableAt_log ( by linarith ) ) ( DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id ) ( by linarith ) );
        · exact DifferentiableAt.add ( Real.differentiableAt_log ( by linarith ) ) ( DifferentiableAt.div ( differentiableAt_const _ ) ( differentiableAt_id ) ( by linarith ) )
      rw [h_deriv_def];
      rw [ g_deriv, g_deriv ] <;> ring <;> linarith [ inv_mul_cancel₀ ( by linarith : x ≠ 0 ), inv_mul_cancel₀ ( by linarith : ( 2 - x ) ≠ 0 ) ];
    exact fun x hx => h_deriv_def x hx ▸ sub_neg_of_lt ( by rw [ div_lt_div_iff₀ ] <;> nlinarith );
  -- By the Mean Value Theorem, since $h$ is differentiable on $(1, x)$ and $h$ is continuous on $[1, x]$, there exists some $c \in (1, x)$ such that $h'(c) = (h(x) - h(1)) / (x - 1)$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 1 x, deriv h c = (h x - h 1) / (x - 1) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.sub ( ContinuousAt.add ( Real.continuousAt_log ( by linarith [ hx.1 ] ) ) ( continuousAt_const.div continuousAt_id ( by linarith [ hx.1 ] ) ) ) ( ContinuousAt.add ( ContinuousAt.log ( continuousAt_const.sub continuousAt_id ) ( by linarith [ hx.2 ] ) ) ( continuousAt_const.div ( continuousAt_const.sub continuousAt_id ) ( by linarith [ hx.2 ] ) ) );
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv x ⟨ hx.1, hx.2.trans hx2 ⟩ ) ) );
  simp +zetaDelta at *;
  have := h_deriv c hc.1.1 ( by linarith ) ; rw [ hc.2, div_lt_iff₀ ] at this <;> norm_num at * <;> linarith;

/-
x1 + x2 > 2.
-/
lemma sum_gt_two (a : ℝ) (x₁ x₂ : ℝ) (h₁ : 0 < x₁) (h₂ : 0 < x₂) (h_order : x₁ < x₂)
  (hx1 : IsLocalExtr (f a) x₁) (hx2 : IsLocalExtr (f a) x₂) :
  2 < x₁ + x₂ := by
    -- We know $x_1 < 1 < x_2$ from `x1_lt_1_lt_x2`.
    obtain ⟨hx1_lt_1, hx2_gt_1⟩ : x₁ < 1 ∧ 1 < x₂ := by
      exact x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2;
    by_cases hx2_ge_2 : x₂ ≥ 2;
    · linarith [ show x₁ > 0 from h₁ ];
    · -- Since $g(x)$ is strictly decreasing on $(0, 1)$ and $g(x_1) = g(x_2) = a$, we have $g(x_1) < g(2 - x_2)$.
      have h_g_decreasing : g x₁ < g (2 - x₂) := by
        convert g_symmetry_inequality x₂ hx2_gt_1 ( lt_of_not_ge hx2_ge_2 ) using 1;
        exact critical_point_value a x₁ h₁ hx1 ▸ critical_point_value a x₂ h₂ hx2 ▸ rfl;
      -- Since $g(x)$ is strictly decreasing on $(0, 1)$, we have $x_1 > 2 - x_2$.
      have h_x1_gt_2_minus_x2 : x₁ > 2 - x₂ := by
        contrapose! h_g_decreasing;
        -- Since $g(x)$ is strictly decreasing on $(0, 1)$, we have $g(x_1) \geq g(2 - x_2)$.
        have h_g_decreasing : ∀ x y : ℝ, 0 < x → x < y → y < 1 → g x > g y := by
          intros x y hx hy hxy; exact (by
          -- Apply the mean value theorem to the interval $[x, y]$.
          obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv g c = (g y - g x) / (y - x) := by
            apply_rules [ exists_deriv_eq_slope ];
            · exact continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.add ( Real.continuousAt_log ( by linarith [ hz.1 ] ) ) ( ContinuousAt.div continuousAt_const continuousAt_id ( by linarith [ hz.1 ] ) );
            · exact fun u hu => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( Real.differentiableAt_log ( by linarith [ hu.1 ] ) ) ( DifferentiableAt.div ( differentiableAt_const _ ) differentiableAt_id ( by linarith [ hu.1 ] ) ) );
          have := g_decreasing_on_0_1 c ( by linarith [ hc.1.1 ] ) ( by linarith [ hc.1.2 ] ) ; rw [ hc.2, div_lt_iff₀ ] at this <;> linarith;);
        exact le_of_not_gt fun h => by linarith [ h_g_decreasing x₁ ( 2 - x₂ ) h₁ ( lt_of_le_of_ne ‹_› ( by rintro rfl; linarith ) ) ( by linarith ) ] ;
      linarith

/-
h_aux(x) is positive for x > 1.
-/
noncomputable def h_aux (x : ℝ) : ℝ := 3 * x * Real.exp (1 / x - 1) - 1 - x

lemma h_aux_pos (x : ℝ) (hx : 1 < x) : 0 < h_aux x := by
  -- Let's define $t = \frac{1}{x}$ and note that $t \in (0, 1)$ since $x > 1$.
  set t : ℝ := 1 / x
  have ht : 0 < t ∧ t < 1 := by
    exact ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> linarith ⟩;
  -- We'll use that $N(t) = 3 * \exp(t - 1) - t - 1$ is positive for $t \in (0, 1)$.
  have hN_pos : ∀ t ∈ Set.Ioo 0 1, 3 * Real.exp (t - 1) - t - 1 > 0 := by
    intro t ht; have := Real.exp_neg_one_gt_d9; norm_num1 at *; rw [ show t - 1 = -1 + ( t - 0 ) by ring ] ; rw [ Real.exp_add ] ; nlinarith [ Real.add_one_le_exp ( t - 0 ), ht.1, ht.2 ] ;
  convert div_pos ( hN_pos t ht ) ( one_div_pos.mpr ( zero_lt_one.trans hx ) ) using 1 ; ring!;
  unfold h_aux; norm_num ; ring;
  rw [ mul_inv_cancel₀ ( by linarith ) ] ; ring

/-
Definition of the auxiliary function K(t) = 3e^{t-1} - t^2 - t - 1.
-/
noncomputable def K (t : ℝ) : ℝ := 3 * Real.exp (t - 1) - t^2 - t - 1

/-
Derivative of K(t).
-/
lemma K_deriv (t : ℝ) : deriv K t = 3 * Real.exp (t - 1) - 2 * t - 1 := by
  unfold K; norm_num [ Real.differentiableAt_exp, mul_comm ] ;

/-
Second derivative of K(t).
-/
lemma K_deriv2 (t : ℝ) : deriv (deriv K) t = 3 * Real.exp (t - 1) - 2 := by
  rw [ show deriv K = fun t => 3 * Real.exp ( t - 1 ) - 2 * t - 1 from funext fun t => K_deriv t ] ; norm_num [ Real.differentiableAt_exp, mul_comm ]

/-
t_inflection is in (0, 1).
-/
def t_inflection : ℝ := 1 + Real.log (2 / 3)

lemma t_inflection_in_0_1 : 0 < t_inflection ∧ t_inflection < 1 := by
  unfold t_inflection;
  norm_num [ Real.log_neg ];
  linarith [ Real.log_inv ( 2 / 3 ), Real.log_lt_sub_one_of_pos ( inv_pos.mpr ( by norm_num : ( 0 : ℝ ) < 2 / 3 ) ) ( by norm_num ), inv_mul_cancel₀ ( by norm_num : ( 2 / 3 : ℝ ) ≠ 0 ) ]

/-
Sign of the second derivative of K(t).
-/
lemma K_deriv2_sign (t : ℝ) :
  (t < t_inflection → deriv (deriv K) t < 0) ∧
  (t > t_inflection → deriv (deriv K) t > 0) := by
    -- By definition of $t_inflection$, we know that $t_inflection = 1 + \ln(2/3)$.
    have h_t_inflection : t_inflection = 1 + Real.log (2 / 3) := by
      rfl;
    constructor <;> intro h <;> rw [ h_t_inflection ] at * <;> norm_num [ K_deriv2 ] at *;
    · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ; linarith [ Real.log_div ( by positivity : ( 2 : ℝ ) ≠ 0 ) ( by positivity : ( 3 : ℝ ) ≠ 0 ) ];
    · linarith [ Real.log_lt_iff_lt_exp ( by norm_num ) |>.1 ( by linarith : Real.log ( 2 / 3 ) < t - 1 ), Real.exp_pos ( t - 1 ) ]

/-
K'(t) is negative on (t_inflection, 1).
-/
lemma K_deriv_neg_on_right (t : ℝ) (h1 : t_inflection < t) (h2 : t < 1) : deriv K t < 0 := by
  -- Since $K'(1) = 0$, we have $K'(t) < K'(1) = 0$ for $t$ in $(t_inflection, 1)$.
  have h_deriv_neg : ∀ t ∈ Set.Ioo t_inflection 1, deriv K t < deriv K 1 := by
    -- Since $K''(t) > 0$ for $t > t_inflection$, we have $K'(t)$ is strictly increasing on $(t_inflection, 1)$.
    have h_deriv_incr : StrictMonoOn (deriv K) (Set.Ioi t_inflection) := by
      -- Since $K''(t) > 0$ for $t > t_inflection$, we have $K'(t)$ is strictly increasing on $(t_inflection, \infty)$.
      have h_second_deriv_pos : ∀ t, t > t_inflection → 0 < deriv (deriv K) t := by
        exact fun t ht => K_deriv2_sign t |>.2 ht;
      -- Apply the fact that if the derivative of a function is positive on an interval, then the function is strictly increasing on that interval.
      apply strictMonoOn_of_deriv_pos;
      · exact convex_Ioi _;
      · exact continuousOn_of_forall_continuousAt fun x hx => by exact DifferentiableAt.continuousAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( h_second_deriv_pos x hx ) ) );
      · aesop;
    exact fun t ht => h_deriv_incr ( show t_inflection < t by linarith [ ht.1 ] ) ( show t_inflection < 1 by linarith [ ht.2 ] ) ( by linarith [ ht.2 ] );
  exact lt_of_lt_of_le ( h_deriv_neg t ⟨ h1, h2 ⟩ ) ( by unfold K; norm_num [ Real.differentiableAt_exp, mul_comm ] )

/-
K(1) = 0.
-/
lemma K_at_one : K 1 = 0 := by
  unfold K; norm_num;

/-
K(0) > 0.
-/
lemma K_at_zero_pos : K 0 > 0 := by
  exact sub_pos_of_lt ( by have := Real.exp_neg_one_gt_d9; norm_num at *; linarith )

/-
K'(0) > 0.
-/
lemma K_deriv_at_zero_pos : deriv K 0 > 0 := by
  rw [ show K = fun t => 3 * Real.exp ( t - 1 ) - t ^ 2 - t - 1 from funext fun t => rfl ] ; norm_num [ Real.differentiableAt_exp ] ;
  exact lt_of_le_of_lt ( by norm_num ) ( mul_lt_mul_of_pos_left ( Real.exp_neg_one_gt_d9.gt ) zero_lt_three )

/-
K'(t_inflection) < 0.
-/
lemma K_deriv_at_inflection_neg : deriv K t_inflection < 0 := by
  unfold K t_inflection;
  norm_num [ Real.exp_add, Real.exp_log ];
  linarith [ Real.log_inv ( 2 / 3 ), Real.log_lt_sub_one_of_pos ( inv_pos.mpr ( by norm_num : ( 0 : ℝ ) < 2 / 3 ) ) ( by norm_num ), inv_mul_cancel₀ ( by norm_num : ( 2 / 3 : ℝ ) ≠ 0 ) ]

/-
K(t) > 0 for t in [t_inflection, 1).
-/
lemma K_pos_on_right (t : ℝ) (h1 : t_inflection ≤ t) (h2 : t < 1) : K t > 0 := by
  -- By the Mean Value Theorem, since $K(t)$ is continuous on $[t, 1]$ and differentiable on $(t, 1)$, there exists some $c \in (t, 1)$ such that $K'(c) = (K(1) - K(t)) / (1 - t)$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo t 1, deriv K c = (K 1 - K t) / (1 - t) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact Continuous.continuousOn ( by exact Continuous.sub ( Continuous.sub ( Continuous.sub ( continuous_const.mul ( Real.continuous_exp.comp ( continuous_id.sub continuous_const ) ) ) ( continuous_pow 2 ) ) ( continuous_id ) ) continuous_const );
    · exact DifferentiableOn.sub ( DifferentiableOn.sub ( DifferentiableOn.sub ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.exp ( differentiableOn_id.sub ( differentiableOn_const _ ) ) ) ) ( differentiableOn_id.pow 2 ) ) ( differentiableOn_id ) ) ( differentiableOn_const _ );
  -- Since $K'(c) < 0$ for $c \in (t_inflection, 1)$, we have $(K(1) - K(t)) / (1 - t) < 0$.
  have h_deriv_neg : deriv K c < 0 := by
    exact K_deriv_neg_on_right c ( by linarith [ hc.1.1, t_inflection_in_0_1.1 ] ) ( by linarith [ hc.1.2, t_inflection_in_0_1.2 ] );
  rw [ hc.2, div_lt_iff₀ ] at h_deriv_neg <;> linarith [ K_at_one ]

/-
K is concave on [0, t_inflection].
-/
lemma K_concave_on_left : ConcaveOn ℝ (Set.Icc 0 t_inflection) K := by
  apply_rules [ concaveOn_of_deriv2_nonpos ];
  · exact convex_Icc _ _;
  · exact Continuous.continuousOn ( by unfold K; continuity );
  · exact Differentiable.differentiableOn ( by unfold K; norm_num [ Real.differentiable_exp ] );
  · exact Differentiable.differentiableOn ( by rw [ show deriv K = fun t => 3 * Real.exp ( t - 1 ) - 2 * t - 1 from funext fun t => K_deriv t ] ; norm_num [ Real.differentiableAt_exp, mul_comm ] );
  · simp +zetaDelta at *;
    exact fun x hx₁ hx₂ => by rw [ show deriv ( deriv K ) x = 3 * Real.exp ( x - 1 ) - 2 by exact K_deriv2 x ] ; exact sub_nonpos_of_le <| by rw [ show t_inflection = 1 + Real.log ( 2 / 3 ) by rfl ] at hx₂; nlinarith [ Real.log_le_sub_one_of_pos ( show 0 < 2 / 3 by norm_num ), Real.exp_le_exp.2 <| show x - 1 ≤ Real.log ( 2 / 3 ) by linarith, Real.exp_log <| show 0 < 2 / 3 by norm_num ] ;

/-
K(t) > 0 for t in (0, t_inflection].
-/
lemma K_pos_on_left (t : ℝ) (h1 : 0 < t) (h2 : t ≤ t_inflection) : K t > 0 := by
  have := K_concave_on_left.2 ( show 0 ∈ Set.Icc 0 t_inflection from ⟨ by norm_num, by linarith [ t_inflection_in_0_1.1 ] ⟩ ) ( show t_inflection ∈ Set.Icc 0 t_inflection from ⟨ by linarith [ t_inflection_in_0_1.1 ], by linarith [ t_inflection_in_0_1.2 ] ⟩ );
  -- By definition of $t_inflection$, we know that $t = \lambda \cdot 0 + (1 - \lambda) \cdot t_inflection$ for some $\lambda \in [0, 1]$.
  obtain ⟨lambda, hlambda⟩ : ∃ lambda : ℝ, 0 ≤ lambda ∧ lambda ≤ 1 ∧ t = lambda * 0 + (1 - lambda) * t_inflection := by
    exact ⟨ 1 - t / t_inflection, by nlinarith [ show 0 < t_inflection by exact lt_of_le_of_lt ( by norm_num ) ( t_inflection_in_0_1.1 ), div_mul_cancel₀ t ( show t_inflection ≠ 0 by exact ne_of_gt ( lt_of_le_of_lt ( by norm_num ) ( t_inflection_in_0_1.1 ) ) ) ], by nlinarith [ show 0 < t_inflection by exact lt_of_le_of_lt ( by norm_num ) ( t_inflection_in_0_1.1 ), div_mul_cancel₀ t ( show t_inflection ≠ 0 by exact ne_of_gt ( lt_of_le_of_lt ( by norm_num ) ( t_inflection_in_0_1.1 ) ) ) ], by nlinarith [ show 0 < t_inflection by exact lt_of_le_of_lt ( by norm_num ) ( t_inflection_in_0_1.1 ), div_mul_cancel₀ t ( show t_inflection ≠ 0 by exact ne_of_gt ( lt_of_le_of_lt ( by norm_num ) ( t_inflection_in_0_1.1 ) ) ) ] ⟩;
  have := @this ( 1 - ( 1 -lambda ) ) ( 1 -lambda ) ?_ ?_ ?_ <;> simp_all +decide [ mul_comm ];
  nlinarith [ K_at_zero_pos, show K t_inflection > 0 from by exact K_pos_on_right t_inflection ( by linarith ) ( by linarith [ t_inflection_in_0_1.2 ] ) ]

/-
K(t) > 0 for t in (0, 1).
-/
lemma K_pos_on_0_1 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : K t > 0 := by
  -- Since $t \in (0, 1)$, we can split into cases based on whether $t \leq t_{\text{inflection}}$ or $t > t_{\text{inflection}}$.
  by_cases h_cases : t ≤ t_inflection;
  · exact K_pos_on_left t ht0 h_cases;
  · exact K_pos_on_right t ( by linarith ) ( by linarith ) |> fun h => by linarith;

/-
For t in (0, 1), t^2 + t + 1 < 3 * exp(t - 1).
-/
lemma poly_lt_exp (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : t^2 + t + 1 < 3 * Real.exp (t - 1) := by
  have := K_pos_on_0_1 t ht0 ht1; norm_num [ K ] at this; linarith;

/-
Y(t) > t^2 for t in (0, 1).
-/
noncomputable def Y (t : ℝ) : ℝ := 3 * Real.exp (t - 1) - t - 1

lemma Y_gt_sq (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : Y t > t^2 := by
  have := poly_lt_exp t ht0 ht1;
  unfold Y; nlinarith [ mul_inv_cancel₀ ( ne_of_gt ht0 ), Real.exp_pos ( t - 1 ), Real.exp_neg ( t - 1 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( t - 1 ) ) ), Real.add_one_le_exp ( t - 1 ), Real.add_one_le_exp ( - ( t - 1 ) ) ] ;

/-
Derivative of Y and definition of the numerator of the derivative of F_goal.
-/
lemma Y_deriv_eq (t : ℝ) : deriv Y t = 3 * Real.exp (t - 1) - 1 := by
  unfold Y; norm_num [ Real.differentiableAt_exp, mul_comm ] ;

noncomputable def N_numerator (t : ℝ) : ℝ := (Y t)^2 - Y t + (3 * Real.exp (t - 1) - 1) * (t - Y t)

/-
Simplification of N_numerator.
-/
lemma N_numerator_eq_poly_sub_exp (t : ℝ) :
  N_numerator t = t^2 + t + 1 - 3 * Real.exp (t - 1) := by
    unfold N_numerator Y; ring;

/-
N_numerator(t) < 0 for t in (0, 1).
-/
lemma N_numerator_neg (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : N_numerator t < 0 := by
  exact N_numerator_eq_poly_sub_exp t ▸ by linarith [ poly_lt_exp t ht0 ht1 ] ;

/-
Definition of the goal function F_goal(t) = t - t/Y(t) - ln(Y(t)).
-/
noncomputable def F_goal (t : ℝ) : ℝ := t - t / Y t - Real.log (Y t)

/-
Derivative of F_goal expressed in terms of N_numerator.
-/
lemma F_goal_deriv_eq (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
  deriv F_goal t = N_numerator t / (Y t)^2 := by
    unfold N_numerator F_goal ; ring;
    by_cases h' : Y t = 0 <;> simp_all +decide [mul_assoc, mul_comm, mul_left_comm, sq];
    · have h_Y_pos : ∀ t ∈ Set.Ioo 0 1, 0 < Y t := by
        exact fun t ht => by have := Y_gt_sq t ht.1 ht.2; nlinarith [ ht.1, ht.2 ] ;
      linarith [ h_Y_pos t ⟨ ht0, ht1 ⟩ ];
    · convert HasDerivAt.deriv ( HasDerivAt.add ( hasDerivAt_id t ) ( HasDerivAt.sub ( HasDerivAt.neg ( HasDerivAt.mul ( hasDerivAt_id t ) ( HasDerivAt.inv ( hasDerivAt_deriv_iff.mpr ?_ ) h' ) ) ) ( HasDerivAt.log ( hasDerivAt_deriv_iff.mpr ?_ ) h' ) ) ) using 1 <;> norm_num [ Real.differentiableAt_exp, mul_comm, h', Y ] ; ring;
      · rw [ show deriv Y t = deriv ( fun t => 3 * Real.exp ( t - 1 ) - t - 1 ) t by rfl ] ; norm_num [ Real.differentiableAt_exp, mul_comm ] ; ring;
      · exact DifferentiableAt.sub ( DifferentiableAt.sub ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.exp ( differentiableAt_id.sub ( differentiableAt_const _ ) ) ) ) ( differentiableAt_id ) ) ( differentiableAt_const _ );
      · exact DifferentiableAt.sub ( DifferentiableAt.sub ( DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.exp ( differentiableAt_id.sub ( differentiableAt_const _ ) ) ) ) ( differentiableAt_id ) ) ( differentiableAt_const _ )

/-
Derivative of F_goal expressed in terms of N_numerator.
-/
lemma F_goal_deriv (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
  deriv F_goal t = N_numerator t / (Y t)^2 := by
    -- Apply the lemma that states the derivative of F_goal is N_numerator divided by Y^2.
    apply F_goal_deriv_eq; assumption; assumption

/-
Derivative of F_goal expressed in terms of N_numerator.
-/
lemma F_goal_deriv_new (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
  deriv F_goal t = N_numerator t / (Y t)^2 := by
    convert F_goal_deriv t ht0 ht1 using 1

/-
Derivative of F_goal expressed in terms of N_numerator.
-/
lemma F_goal_deriv_aux (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
  deriv F_goal t = N_numerator t / (Y t)^2 := by
    convert F_goal_deriv t ht0 ht1 using 1

/-
Derivative of F_goal expressed in terms of N_numerator.
-/
lemma F_goal_deriv_prop (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
  deriv F_goal t = N_numerator t / (Y t)^2 := by
    convert F_goal_deriv_aux t ht0 ht1 using 1

/-
F_goal(1) = 0.
-/
lemma F_goal_at_one : F_goal 1 = 0 := by
  unfold F_goal Y; norm_num;

/-
F_goal(t) > 0 for t in (0, 1).
-/
lemma F_goal_pos (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : F_goal t > 0 := by
  -- We know $F_{\text{goal}}'(t) < 0$ for $t \in (0, 1)$.
  have h_deriv_neg : ∀ t ∈ Set.Ioo 0 1, deriv F_goal t < 0 := by
    intros t ht
    have h_num_neg : N_numerator t < 0 := by
      exact N_numerator_neg t ht.1 ht.2
    have h_denom_pos : 0 < Y t := by
      exact Y_gt_sq t ht.1 ht.2 |> lt_of_le_of_lt ( by nlinarith [ ht.1, ht.2 ] )
    have h_deriv_neg : deriv F_goal t = N_numerator t / (Y t)^2 := by
      exact F_goal_deriv t ht.1 ht.2 ▸ rfl
    rw [h_deriv_neg]
    exact div_neg_of_neg_of_pos h_num_neg (sq_pos_of_pos h_denom_pos);
  -- By the Mean Value Theorem, since F_goal is continuous on [t,1] and differentiable on (t,1), there exists some c in (t,1) such that F_goal'(c) = (F_goal(1) - F_goal(t)) / (1 - t).
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo t 1, deriv F_goal c = (F_goal 1 - F_goal t) / (1 - t) := by
    apply_rules [ exists_deriv_eq_slope ];
    · refine' continuousOn_of_forall_continuousAt _;
      intro x hx; by_cases hx' : x = 1 <;> simp_all +decide ; (
      refine' ContinuousAt.sub _ _;
      · refine' ContinuousAt.sub continuousAt_id ( ContinuousAt.div continuousAt_id _ _ ) <;> norm_num [ Y ];
        exact ContinuousAt.sub ( ContinuousAt.sub ( continuousAt_const.mul ( Real.continuous_exp.continuousAt.comp ( continuousAt_id.sub continuousAt_const ) ) ) continuousAt_id ) continuousAt_const;
      · refine' ContinuousAt.log _ _ <;> norm_num [ Y ];
        exact ContinuousAt.sub ( ContinuousAt.sub ( continuousAt_const.mul ( Real.continuous_exp.continuousAt.comp ( continuousAt_id.sub continuousAt_const ) ) ) continuousAt_id ) continuousAt_const);
      exact DifferentiableAt.continuousAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv_neg x ( by linarith ) ( lt_of_le_of_ne ( by linarith ) hx' ) ) ) );
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv_neg x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ) ) );
  have := h_deriv_neg c ⟨ by linarith [ hc.1.1 ], by linarith [ hc.1.2 ] ⟩ ; rw [ hc.2, div_lt_iff₀ ] at this <;> try linarith;
  linarith [ show F_goal 1 = 0 by exact F_goal_at_one ]

/-
The derivative of F_goal is negative on (0, 1).
-/
lemma F_goal_deriv_neg (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : deriv F_goal t < 0 := by
  convert div_neg_of_neg_of_pos ( N_numerator_neg t ht0 ht1 ) ( sq_pos_of_pos _ ) using 1;
  convert F_goal_deriv t ht0 ht1 using 1;
  exact lt_of_le_of_lt ( by nlinarith [ Real.add_one_le_exp ( t - 1 ) ] ) ( Y_gt_sq t ht0 ht1 )

/-
If h_aux(x) < 1, then g(h_aux(x)) < g(x).
-/
lemma g_h_aux_lt_g_x (x : ℝ) (hx : 1 < x) (_ : h_aux x < 1) : g (h_aux x) < g x := by
  -- Let $t = 1 / x$. Since $x > 1$, $t \in (0, 1)$.
  set t : ℝ := 1 / x
  have ht : 0 < t ∧ t < 1 := by
    exact ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> linarith ⟩;
  -- From F_goal_pos, F_goal(t) > 0. t - t/Y(t) - ln(Y(t)) > 0.
  have h_F_goal_pos : t - t / Y t - Real.log (Y t) > 0 := by
    convert F_goal_pos t ht.1 ht.2 using 1;
  -- Since $h_aux(x) = x * Y(t)$, we can substitute this into the inequality.
  have h_subst : t - 1 / h_aux x - Real.log (h_aux x / x) > 0 := by
    convert h_F_goal_pos using 2 <;> ring;
    · unfold h_aux Y; ring;
      grind;
    · unfold h_aux Y; ring;
      rw [ show t = x⁻¹ by ring ] ; norm_num [ show x ≠ 0 by linarith ] ; ring;
  norm_num +zetaDelta at *;
  rw [ Real.log_div ] at h_subst <;> norm_num at *;
  · unfold g; ring_nf at *; linarith;
  · exact ne_of_gt ( by exact lt_of_le_of_lt ( by norm_num ) ( h_aux_pos x hx ) );
  · linarith

/-
F_goal(t) > 0 for t in (0, 1).
-/
lemma F_goal_positive (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : F_goal t > 0 := by
  apply F_goal_pos t ht0 ht1

/-
Algebraic identity: 3e^{a-1} - 1 = h_aux(x2) + x2.
-/
lemma upper_bound_eq_h_aux_add_x2 (a : ℝ) (x₂ : ℝ) (h₂ : 0 < x₂) (ha : a = g x₂) :
  3 * Real.exp (a - 1) - 1 = h_aux x₂ + x₂ := by
    unfold g h_aux at *;
    rw [ ha, add_sub_assoc ] ; ring;
    norm_num [ Real.exp_add, Real.exp_neg, Real.exp_log h₂, h₂.ne' ] ; ring

/-
Proof of part 2: 2 < x1 + x2 < 3e^{a-1} - 1.
-/
theorem part2 (a : ℝ) (x₁ x₂ : ℝ) (h₁ : 0 < x₁) (h₂ : 0 < x₂) (h_order : x₁ < x₂)
  (hx1 : IsLocalExtr (f a) x₁) (hx2 : IsLocalExtr (f a) x₂) :
  2 < x₁ + x₂ ∧ x₁ + x₂ < 3 * Real.exp (a - 1) - 1 := by
    -- By `g_decreasing_on_0_1`, we know that if $x₁ < h_aux(x₂)$, then $g(x₁) > g(h_aux(x₂))$.
    by_cases h_aux_lt : h_aux x₂ < 1
    -- Case 2.1
    have h_g_lt : g (h_aux x₂) < g x₁ := by
      have h_g_h_aux_lt_g_x : g (h_aux x₂) < g x₂ := by
        exact g_h_aux_lt_g_x x₂ (by
          exact x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2 |>.2) h_aux_lt
      exact h_g_h_aux_lt_g_x.trans_le ( by rw [ show g x₁ = a by exact critical_point_value a x₁ h₁ hx1 ] ; rw [ show g x₂ = a by exact critical_point_value a x₂ h₂ hx2 ] );
    -- By `g_decreasing_on_0_1`, we know that if $x₁ < h_aux(x₂)$, then $g(x₁) > g(h_aux(x₂))$. Hence, $x₁ < h_aux(x₂)$.
    have h_x1_lt_h_aux_x2 : x₁ < h_aux x₂ := by
      have h_g_decreasing : StrictAntiOn g (Set.Ioo 0 1) := by
        intros x hx y hy hxy;
        -- Apply the mean value theorem to the interval $[x, y]$.
        obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv g c = (g y - g x) / (y - x) := by
          apply_rules [ exists_deriv_eq_slope ];
          · exact continuousOn_of_forall_continuousAt fun z hz => by exact ContinuousAt.add ( Real.continuousAt_log ( by linarith [ hx.1, hy.1, hz.1 ] ) ) ( ContinuousAt.div continuousAt_const continuousAt_id ( by linarith [ hx.1, hy.1, hz.1 ] ) ) ;
          · exact DifferentiableOn.add ( DifferentiableOn.log ( differentiableOn_id ) ( by intro z hz; linarith [ hx.1, hy.1, hz.1 ] ) ) ( DifferentiableOn.div ( differentiableOn_const _ ) ( differentiableOn_id ) ( by intro z hz; linarith [ hx.1, hy.1, hz.1 ] ) );
        have := g_decreasing_on_0_1 c ( by linarith [ hc.1.1, hx.1 ] ) ( by linarith [ hc.1.2, hy.2 ] ) ; rw [ hc.2, div_lt_iff₀ ] at this <;> linarith;
      exact h_g_decreasing.lt_iff_gt ( ⟨ by linarith [ h_aux_pos x₂ ( by linarith [ x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2 ] ) ], by linarith [ x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2 ] ⟩ ) ( ⟨ by linarith [ x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2 ], by linarith [ x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2 ] ⟩ ) |>.1 h_g_lt;
    -- By `upper_bound_eq_h_aux_add_x2`, we know that $3 * \exp(a - 1) - 1 = h_aux(x₂) + x₂$.
    have h_upper_bound_eq : 3 * Real.exp (a - 1) - 1 = h_aux x₂ + x₂ := by
      apply upper_bound_eq_h_aux_add_x2 a x₂ h₂ (by
      exact critical_point_value a x₂ h₂ hx2 ▸ rfl);
    constructor <;> linarith [ sum_gt_two a x₁ x₂ h₁ h₂ h_order hx1 hx2 ]
    -- Case 2.2
    -- By `g_decreasing_on_0_1`, we know that if $x₁ < h_aux(x₂)$, then $g(x₁) > g(h_aux(x₂))$. Hence, we have $x₁ < h_aux(x₂)$.
    have h_x1_lt_h_aux_x2 : x₁ < 1 := by
      exact x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2 |>.1
    have h_x2_gt_1 : 1 < x₂ := by
      exact not_le.mp fun h => by exact absurd ( x1_lt_1_lt_x2 a x₁ x₂ h₁ h₂ h_order hx1 hx2 ) ( by aesop ) ;
    have h_h_aux_x2_gt_x1 : x₁ < h_aux x₂ := by
      linarith [ h_aux_pos x₂ h_x2_gt_1 ];
    -- By `upper_bound_eq_h_aux_add_x2`, we know that $3e^{a-1} - 1 = h_aux(x₂) + x₂$.
    have h_upper_bound : 3 * Real.exp (a - 1) - 1 = h_aux x₂ + x₂ := by
      convert upper_bound_eq_h_aux_add_x2 a x₂ h₂ _ using 1;
      exact Eq.symm ( critical_point_value a x₂ h₂ hx2 ) ▸ rfl;
    constructor <;> linarith [ sum_gt_two a x₁ x₂ h₁ h₂ h_order hx1 hx2 ]

/- 便于展示的别名。 -/
theorem tangent_line_at_one :
    let a := 0
    (f a 1 = tangent_line_y 1) ∧ (deriv (f a) 1 = deriv tangent_line_y 1) :=
  part1

theorem two_extrema_sum_bounds
    (a : ℝ) (x₁ x₂ : ℝ) (h₁ : 0 < x₁) (h₂ : 0 < x₂) (h_order : x₁ < x₂)
    (hx1 : IsLocalExtr (f a) x₁) (hx2 : IsLocalExtr (f a) x₂) :
    2 < x₁ + x₂ ∧ x₁ + x₂ < 3 * Real.exp (a - 1) - 1 :=
  part2 a x₁ x₂ h₁ h₂ h_order hx1 hx2

end LeanShowcase.LogExtrema
