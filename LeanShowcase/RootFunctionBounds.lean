/-!
# 根式函数的单调性与估计

这里研究函数
`f(a, x) = 1 / sqrt(1 + x) + 1 / sqrt(1 + a) + sqrt((a * x) / (a * x + 8))`。
文件证明了 `a = 8` 时的分段单调性，以及任意 `a > 0, x > 0` 时的双边估计 `1 < f(a, x) < 2`。
-/
import Mathlib

namespace LeanShowcase.RootFunctionBounds

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
The function f(x) = 1/sqrt(1+x) + 1/sqrt(1+a) + sqrt(ax/(ax+8)) defined for x > 0.
-/
noncomputable def f (a : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 + x) + 1 / Real.sqrt (1 + a) + Real.sqrt ((a * x) / (a * x + 8))

/-
The function g(u) = u + sqrt(1-u^2) + 1/3 is strictly increasing on (0, 1/sqrt(2)].
-/
noncomputable def g (u : ℝ) : ℝ := u + Real.sqrt (1 - u ^ 2) + 1 / 3

theorem g_increasing : StrictMonoOn g (Set.Ioc 0 (1 / Real.sqrt 2)) := by
  unfold StrictMonoOn g;
  norm_num +zetaDelta at *;
  intro a ha₁ ha₂ b hb₁ hb₂ hab;
  -- We'll use that $a < b$ to show that $a + \sqrt{1 - a^2} < b + \sqrt{1 - b^2}$.
  have h_sqrt : Real.sqrt (1 - a^2) < Real.sqrt (1 - b^2) + (b - a) := by
    rw [ Real.sqrt_lt' ];
    · -- Since $a < b$, we have $1 - b^2 < 1 - a^2$, and thus $\sqrt{1 - b^2} > \sqrt{1 - a^2}$.
      have h_sqrt : Real.sqrt (1 - b^2) > a := by
        exact Real.lt_sqrt_of_sq_lt ( by nlinarith [ inv_mul_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, inv_pow ( Real.sqrt 2 ) 2 ] );
      nlinarith [ Real.sqrt_nonneg ( 1 - b ^ 2 ), Real.mul_self_sqrt ( show 0 ≤ 1 - b ^ 2 by exact sub_nonneg.2 <| by exact pow_le_one₀ hb₁.le <| hb₂.trans <| inv_le_one_of_one_le₀ <| Real.le_sqrt_of_sq_le <| by norm_num ) ];
    · exact add_pos_of_nonneg_of_pos ( Real.sqrt_nonneg _ ) ( sub_pos.mpr hab );
  linarith

/-
The function g(u) = u + sqrt(1-u^2) + 1/3 is strictly decreasing on [1/sqrt(2), 1).
-/
theorem g_decreasing : StrictAntiOn g (Set.Ico (1 / Real.sqrt 2) 1) := by
  -- Compute the derivative of $g(u)$ and show it is negative on $(1 / \sqrt{2}, 1)$.
  have h_deriv_neg : ∀ u ∈ Set.Ioo (1 / Real.sqrt 2) 1, deriv g u < 0 := by
    -- By definition of $g$, we know that its derivative is $g'(u) = 1 - u / \sqrt{1 - u^2}$.
    have h_deriv : ∀ u ∈ Set.Ioo (1 / Real.sqrt 2) 1, deriv g u = 1 - u / Real.sqrt (1 - u^2) := by
      intro u hu;
      convert HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.add ( hasDerivAt_id u ) ( HasDerivAt.sqrt ( HasDerivAt.const_sub 1 ( hasDerivAt_pow 2 u ) ) _ ) ) ( hasDerivAt_const _ _ ) ) using 1 <;> norm_num ; ring;
      nlinarith [ hu.1, hu.2, show 0 < u by exact lt_trans ( by positivity ) hu.1 ];
    simp +zetaDelta at *;
    intro u hu₁ hu₂; rw [ h_deriv u hu₁ hu₂ ] ; rw [ sub_neg ] ; rw [ lt_div_iff₀ ] <;> norm_num;
    · rw [ Real.sqrt_lt' ] <;> nlinarith [ inv_pos.2 <| Real.sqrt_pos.2 zero_lt_two, mul_inv_cancel₀ <| ne_of_gt <| Real.sqrt_pos.2 zero_lt_two, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, inv_pow ( Real.sqrt 2 ) 2 ];
    · rwa [ abs_of_pos ( lt_trans ( by positivity ) hu₁ ) ];
  norm_num +zetaDelta at *;
  -- By the Mean Value Theorem, if the derivative of $g$ is negative on $(1 / \sqrt{2}, 1)$, then $g$ is strictly decreasing on $[1 / \sqrt{2}, 1)$.
  have h_mvt : ∀ x y : ℝ, 1 / Real.sqrt 2 ≤ x → x < y → y < 1 → ∃ c ∈ Set.Ioo x y, deriv g c = (g y - g x) / (y - x) := by
    intros x y hx hy h1; apply_rules [ exists_deriv_eq_slope ];
    · exact continuousOn_of_forall_continuousAt fun u hu => by exact ContinuousAt.add ( ContinuousAt.add continuousAt_id <| Real.continuous_sqrt.continuousAt.comp <| continuousAt_const.sub <| continuousAt_id.pow 2 ) <| continuousAt_const;
    · exact fun u hu => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv_neg u ( by exact lt_of_le_of_lt ( by simpa using hx ) hu.1 ) ( by exact hu.2.trans_le <| by linarith ) ) ) );
  intro x hx y hy hxy; have := h_mvt x y ( by simpa using hx.1 ) hxy ( by simpa using hy.2 ) ; obtain ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ := this; have := h_deriv_neg c ( by simpa using hxc.trans_le' hx.1 ) ( by simpa using hcy.trans_le hy.2.le ) ; rw [ hcd, div_lt_iff₀ ] at this <;> linarith;

/-
For x > 0, f(8, x) = g(1/sqrt(1+x)).
-/
lemma f_eq_g (x : ℝ) (hx : 0 < x) : f 8 x = g (1 / Real.sqrt (1 + x)) := by
  unfold f g; ring_nf;
  grind

/-
Define u(x) = 1/sqrt(1+x). u is strictly decreasing on (0, infinity).
-/
noncomputable def u (x : ℝ) : ℝ := 1 / Real.sqrt (1 + x)

theorem u_decreasing : StrictAntiOn u (Set.Ioi 0) := by
  exact fun x hx y hy hxy => by exact one_div_lt_one_div_of_lt ( Real.sqrt_pos.mpr <| by linarith [ hx.out ] ) <| Real.sqrt_lt_sqrt ( by linarith [ hx.out ] ) <| by linarith [ hx.out, hy.out ] ;

/-
u maps (0, 1] to [1/sqrt(2), 1).
-/
theorem u_range_part1 : Set.MapsTo u (Set.Ioc 0 1) (Set.Ico (1 / Real.sqrt 2) 1) := by
  intro x hx;
  -- By definition of $u$, we know that $u(x) = 1 / \sqrt{1 + x}$.
  rw [u];
  exact ⟨ one_div_le_one_div_of_le ( Real.sqrt_pos.2 <| by linarith [ hx.1 ] ) <| Real.sqrt_le_sqrt <| by linarith [ hx.2 ], by rw [ div_lt_iff₀ ] <;> nlinarith [ hx.1, hx.2, Real.sqrt_nonneg ( 1 + x ), Real.sq_sqrt <| show 0 ≤ 1 + x by linarith [ hx.1 ] ] ⟩

/-
u maps [1, infinity) to (0, 1/sqrt(2)].
-/
theorem u_range_part2 : Set.MapsTo u (Set.Ici 1) (Set.Ioc 0 (1 / Real.sqrt 2)) := by
  exact fun x hx => ⟨ by exact one_div_pos.2 <| Real.sqrt_pos.2 <| by linarith [ Set.mem_Ici.1 hx ], by exact one_div_le_one_div_of_le ( Real.sqrt_pos.2 ( by norm_num ) ) <| Real.sqrt_le_sqrt <| by linarith [ Set.mem_Ici.1 hx ] ⟩

/-
When a = 8, f(x) is strictly increasing on (0, 1].
-/
theorem part1_increasing : StrictMonoOn (f 8) (Set.Ioc 0 1) := by
  -- By combining the results from h_chain1 and h_chain2, we conclude that $f(8)$ is strictly increasing on $(0, 1]$.
  intros x hx y hy hxy;
  -- By definition of $f(8)$, we know that $f(8, x) = g(u(x))$ where $u(x) = 1/\sqrt{1+x}$.
  have h_eq_g1 : f 8 x = g (u x) := by
    exact f_eq_g x hx.1
  have h_eq_g2 : f 8 y = g (u y) := by
    exact f_eq_g y hy.1;
  -- Since $u$ is strictly decreasing on $(0, \infty)$, we have $u(x) > u(y)$.
  have h_u_decreasing : u x > u y := by
    exact one_div_lt_one_div_of_lt ( Real.sqrt_pos.mpr ( by linarith [ hx.1, hy.1 ] ) ) ( Real.sqrt_lt_sqrt ( by linarith [ hx.1, hy.1 ] ) ( by linarith [ hx.1, hy.1 ] ) );
  -- Since $u(x)$ and $u(y)$ are in $[1/\sqrt{2}, 1)$, we can apply the strict decreasing property of $g$ on this interval.
  have h_g_decreasing : u x ∈ Set.Ico (1 / Real.sqrt 2) 1 ∧ u y ∈ Set.Ico (1 / Real.sqrt 2) 1 := by
    exact ⟨ ⟨ by simpa using u_range_part1 hx |>.1, by simpa using u_range_part1 hx |>.2 ⟩, ⟨ by simpa using u_range_part1 hy |>.1, by simpa using u_range_part1 hy |>.2 ⟩ ⟩;
  exact h_eq_g1.symm ▸ h_eq_g2.symm ▸ g_decreasing h_g_decreasing.2 h_g_decreasing.1 h_u_decreasing

/-
When a = 8, f(x) is strictly decreasing on [1, infinity).
-/
theorem part1_decreasing : StrictAntiOn (f 8) (Set.Ici 1) := by
  -- From u_range_part2, u(x) and u(y) are in (0, 1/sqrt(2)].
  have hu_range : ∀ x ∈ Set.Ici 1, u x ∈ Set.Ioc 0 (1 / Real.sqrt 2) := by
    exact fun x hx => u_range_part2 hx;
  -- From g_increasing, g is strictly increasing on (0, 1/sqrt(2)].
  have h_g_increasing : StrictMonoOn g (Set.Ioc 0 (1 / Real.sqrt 2)) := by
    exact g_increasing;
  -- Since $f(8, t) = g(u(t))$, we have $f(8, x) > f(8, y)$.
  have h_f_gt_f : ∀ x y : ℝ, 1 ≤ x → x < y → f 8 y < f 8 x := by
    intros x y hx hy
    have h_u_gt : u x > u y := by
      exact one_div_lt_one_div_of_lt ( Real.sqrt_pos.mpr ( by linarith ) ) ( Real.sqrt_lt_sqrt ( by linarith ) ( by linarith ) );
    convert h_g_increasing ( hu_range y <| Set.mem_Ici.mpr <| by linarith ) ( hu_range x <| Set.mem_Ici.mpr hx ) h_u_gt using 1 <;> rw [ f_eq_g ];
    · unfold u; ring;
    · linarith;
    · unfold u; ring;
    · linarith;
  exact fun x hx y hy hxy => h_f_gt_f x y hx hxy

/-
For any a > 0 and x > 0, f(a, x) > 1.
-/
theorem part2_lower (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 < x) : 1 < f a x := by
  -- Applying the AM-GM inequality to each term, we get:
  have h1 : 1 / Real.sqrt (1 + x) > 1 / (1 + x / 2) := by
    exact one_div_lt_one_div_of_lt ( by positivity ) ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + x by positivity ) ] )
  have h2 : 1 / Real.sqrt (1 + a) > 1 / (1 + a / 2) := by
    exact one_div_lt_one_div_of_lt ( by positivity ) ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + a by positivity ) ] )
  have h3 : Real.sqrt (a * x / (a * x + 8)) > 2 * a * x / (a * x + 8 + a * x) := by
    exact Real.lt_sqrt_of_sq_lt ( by rw [ div_pow, div_lt_div_iff₀ ] <;> nlinarith [ mul_pos ha hx, sq_nonneg ( a * x - 8 ) ] );
  refine' lt_of_le_of_lt _ ( add_lt_add ( add_lt_add h1 h2 ) h3 );
  rw [ div_add_div, div_add_div, le_div_iff₀ ] <;> try positivity;
  nlinarith [ sq_nonneg ( a * x - 4 ), mul_pos ha hx ]

/-
For any a > 0 and x > 0, f(a, x) < 2.
-/
theorem part2_upper (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 < x) : f a x < 2 := by
  -- Notice that $\frac{1}{\sqrt{1+x}} < 1$ and $\frac{1}{\sqrt{1+a}} < 1$.
  have h_fractions : 1 / Real.sqrt (1 + x) < 1 ∧ 1 / Real.sqrt (1 + a) < 1 := by
    exact ⟨ by simpa using inv_lt_one_of_one_lt₀ <| Real.lt_sqrt_of_sq_lt <| by linarith, by simpa using inv_lt_one_of_one_lt₀ <| Real.lt_sqrt_of_sq_lt <| by linarith ⟩;
  -- We need to show that $\sqrt{\frac{ax}{ax+8}} < 2 - \frac{1}{\sqrt{1+x}} - \frac{1}{\sqrt{1+a}}$.
  suffices h_sqrt : Real.sqrt ((a * x) / (a * x + 8)) < 2 - 1 / Real.sqrt (1 + x) - 1 / Real.sqrt (1 + a) by
    convert add_lt_add_left h_sqrt ( 1 / Real.sqrt ( 1 + x ) + 1 / Real.sqrt ( 1 + a ) ) using 1 ; ring;
  rw [ Real.sqrt_lt' ];
  · -- Now use algebra to simplify the inequality.
    field_simp at *;
    rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ) ];
    -- Let's simplify the expression by setting $u = \sqrt{1 + x}$ and $v = \sqrt{1 + a}$.
    set u := Real.sqrt (1 + x)
    set v := Real.sqrt (1 + a);
    -- Substitute $u$ and $v$ back into the inequality.
    have h_sub : (u^2 - 1) * (v^2 - 1) * u^2 * v^2 < ((u^2 - 1) * (v^2 - 1) + 8) * ((2 * u - 1) * v - u)^2 := by
      -- Since $u$ and $v$ are greater than 1, we can use the fact that $(u - 1)(v - 1) > 0$ to simplify the inequality.
      have h_pos : (u - 1) * (v - 1) > 0 := by
        nlinarith;
      nlinarith [ mul_pos h_pos ( sq_pos_of_pos ( sub_pos.mpr h_fractions.1 ) ), mul_pos h_pos ( sq_pos_of_pos ( sub_pos.mpr h_fractions.2 ) ), mul_pos h_pos ( mul_pos ( sub_pos.mpr h_fractions.1 ) ( sub_pos.mpr h_fractions.2 ) ), mul_pos h_pos ( mul_pos ( sub_pos.mpr h_fractions.1 ) ( sq_pos_of_pos ( sub_pos.mpr h_fractions.2 ) ) ), mul_pos h_pos ( mul_pos ( sub_pos.mpr h_fractions.2 ) ( sq_pos_of_pos ( sub_pos.mpr h_fractions.1 ) ) ) ];
    rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ) ] at h_sub ; linarith;
  · linarith
/- 便于展示的别名。 -/
theorem a8_increasing_on_Ioc : StrictMonoOn (f 8) (Set.Ioc 0 1) :=
  part1_increasing

theorem a8_decreasing_on_Ici : StrictAntiOn (f 8) (Set.Ici 1) :=
  part1_decreasing

theorem root_function_gt_one (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : 1 < f a x :=
  part2_lower a ha x hx

theorem root_function_lt_two (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : f a x < 2 :=
  part2_upper a ha x hx

end LeanShowcase.RootFunctionBounds
