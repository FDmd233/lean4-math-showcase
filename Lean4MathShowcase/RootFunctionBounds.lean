import Mathlib

open Real Set

noncomputable section

/-- The function f(a, x) = 1/√(1+x) + 1/√(1+a) + √(ax/(ax+8)) -/
def f (a x : ℝ) : ℝ :=
  1 / sqrt (1 + x) + 1 / sqrt (1 + a) + sqrt (a * x / (a * x + 8))

/-! ## Part 2: Two-sided estimate `1 < f(a,x) < 2`

I start with the two-sided estimate because the same inequalities are useful again in the monotonicity argument.
-/

/-! ### Lower bound

The comparison is elementary: replace the three square-root terms by slightly smaller rational expressions and reduce the remaining inequality to `poly_nonneg`.
-/

lemma poly_nonneg (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    0 ≤ a ^ 2 * x + a * x ^ 2 - 6 * a * x + 8 := by
  by_cases h : a + x ≥ 6;
  · nlinarith [ sq_nonneg ( a - x ), mul_pos ha hx ];
  · nlinarith [ sq_nonneg ( a - x ), mul_pos ha hx, mul_pos ha ( sub_pos_of_lt hx ), mul_pos hx ( sub_pos_of_lt ha ), sq_nonneg ( a + x - 4 ) ]

lemma rational_lower_bound (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    1 ≤ 1 / (1 + x) + 1 / (1 + a) + a * x / (a * x + 8) := by
  rw [ div_add_div, div_add_div, le_div_iff₀ ] <;> nlinarith [ mul_pos ha hx, poly_nonneg a x ha hx ]

lemma inv_lt_inv_sqrt (t : ℝ) (ht : 0 < t) :
    1 / (1 + t) < 1 / sqrt (1 + t) := by
  gcongr ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + t by linarith ) ]

lemma sqrt_gt_self (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    s < sqrt s := by
  exact Real.lt_sqrt_of_sq_lt ( by nlinarith )

lemma ax_frac_pos (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    0 < a * x / (a * x + 8) := by
  positivity

lemma ax_frac_lt_one (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    a * x / (a * x + 8) < 1 := by
  rw [ div_lt_iff₀ ] <;> nlinarith

theorem f_gt_one (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : 1 < f a x := by
  unfold f;
  have h1 : 1 / Real.sqrt (1 + x) > 1 / (1 + x) := by
    gcongr ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + x by positivity ) ]
  have h2 : 1 / Real.sqrt (1 + a) > 1 / (1 + a) := by
    gcongr ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + a by positivity ) ]
  have h3 : Real.sqrt (a * x / (a * x + 8)) > a * x / (a * x + 8) := by
    exact Real.lt_sqrt_of_sq_lt ( by nlinarith [ show 0 < a * x / ( a * x + 8 ) by positivity, show a * x / ( a * x + 8 ) < 1 by rw [ div_lt_one ( by positivity ) ] ; linarith ] );
  linarith [ rational_lower_bound a x ha hx ]

/-! ### Upper bound

For the upper estimate I use `u = √(1+x)` and `v = √(1+a)`, then reduce the square-root inequality to the polynomial statement `upper_bound_poly`.
-/

lemma upper_bound_poly (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    8 * (p + q + 2 * p * q) ^ 2 +
    p * q * (p + 2) * (q + 2) * (p * q - 1) * (1 + 2 * p + 2 * q + 3 * p * q) > 0 := by
  by_contra h_contra;
  by_cases h : p * q ≥ 1;
  · exact h_contra <| by exact add_pos_of_pos_of_nonneg ( by positivity ) <| mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) <| by positivity ) <| by positivity ) <| by nlinarith ) <| by positivity;
  · have := mul_pos hp hq;
    nlinarith only [ this, h, h_contra, sq_nonneg ( p - q ), mul_pos this hp, mul_pos this hq, mul_pos ( mul_pos this hp ) hq, mul_pos ( mul_pos ( mul_pos this hp ) hq ) this, mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) hp, mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) hq, mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) ( mul_pos this hp ), mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) ( mul_pos this hq ) ]

theorem f_lt_two (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : f a x < 2 := by
  set u : ℝ := Real.sqrt (1 + x)
  set v : ℝ := Real.sqrt (1 + a);
  set p : ℝ := u - 1
  set q : ℝ := v - 1
  have hp : 0 < p := by
    exact sub_pos_of_lt <| Real.lt_sqrt_of_sq_lt <| by linarith;
  have hq : 0 < q := by
    exact sub_pos_of_lt <| Real.lt_sqrt_of_sq_lt <| by linarith;
  have h_pos : 2 - 1 / u - 1 / v > 0 := by
    exact sub_pos_of_lt ( by nlinarith [ show 1 / u < 1 from by rw [ div_lt_one ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; exact Real.lt_sqrt_of_sq_lt ( by linarith ), show 1 / v < 1 from by rw [ div_lt_one ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; exact Real.lt_sqrt_of_sq_lt ( by linarith ) ] );
  have h_sq : (2 - 1 / u - 1 / v) ^ 2 > a * x / (a * x + 8) := by
    have h_sub : (2 - 1 / u - 1 / v) ^ 2 = (2 * u * v - u - v) ^ 2 / (u ^ 2 * v ^ 2) := by
      field_simp [u, v]
      ring;
    have h_ineq : (2 * u * v - u - v) ^ 2 * (a * x + 8) > u ^ 2 * v ^ 2 * a * x := by
      have h_ineq : (2 * u * v - u - v) ^ 2 * (a * x + 8) - u ^ 2 * v ^ 2 * a * x = p * q * (p + 2) * (q + 2) * (p * q - 1) * (1 + 2 * p + 2 * q + 3 * p * q) + 8 * (p + q + 2 * p * q) ^ 2 := by
        rw [ show a = ( v ^ 2 - 1 ) by rw [ Real.sq_sqrt <| by positivity ] ; ring, show x = ( u ^ 2 - 1 ) by rw [ Real.sq_sqrt <| by positivity ] ; ring ] ; ring;
      linarith [ upper_bound_poly p q hp hq ];
    rw [ h_sub, gt_iff_lt, div_lt_div_iff₀ ] <;> first | positivity | linarith;
  have h_sqrt : 2 - 1 / u - 1 / v > Real.sqrt (a * x / (a * x + 8)) := by
    exact Real.sqrt_lt' h_pos |>.2 h_sq;
  unfold f; ring_nf at *; linarith;

/-! ## Part 1: Monotonicity of f(8, ·)

When a = 8, f(8, x) = (1 + √x)/√(1+x) + 1/3.
The key algebraic identity for comparing g(x₁) vs g(x₂) where
g(x) = (1 + √x)/√(1+x):

√x₁(1+x₂) - √x₂(1+x₁) = (√x₁ - √x₂)(1 - √(x₁x₂))
-/

lemma eight_x_simplify (x : ℝ) (hx : 0 < x) :
    8 * x / (8 * x + 8) = x / (x + 1) := by
  rw [ div_eq_div_iff ] <;> linarith

lemma f8_eq (x : ℝ) (hx : 0 < x) :
    f 8 x = (1 + sqrt x) / sqrt (1 + x) + 1 / 3 := by
  unfold f; norm_num; ring;
  field_simp
  ring;
  rw [ ← Real.sqrt_mul ( by positivity ) ];
  rw [ mul_left_comm, mul_inv_cancel₀ ( by positivity ), mul_one ]

lemma g_strictMonoOn :
    StrictMonoOn (fun x => (1 + sqrt x) / sqrt (1 + x)) (Ioc 0 1) := by
  intros x hx y hy hxy
  have h_sqrt : Real.sqrt x < Real.sqrt y := by
    rw [ Real.sqrt_lt_sqrt_iff ] <;> linarith [ hx.1, hy.1 ]
  have h_sqrt_prod : Real.sqrt (x * y) < 1 := by
    rw [ Real.sqrt_lt' ] <;> nlinarith [ hx.1, hx.2, hy.1, hy.2 ]
  have h_cross : (Real.sqrt x - Real.sqrt y) * (1 - Real.sqrt (x * y)) < 0 := by
    exact mul_neg_of_neg_of_pos ( sub_neg_of_lt h_sqrt ) ( sub_pos_of_lt h_sqrt_prod )
  have h_expand : (1 + Real.sqrt x)^2 * (1 + y) < (1 + Real.sqrt y)^2 * (1 + x) := by
    rw [ Real.sqrt_mul hx.1.le ] at * ; nlinarith [ Real.mul_self_sqrt hx.1.le, Real.mul_self_sqrt hy.1.le ] ;
  have h_div : (1 + Real.sqrt x) / Real.sqrt (1 + x) < (1 + Real.sqrt y) / Real.sqrt (1 + y) := by
    rw [ div_lt_div_iff₀ ];
    · nlinarith [ show 0 < ( 1 + Real.sqrt y ) * Real.sqrt ( 1 + x ) by exact mul_pos ( by positivity ) ( Real.sqrt_pos.mpr ( by linarith [ hx.1 ] ) ), show 0 < ( 1 + Real.sqrt x ) * Real.sqrt ( 1 + y ) by exact mul_pos ( by positivity ) ( Real.sqrt_pos.mpr ( by linarith [ hy.1 ] ) ), Real.mul_self_sqrt ( by linarith [ hx.1 ] : 0 ≤ 1 + x ), Real.mul_self_sqrt ( by linarith [ hy.1 ] : 0 ≤ 1 + y ) ];
    · exact Real.sqrt_pos.mpr ( by linarith [ hx.1 ] );
    · exact Real.sqrt_pos.mpr ( by linarith [ hy.1 ] )
  exact h_div

lemma g_strictAntiOn :
    StrictAntiOn (fun x => (1 + sqrt x) / sqrt (1 + x)) (Ici 1) := by
  norm_num [ StrictAntiOn ];
  intro a ha b hb hab;
  suffices h_sq : ((1 + Real.sqrt b) / Real.sqrt (1 + b))^2 < ((1 + Real.sqrt a) / Real.sqrt (1 + a))^2 by
    contrapose! h_sq; gcongr;
  field_simp;
  suffices h_simp : 2 * Real.sqrt b * (1 + a) < 2 * Real.sqrt a * (1 + b) by
    rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> nlinarith [ Real.mul_self_sqrt ( show 0 ≤ a by linarith ), Real.mul_self_sqrt ( show 0 ≤ b by linarith ), Real.mul_self_sqrt ( show 0 ≤ 1 + a by linarith ), Real.mul_self_sqrt ( show 0 ≤ 1 + b by linarith ) ];
  nlinarith [ mul_le_mul_of_nonneg_left hb <| Real.sqrt_nonneg a, mul_le_mul_of_nonneg_left ha <| Real.sqrt_nonneg b, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.mul_self_sqrt ( by linarith : 0 ≤ a ), Real.mul_self_sqrt ( by linarith : 0 ≤ b ), Real.sqrt_lt_sqrt ( by linarith ) hab ]

theorem f8_strictMonoOn : StrictMonoOn (f 8) (Ioc 0 1) := by
  intros x hx y hy hxy;
  have h_g_mono : (1 + Real.sqrt x) / Real.sqrt (1 + x) < (1 + Real.sqrt y) / Real.sqrt (1 + y) := by
    exact g_strictMonoOn hx hy hxy;
  convert add_lt_add_right h_g_mono ( 1 / 3 ) using 1;
  · convert f8_eq x hx.1 using 1 ; 
  · convert f8_eq y hy.1 using 1 ;

theorem f8_strictAntiOn : StrictAntiOn (f 8) (Ici 1) := by
  intros x hx y hy hxy;
  rw [ f8_eq x ( lt_of_lt_of_le zero_lt_one hx ), f8_eq y ( lt_of_lt_of_le zero_lt_one hy ) ];
  have := g_strictAntiOn ( show 1 ≤ x from hx ) ( show 1 ≤ y from hy ) hxy ; aesop;

end