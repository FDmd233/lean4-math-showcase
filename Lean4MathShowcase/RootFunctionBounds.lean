import Mathlib

open Real Set

noncomputable section

/-- The function f(a, x) = 1/√(1+x) + 1/√(1+a) + √(ax/(ax+8)) -/
def f (a x : ℝ) : ℝ :=
  1 / sqrt (1 + x) + 1 / sqrt (1 + a) + sqrt (a * x / (a * x + 8))

/-! ## Part 2: Two-sided estimate 1 < f(a,x) < 2

We prove this first since Part 1 uses some similar techniques.
-/

/-! ### Lower bound: f(a,x) > 1

**Proof strategy:**
1. Show 1/(1+t) < 1/√(1+t) for t > 0
2. Show √s > s for s ∈ (0,1)
3. Show 1/(1+x) + 1/(1+a) + ax/(ax+8) ≥ 1 (polynomial inequality)
4. Combine to get f > 1
-/

/-
PROBLEM
The key polynomial inequality: a²x + ax² - 6ax + 8 ≥ 0 for a, x > 0.
This follows from AM-GM: ax(6-a-x) ≤ (a+x)²(6-a-x)/4 ≤ 8.

PROVIDED SOLUTION
Split into cases: if a + x ≥ 6 then a²x + ax² - 6ax + 8 = ax(a+x-6) + 8 ≥ 0+8 > 0. If a + x < 6, then: (1) by AM-GM (a-x)² ≥ 0, so 4ax ≤ (a+x)². (2) Let s = a+x, then s²(6-s) ≤ 32 because s³-6s²+32 = (s-4)²(s+2) ≥ 0 for s > 0. So ax(6-a-x) ≤ s²(6-s)/4 ≤ 8, hence a²x+ax²-6ax+8 = 8-ax(6-a-x) ≥ 0.
-/
lemma poly_nonneg (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    0 ≤ a ^ 2 * x + a * x ^ 2 - 6 * a * x + 8 := by
  by_cases h : a + x ≥ 6;
  · nlinarith [ sq_nonneg ( a - x ), mul_pos ha hx ];
  · nlinarith [ sq_nonneg ( a - x ), mul_pos ha hx, mul_pos ha ( sub_pos_of_lt hx ), mul_pos hx ( sub_pos_of_lt ha ), sq_nonneg ( a + x - 4 ) ]

/-
PROBLEM
The rational lower bound: 1/(1+x) + 1/(1+a) + ax/(ax+8) ≥ 1

PROVIDED SOLUTION
We need 1/(1+x) + 1/(1+a) + ax/(ax+8) ≥ 1, equivalently the numerator (a²x + ax² - 6ax + 8) / ((1+x)(1+a)(ax+8)) ≥ 0. Use poly_nonneg and clear denominators with field_simp. All denominators are positive: 1+x > 0, 1+a > 0, ax+8 > 0.
-/
lemma rational_lower_bound (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    1 ≤ 1 / (1 + x) + 1 / (1 + a) + a * x / (a * x + 8) := by
  rw [ div_add_div, div_add_div, le_div_iff₀ ] <;> nlinarith [ mul_pos ha hx, poly_nonneg a x ha hx ]

/-
PROBLEM
1/(1+t) < 1/√(1+t) for t > 0

PROVIDED SOLUTION
For t > 0: 1/(1+t) < 1/√(1+t) iff √(1+t) < 1+t iff (1+t)^2 > 1+t iff t(1+t) > 0, which is true since t > 0. Use div_lt_div_of_pos_left (1 is positive) with sqrt(1+t) < 1+t. For sqrt(1+t) < 1+t: since 1+t > 1 > 0, we have (1+t)^2 = 1+2t+t^2 > 1+t, so sqrt(1+t) < 1+t by Real.sqrt_lt_self or Real.sqrt_lt'.
-/
lemma inv_lt_inv_sqrt (t : ℝ) (ht : 0 < t) :
    1 / (1 + t) < 1 / sqrt (1 + t) := by
  gcongr ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + t by linarith ) ]

/-
PROBLEM
√s > s for s ∈ (0,1)

PROVIDED SOLUTION
For s ∈ (0,1): s < √s iff s² < s iff s(s-1) < 0, true since 0 < s < 1. Use Real.lt_sqrt (with hs0 for s ≥ 0) to reduce to s^2 < s, then nlinarith.
-/
lemma sqrt_gt_self (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    s < sqrt s := by
  exact Real.lt_sqrt_of_sq_lt ( by nlinarith )

/-
PROBLEM
ax/(ax+8) ∈ (0,1) for a, x > 0

PROVIDED SOLUTION
Since a*x > 0 and a*x + 8 > 0, the fraction is positive.
-/
lemma ax_frac_pos (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    0 < a * x / (a * x + 8) := by
  positivity

/-
PROVIDED SOLUTION
ax/(ax+8) < 1 because ax < ax + 8 since 8 > 0.
-/
lemma ax_frac_lt_one (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    a * x / (a * x + 8) < 1 := by
  rw [ div_lt_iff₀ ] <;> nlinarith

/-
PROBLEM
**Part 2, Lower Bound**: f(a,x) > 1 for all a, x > 0

PROVIDED SOLUTION
We show f(a,x) > 1 by showing each term of f is strictly greater than the corresponding term of 1/(1+x) + 1/(1+a) + ax/(ax+8), and the sum of the latter is ≥ 1.

Specifically:
- 1/sqrt(1+x) > 1/(1+x) by inv_lt_inv_sqrt
- 1/sqrt(1+a) > 1/(1+a) by inv_lt_inv_sqrt
- sqrt(ax/(ax+8)) > ax/(ax+8) by sqrt_gt_self applied to ax/(ax+8) ∈ (0,1), using ax_frac_pos and ax_frac_lt_one
- 1/(1+x) + 1/(1+a) + ax/(ax+8) ≥ 1 by rational_lower_bound

So f > 1/(1+x) + 1/(1+a) + ax/(ax+8) ≥ 1.
-/
theorem f_gt_one (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : 1 < f a x := by
  unfold f;
  -- Apply the three inequalities for each term of f.
  have h1 : 1 / Real.sqrt (1 + x) > 1 / (1 + x) := by
    gcongr ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + x by positivity ) ]
  have h2 : 1 / Real.sqrt (1 + a) > 1 / (1 + a) := by
    gcongr ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + a by positivity ) ]
  have h3 : Real.sqrt (a * x / (a * x + 8)) > a * x / (a * x + 8) := by
    exact Real.lt_sqrt_of_sq_lt ( by nlinarith [ show 0 < a * x / ( a * x + 8 ) by positivity, show a * x / ( a * x + 8 ) < 1 by rw [ div_lt_one ( by positivity ) ] ; linarith ] );
  linarith [ rational_lower_bound a x ha hx ]

/-! ### Upper bound: f(a,x) < 2

**Proof strategy:**
Show each term is < 1, but more precisely show f < 2 directly.
Key insight: 1/√(1+t) < (2+t)/(2(1+t)) and √s < (s+1)/2,
then combine with the polynomial inequality.
-/

/-
PROBLEM
Core polynomial inequality for the upper bound.
With substitution p = u-1, q = v-1 where u = √(1+x), v = √(1+a):
8·(p+q+2pq)² + pq(p+2)(q+2)·(pq-1)·(1+2p+2q+3pq) > 0

PROVIDED SOLUTION
Split into two cases using `by_cases h : p * q ≥ 1`.

Case 1 (p*q ≥ 1): All factors in the second term are nonneg (p*q*(p+2)*(q+2) > 0, p*q-1 ≥ 0, 1+2*p+2*q+3*p*q > 0), so the second term ≥ 0. The first term 8*(p+q+2*p*q)^2 > 0. Use `positivity` or `nlinarith [sq_nonneg (p+q+2*p*q)]` with `mul_pos`.

Case 2 (p*q < 1): Use `push_neg at h` to get h : p*q < 1. Need:
8*(p+q+2*p*q)^2 > p*q*(p+2)*(q+2)*(1-p*q)*(1+2*p+2*q+3*p*q)

Key insight: (p+q+2*p*q)^2 ≥ (p+q)^2 + 4*p*q*(p+q) + 4*p^2*q^2 (expand).

Try nlinarith with these auxiliary terms:
- sq_nonneg (p - q)
- sq_nonneg (p*q)
- sq_nonneg (p + q)
- sq_nonneg (p * (1 - q))
- sq_nonneg (q * (1 - p))
- mul_pos hp hq
- sq_nonneg (1 - p*q)
- mul_pos (show 0 < p + 2 by linarith) (show 0 < q + 2 by linarith)
- sq_nonneg (p*q*(p+q))
- sq_nonneg (p^2*q - p*q^2)

Use nlinarith (config := { maxDegree := 4 }) with all these hints.
-/
lemma upper_bound_poly (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    8 * (p + q + 2 * p * q) ^ 2 +
    p * q * (p + 2) * (q + 2) * (p * q - 1) * (1 + 2 * p + 2 * q + 3 * p * q) > 0 := by
  by_contra h_contra;
  by_cases h : p * q ≥ 1;
  · exact h_contra <| by exact add_pos_of_pos_of_nonneg ( by positivity ) <| mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) <| by positivity ) <| by positivity ) <| by nlinarith ) <| by positivity;
  · have := mul_pos hp hq;
    nlinarith only [ this, h, h_contra, sq_nonneg ( p - q ), mul_pos this hp, mul_pos this hq, mul_pos ( mul_pos this hp ) hq, mul_pos ( mul_pos ( mul_pos this hp ) hq ) this, mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) hp, mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) hq, mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) ( mul_pos this hp ), mul_pos ( mul_pos ( mul_pos ( mul_pos this hp ) hq ) this ) ( mul_pos this hq ) ]

/-
PROBLEM
**Part 2, Upper Bound**: f(a,x) < 2 for all a, x > 0

PROVIDED SOLUTION
Set u = sqrt(1+x), v = sqrt(1+a). Then u > 1, v > 1 (since x, a > 0). Set p = u-1 > 0, q = v-1 > 0.

Step 1: Show 1/sqrt(1+x) < 1 and 1/sqrt(1+a) < 1, so 2-A-B > 0 where A = 1/sqrt(1+x), B = 1/sqrt(1+a).

Step 2: It suffices to show C < 2-A-B where C = sqrt(ax/(ax+8)). Since both sides are positive, square: C² < (2-A-B)².

Step 3: C² = ax/(ax+8). Express ax = (u²-1)(v²-1) = p(p+2)q(q+2) and ax+8 in terms of u, v.
(2-A-B) = 2-1/u-1/v = (2uv-u-v)/(uv). So (2-A-B)² = (2uv-u-v)²/(u²v²).

Step 4: Need ax/(ax+8) < (2uv-u-v)²/(u²v²).
Cross-multiply (both denominators positive): ax·u²v² < (2uv-u-v)²·(ax+8).
This rearranges to: (2uv-u-v)²·(ax+8) - u²v²·ax > 0.
= (2uv-u-v)²·ax + 8·(2uv-u-v)² - u²v²·ax
= ax·((2uv-u-v)² - u²v²) + 8·(2uv-u-v)²

Note (2uv-u-v)² - u²v² = (2uv-u-v-uv)(2uv-u-v+uv) = (uv-u-v)(3uv-u-v).

So we need: ax·(uv-u-v)·(3uv-u-v) + 8·(2uv-u-v)² > 0.

With p = u-1, q = v-1: uv-u-v = pq-1, 3uv-u-v = 1+2p+2q+3pq, 2uv-u-v = p+q+2pq, ax = pq(p+2)(q+2).

This becomes: pq(p+2)(q+2)(pq-1)(1+2p+2q+3pq) + 8(p+q+2pq)² > 0.

This is exactly upper_bound_poly p q. Apply the lemma.

For the implementation:
1. Set u := sqrt(1+x), v := sqrt(1+a).
2. Have hu : 1 < u, hv : 1 < v.
3. Have u² = 1+x from sq_sqrt, and v² = 1+a.
4. Show f a x = 1/u + 1/v + sqrt(ax/(ax+8)).
5. Show 2 - 1/u - 1/v > 0.
6. Show (2-1/u-1/v)² > ax/(ax+8) using upper_bound_poly.
7. Conclude f < 2.

Note: the key step is showing the squared inequality and then taking square roots. Use Real.sqrt_lt' to go from C² < D² to C < D (when D > 0).
-/
theorem f_lt_two (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : f a x < 2 := by
  -- Set u := sqrt(1+x), v := sqrt(1+a).
  set u : ℝ := Real.sqrt (1 + x)
  set v : ℝ := Real.sqrt (1 + a);
  -- Set p = u-1 > 0, q = v-1 > 0.
  set p : ℝ := u - 1
  set q : ℝ := v - 1
  have hp : 0 < p := by
    exact sub_pos_of_lt <| Real.lt_sqrt_of_sq_lt <| by linarith;
  have hq : 0 < q := by
    exact sub_pos_of_lt <| Real.lt_sqrt_of_sq_lt <| by linarith;
  -- Show 2 - 1/u - 1/v > 0.
  have h_pos : 2 - 1 / u - 1 / v > 0 := by
    exact sub_pos_of_lt ( by nlinarith [ show 1 / u < 1 from by rw [ div_lt_one ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; exact Real.lt_sqrt_of_sq_lt ( by linarith ), show 1 / v < 1 from by rw [ div_lt_one ( Real.sqrt_pos.mpr ( by linarith ) ) ] ; exact Real.lt_sqrt_of_sq_lt ( by linarith ) ] );
  -- Show (2-1/u-1/v)² > ax/(ax+8) using upper_bound_poly.
  have h_sq : (2 - 1 / u - 1 / v) ^ 2 > a * x / (a * x + 8) := by
    -- Substitute $u = \sqrt{1+x}$ and $v = \sqrt{1+a}$ into the inequality.
    have h_sub : (2 - 1 / u - 1 / v) ^ 2 = (2 * u * v - u - v) ^ 2 / (u ^ 2 * v ^ 2) := by
      field_simp [u, v]
      ring;
    -- Substitute $u$ and $v$ into the inequality.
    have h_ineq : (2 * u * v - u - v) ^ 2 * (a * x + 8) > u ^ 2 * v ^ 2 * a * x := by
      -- Substitute $u$ and $v$ into the inequality and simplify.
      have h_ineq : (2 * u * v - u - v) ^ 2 * (a * x + 8) - u ^ 2 * v ^ 2 * a * x = p * q * (p + 2) * (q + 2) * (p * q - 1) * (1 + 2 * p + 2 * q + 3 * p * q) + 8 * (p + q + 2 * p * q) ^ 2 := by
        rw [ show a = ( v ^ 2 - 1 ) by rw [ Real.sq_sqrt <| by positivity ] ; ring, show x = ( u ^ 2 - 1 ) by rw [ Real.sq_sqrt <| by positivity ] ; ring ] ; ring;
      linarith [ upper_bound_poly p q hp hq ];
    rw [ h_sub, gt_iff_lt, div_lt_div_iff₀ ] <;> first | positivity | linarith;
  -- Taking square roots on both sides of the inequality, we get $2 - 1/u - 1/v > \sqrt{ax/(ax+8)}$.
  have h_sqrt : 2 - 1 / u - 1 / v > Real.sqrt (a * x / (a * x + 8)) := by
    exact Real.sqrt_lt' h_pos |>.2 h_sq;
  unfold f; ring_nf at *; linarith;

/-! ## Part 1: Monotonicity of f(8, ·)

When a = 8, f(8, x) = (1 + √x)/√(1+x) + 1/3.
The key algebraic identity for comparing g(x₁) vs g(x₂) where
g(x) = (1 + √x)/√(1+x):

√x₁(1+x₂) - √x₂(1+x₁) = (√x₁ - √x₂)(1 - √(x₁x₂))
-/

/-
PROBLEM
When a = 8, simplify 8x/(8x+8) = x/(x+1)

PROVIDED SOLUTION
8x/(8x+8) = 8x/(8(x+1)) = x/(x+1). Use field_simp and ring.
-/
lemma eight_x_simplify (x : ℝ) (hx : 0 < x) :
    8 * x / (8 * x + 8) = x / (x + 1) := by
  rw [ div_eq_div_iff ] <;> linarith

/-
PROBLEM
When a = 8, f(8, x) = (1 + √x)/√(1+x) + 1/3

PROVIDED SOLUTION
Unfold f, simplify 1/sqrt(1+8) = 1/sqrt(9) = 1/3. Use eight_x_simplify to get 8x/(8x+8) = x/(x+1). Then sqrt(x/(x+1)) = sqrt(x)/sqrt(x+1). So f 8 x = 1/sqrt(1+x) + 1/3 + sqrt(x)/sqrt(1+x) = (1 + sqrt(x))/sqrt(1+x) + 1/3.
-/
lemma f8_eq (x : ℝ) (hx : 0 < x) :
    f 8 x = (1 + sqrt x) / sqrt (1 + x) + 1 / 3 := by
  unfold f; norm_num; ring;
  -- Simplify the expression under the square root.
  field_simp
  ring;
  rw [ ← Real.sqrt_mul ( by positivity ) ];
  rw [ mul_left_comm, mul_inv_cancel₀ ( by positivity ), mul_one ]

/-
PROBLEM
The function g(x) = (1 + √x)/√(1+x) is strictly increasing on (0, 1]

PROVIDED SOLUTION
For x₁, x₂ ∈ (0,1] with x₁ < x₂, show g(x₁) < g(x₂) where g(x) = (1+√x)/√(1+x).

Key algebraic identity: √x₁(1+x₂) - √x₂(1+x₁) = (√x₁ - √x₂)(1 - √(x₁x₂)).

Since x₁ < x₂: √x₁ < √x₂, so first factor < 0.
Since x₁ < x₂ ≤ 1: x₁·x₂ < 1, so √(x₁x₂) < 1, so second factor > 0.
Product < 0, so √x₁(1+x₂) < √x₂(1+x₁).

This means (1+√x₁)²(1+x₂) < (1+√x₂)²(1+x₁) (expand and simplify: the cross terms give 2√x₁(1+x₂) < 2√x₂(1+x₁), and the other terms cancel).

Then (1+√x₁)/√(1+x₁) < (1+√x₂)/√(1+x₂) by taking square roots and dividing.
-/
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

/-
PROBLEM
The function g(x) = (1 + √x)/√(1+x) is strictly decreasing on [1, ∞)

PROVIDED SOLUTION
For x₁, x₂ ∈ [1,∞) with x₁ < x₂, show g(x₁) > g(x₂) where g(x) = (1+√x)/√(1+x).

Key algebraic identity: √x₁(1+x₂) - √x₂(1+x₁) = (√x₁ - √x₂)(1 - √(x₁x₂)).

Since x₁ < x₂: √x₁ < √x₂, so first factor < 0.
Since x₁ ≥ 1 and x₂ > 1: x₁·x₂ > 1, so √(x₁x₂) > 1, so second factor < 0.
Product > 0, so √x₁(1+x₂) > √x₂(1+x₁).

This means (1+√x₁)²(1+x₂) > (1+√x₂)²(1+x₁) (same expansion argument).

Then (1+√x₁)/√(1+x₁) > (1+√x₂)/√(1+x₂).
-/
lemma g_strictAntiOn :
    StrictAntiOn (fun x => (1 + sqrt x) / sqrt (1 + x)) (Ici 1) := by
  norm_num [ StrictAntiOn ];
  intro a ha b hb hab;
  -- Squaring both sides to remove the square roots.
  suffices h_sq : ((1 + Real.sqrt b) / Real.sqrt (1 + b))^2 < ((1 + Real.sqrt a) / Real.sqrt (1 + a))^2 by
    contrapose! h_sq; gcongr;
  field_simp;
  -- Cancel out common terms:
  suffices h_simp : 2 * Real.sqrt b * (1 + a) < 2 * Real.sqrt a * (1 + b) by
    rw [ Real.sq_sqrt, Real.sq_sqrt ] <;> nlinarith [ Real.mul_self_sqrt ( show 0 ≤ a by linarith ), Real.mul_self_sqrt ( show 0 ≤ b by linarith ), Real.mul_self_sqrt ( show 0 ≤ 1 + a by linarith ), Real.mul_self_sqrt ( show 0 ≤ 1 + b by linarith ) ];
  nlinarith [ mul_le_mul_of_nonneg_left hb <| Real.sqrt_nonneg a, mul_le_mul_of_nonneg_left ha <| Real.sqrt_nonneg b, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.mul_self_sqrt ( by linarith : 0 ≤ a ), Real.mul_self_sqrt ( by linarith : 0 ≤ b ), Real.sqrt_lt_sqrt ( by linarith ) hab ]

/-
PROBLEM
**Part 1**: f(8, ·) is strictly increasing on (0, 1]

PROVIDED SOLUTION
Use f8_eq to rewrite f 8 x = (1+sqrt x)/sqrt(1+x) + 1/3 for x in Ioc 0 1. Since adding 1/3 is a monotone operation, the strict monotonicity of f 8 on Ioc 0 1 follows from g_strictMonoOn (strict monotonicity of g(x) = (1+sqrt x)/sqrt(1+x) on Ioc 0 1).
-/
theorem f8_strictMonoOn : StrictMonoOn (f 8) (Ioc 0 1) := by
  intros x hx y hy hxy;
  -- Using the definition of f 8 and the fact that g is strictly increasing on (0, 1], we get f 8 x < f 8 y.
  have h_g_mono : (1 + Real.sqrt x) / Real.sqrt (1 + x) < (1 + Real.sqrt y) / Real.sqrt (1 + y) := by
    exact g_strictMonoOn hx hy hxy;
  convert add_lt_add_right h_g_mono ( 1 / 3 ) using 1;
  · convert f8_eq x hx.1 using 1 ; 
  · convert f8_eq y hy.1 using 1 ;

/-
PROBLEM
**Part 1**: f(8, ·) is strictly decreasing on [1, ∞)

PROVIDED SOLUTION
Use f8_eq to rewrite f 8 x = (1+sqrt x)/sqrt(1+x) + 1/3 for x in Ici 1. Since adding 1/3 preserves strict anti-monotonicity, and g_strictAntiOn gives strict anti-monotonicity of g on Ici 1, the result follows. Note: Ici 1 ⊆ {x | 0 < x} so f8_eq applies.
-/
theorem f8_strictAntiOn : StrictAntiOn (f 8) (Ici 1) := by
  intros x hx y hy hxy;
  rw [ f8_eq x ( lt_of_lt_of_le zero_lt_one hx ), f8_eq y ( lt_of_lt_of_le zero_lt_one hy ) ];
  have := g_strictAntiOn ( show 1 ≤ x from hx ) ( show 1 ≤ y from hy ) hxy ; aesop;

end