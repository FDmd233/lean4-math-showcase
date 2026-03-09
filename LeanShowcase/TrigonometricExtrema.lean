/-!
# 三角函数极值示例

这份证明围绕表达式 `5 cos x - cos (5x)` 展开，收录了三个相互关联的结论：
区间极大值、区间内余弦上界的存在性，以及带相位偏移时最小上界的确定。
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic


open Real

open Set

-- (1) 求函数 f(x) = 5cos x - cos 5x 在区间 [0, π/4] 的最大值
theorem question1 : IsGreatest {f : ℝ | ∃ (x : ℝ), x ∈ Icc (0 : ℝ) (π/4) ∧ f = 5 * cos x - cos (5 * x)} (3 * Real.sqrt 3) := by
  -- First, we need to show that $f(x) \leq 3 \sqrt{3}$ for all $x \in [0, \frac{\pi}{4}]$.
  have upper_bound : ∀ x, x ∈ Set.Icc 0 (Real.pi / 4) → 5 * Real.cos x - Real.cos (5 * x) ≤ 3 * Real.sqrt 3 := by
    -- Let's choose any $x$ in the interval $[0, \frac{\pi}{4}]$ and derive a contradiction if $f(x) > 3\sqrt{3}$.
    intro x hx
    by_contra h_contra;
    -- Using the trigonometric identity for $\cos(5x)$, we can rewrite the inequality.
    have h_cos_5x : Real.cos (5 * x) = 16 * (Real.cos x)^5 - 20 * (Real.cos x)^3 + 5 * (Real.cos x) := by
      rw [ ( by ring : 5 * x = 2 * ( 2 * x ) + x ), Real.cos_add ] ; norm_num [ Real.sin_two_mul, Real.cos_two_mul ] ; ring;
      rw [ Real.sin_sq ] ; ring;
    -- Let $y = \cos x$. Then we have $y \in [\frac{\sqrt{2}}{2}, 1]$.
    set y : ℝ := Real.cos x
    have hy : y ∈ Set.Icc (Real.sqrt 2 / 2) 1 := by
      exact ⟨ by rw [ ← Real.cos_pi_div_four ] ; exact Real.cos_le_cos_of_nonneg_of_le_pi ( by linarith [ Set.mem_Icc.mp hx ] ) ( by linarith [ Set.mem_Icc.mp hx ] ) ( by linarith [ Set.mem_Icc.mp hx ] ), Real.cos_le_one x ⟩;
    nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), pow_two_nonneg ( y ^ 2 - 3 / 4 ), pow_two_nonneg ( y - Real.sqrt 3 / 2 ), Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), hy.1, hy.2 ];
  -- Next, we need to show that $f(x) = 3 \sqrt{3}$ for some $x \in [0, \frac{\pi}{4}]$.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ Set.Icc 0 (Real.pi / 4), 5 * Real.cos x₀ - Real.cos (5 * x₀) = 3 * Real.sqrt 3 := by
    -- Set $x₀ = \frac{\pi}{6}$ and verify that it satisfies the conditions.
    use Real.pi / 6; norm_num [Real.cos_pi_div_six, Real.cos_pi_div_four] at *; (
    exact ⟨ ⟨ by positivity, by linarith [ Real.pi_pos ] ⟩, by rw [ show 5 * ( Real.pi / 6 ) = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub ] ; norm_num ; ring ⟩);
  exact ⟨ ⟨ x₀, hx₀.1, hx₀.2.symm ⟩, by rintro _ ⟨ x, hx, rfl ⟩ ; exact upper_bound x hx ⟩

variable (θ a : ℝ)

-- (2) 给定 θ ∈ (0, π) 和 a ∈ ℝ，证明：存在 y ∈ [a-θ, a+θ]，使得 cos y ≤ cos θ
theorem question2 (hθ_left : 0 < θ) (hθ_right : θ < π) :
    ∃ (y : ℝ), y ∈ Icc (a - θ) (a + θ) ∧ cos y ≤ cos θ := by
  -- Consider two cases: θ ≤ π - θ and θ > π - θ.
  by_cases h_case : θ ≤ Real.pi - θ;
  · by_contra! h;
    -- Applying the assumption `h` to the points $a - \theta$ and $a + \theta$, we get $\cos(a - \theta) > \cos(\theta)$ and $\cos(a + \theta) > \cos(\theta)$.
    have h_cos_diff : Real.cos (a - θ) > Real.cos θ ∧ Real.cos (a + θ) > Real.cos θ := by
      exact ⟨ h _ ⟨ by linarith, by linarith ⟩, h _ ⟨ by linarith, by linarith ⟩ ⟩;
    -- Using the trigonometric identity for the sum of cosines, we have $\cos(a - \theta) + \cos(a + \theta) = 2 \cos(a) \cos(\theta)$.
    have h_cos_sum : Real.cos (a - θ) + Real.cos (a + θ) = 2 * Real.cos a * Real.cos θ := by
      rw [ Real.cos_sub, Real.cos_add ] ; ring;
    -- Since $\cos(a)$ is bounded by $-1$ and $1$, we have $2 \cos(a) \cos(\theta) \leq 2 \cos(\theta)$.
    have h_cos_bound : 2 * Real.cos a * Real.cos θ ≤ 2 * Real.cos θ := by
      exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right zero_le_two ( Real.cos_le_one a ) ) ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith, by linarith ⟩ );
    linarith;
  · -- Since $θ > π - θ$, we have $π - θ < θ$. Therefore, there exists some integer $k$ such that $a - θ ≤ 2kπ - θ ≤ a + θ$ or $a - θ ≤ 2kπ + θ ≤ a + θ$.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, a - θ ≤ 2 * k * Real.pi + θ ∧ 2 * k * Real.pi + θ ≤ a + θ ∨ a - θ ≤ 2 * k * Real.pi - θ ∧ 2 * k * Real.pi - θ ≤ a + θ := by
      by_contra h_contra;
      push_neg at h_contra;
      have := h_contra ⌊ ( a - θ ) / ( 2 * Real.pi ) ⌋; have := h_contra ( ⌊ ( a - θ ) / ( 2 * Real.pi ) ⌋ + 1 ) ; norm_num at *;
      by_cases h : a ≤ 2 * ⌊ ( a - θ ) / ( 2 * Real.pi ) ⌋ * Real.pi <;> simp_all +decide;
      · nlinarith [ Int.floor_le ( ( a - θ ) / ( 2 * Real.pi ) ), Int.lt_floor_add_one ( ( a - θ ) / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ ( a - θ ) ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ];
      · have := this.1 ( by nlinarith [ Int.floor_le ( ( a - θ ) / ( 2 * Real.pi ) ), Int.lt_floor_add_one ( ( a - θ ) / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ ( a - θ ) ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ] );
        by_cases h : a ≤ 2 * ⌊ ( a - θ ) / ( 2 * Real.pi ) ⌋ * Real.pi + θ + θ <;> simp_all +decide;
        · linarith [ h_contra ⌊ ( a - θ ) / ( 2 * Real.pi ) ⌋ |>.1 h ];
        · nlinarith [ Int.floor_le ( ( a - θ ) / ( 2 * Real.pi ) ), Int.lt_floor_add_one ( ( a - θ ) / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ ( a - θ ) ( by positivity : ( 2 * Real.pi ) ≠ 0 ), ‹a ≤ 2 * ( ( ⌊ ( a - θ ) / ( 2 * Real.pi ) ⌋ : ℝ ) + 1 ) * Real.pi → a + θ < 2 * ( ( ⌊ ( a - θ ) / ( 2 * Real.pi ) ⌋ : ℝ ) + 1 ) * Real.pi - θ› ( by linarith ) ];
    cases hk <;> [ refine' ⟨ 2 * k * Real.pi + θ, ⟨ by linarith, by linarith ⟩, _ ⟩ ; refine' ⟨ 2 * k * Real.pi - θ, ⟨ by linarith, by linarith ⟩, _ ⟩ ] <;> simp +decide [ mul_assoc, mul_left_comm ];
    norm_num [ add_comm, Real.cos_add ];
    norm_num [ show Real.sin ( k * ( 2 * Real.pi ) ) = 0 from Real.sin_eq_zero_iff.mpr ⟨ k * 2, by push_cast; ring ⟩ ]

-- (3) 设 b ∈ ℝ，若存在 φ ∈ ℝ 使得 5cos x - cos(5x + φ) ≤ b 对 x ∈ ℝ 恒成立，求 b 的最小值
noncomputable section PhaseShiftLemmas

/-
Formula for cos(5x) in terms of cos(x).
-/
lemma cos_five_x (x : ℝ) : cos (5 * x) = 16 * cos x ^ 5 - 20 * cos x ^ 3 + 5 * cos x := by
  rw [ ( by ring : 5 * x = 2 * ( 2 * x ) + x ), Real.cos_add ] ; norm_num [ Real.cos_two_mul, Real.sin_two_mul ] ; ring;
  rw [ Real.sin_sq ] ; ring;

/-
The function 5cos(x) - cos(5x) is bounded by 3sqrt(3).
-/
lemma question3_upper_bound_at_zero (x : ℝ) : 5 * cos x - cos (5 * x) ≤ 3 * Real.sqrt 3 := by
  rw [ show 5 * x = 2 * ( 2 * x ) + x by ring, Real.cos_add ] ; norm_num [ Real.sin_two_mul, Real.cos_two_mul ] ; ring_nf;
  by_cases hx : 0 ≤ Real.cos x;
  · rw [ Real.sin_sq ] ; ring_nf;
    nlinarith [ sq_nonneg ( Real.cos x ^ 2 - 3 / 4 ), mul_self_nonneg ( Real.cos x ^ 2 - 1 / 2 ), Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three, pow_two_nonneg ( Real.cos x - Real.sqrt 3 / 2 ), pow_two_nonneg ( Real.cos x + Real.sqrt 3 / 2 ) ];
  · nlinarith [ sq_nonneg ( Real.cos x ), Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three, mul_le_mul_of_nonneg_left ( Real.neg_one_le_cos x ) ( sq_nonneg ( Real.cos x ) ) ]

/-
For any phase shift phi, the maximum value of the function is at least 3sqrt(3).
-/
lemma question3_lower_bound (φ : ℝ) : ∃ x, 5 * cos x - cos (5 * x + φ) ≥ 3 * Real.sqrt 3 := by
  -- Let's choose $k \in \mathbb{Z}$ such that $\phi' = \phi - 2k\pi \in [0, 2\pi]$.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 0 ≤ φ - 2 * k * Real.pi ∧ φ - 2 * k * Real.pi ≤ 2 * Real.pi := by
    exact ⟨ ⌊φ / ( 2 * Real.pi ) ⌋, by nlinarith [ Int.floor_le ( φ / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ φ ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ], by nlinarith [ Int.lt_floor_add_one ( φ / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ φ ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ] ⟩;
  -- Let $x = (\pi - \phi')/6$.
  set x := (Real.pi - (φ - 2 * k * Real.pi)) / 6;
  -- Then $x \in [-\pi/6, \pi/6]$, so $\cos x \ge \sqrt{3}/2$.
  have hx_cos : Real.cos x ≥ Real.sqrt 3 / 2 := by
    rw [ ← Real.cos_abs ] ; exact Real.cos_pi_div_six ▸ Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith ) ( by cases abs_cases ( ( Real.pi - ( φ - 2 * k * Real.pi ) ) / 6 ) <;> linarith ) ;
  -- Also $5x + \phi = 5x + \phi' + 2k\pi$.
  have h_cos_eq : Real.cos (5 * x + φ) = -Real.cos x := by
    rw [ ← Real.cos_pi_sub ] ; ring;
    convert Real.cos_periodic.int_mul k _ using 2 ; ring;
  exact ⟨ x, by linarith ⟩

end PhaseShiftLemmas

theorem question3 : IsLeast {b : ℝ | ∃ (φ : ℝ), ∀ (x : ℝ), 5 * cos x - cos (5 * x + φ) ≤ b} (3 * Real.sqrt 3) := by
  refine' ⟨ _, fun b hb => _ ⟩;
  · exact ⟨ 0, fun x => by simpa using question3_upper_bound_at_zero x ⟩;
  · obtain ⟨ φ, hφ ⟩ := hb; exact le_of_not_gt fun h => by obtain ⟨ x, hx ⟩ := question3_lower_bound φ; linarith [ hφ x ] ;
/- 便于展示的别名。 -/
theorem trig_maximum_on_Icc :
    IsGreatest {f : ℝ | ∃ (x : ℝ), x ∈ Icc (0 : ℝ) (π / 4) ∧ f = 5 * cos x - cos (5 * x)}
      (3 * Real.sqrt 3) :=
  question1

theorem cosine_interval_witness (θ a : ℝ) (hθ_left : 0 < θ) (hθ_right : θ < π) :
    ∃ y : ℝ, y ∈ Icc (a - θ) (a + θ) ∧ cos y ≤ cos θ :=
  question2 (θ := θ) (a := a) hθ_left hθ_right

theorem least_phase_shift_upper_bound :
    IsLeast {b : ℝ | ∃ (φ : ℝ), ∀ x : ℝ, 5 * cos x - cos (5 * x + φ) ≤ b}
      (3 * Real.sqrt 3) :=
  question3