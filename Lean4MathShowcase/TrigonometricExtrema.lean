import Mathlib

open Real Set

noncomputable section

/-!
# Three Trigonometric Optimization Problems

## Problem 1
Find the maximum of f(x) = 5cos(x) - cos(5x) on [0, π/4], and prove it equals 3√3.

## Problem 2
Given θ ∈ (0, π) and any real a, prove ∃ y ∈ [a-θ, a+θ] such that cos(y) ≤ cos(θ).

## Problem 3
If ∃ φ such that 5cos(x) - cos(5x + φ) ≤ b for all x ∈ ℝ, find the minimum value of b.
Answer: 3√3.
-/

/-! ### Auxiliary lemmas for Problem 1 -/

/-- The Chebyshev identity: cos(5x) = 16cos⁵(x) - 20cos³(x) + 5cos(x) -/
lemma cos_five_mul (x : ℝ) :
    cos (5 * x) = 16 * (cos x) ^ 5 - 20 * (cos x) ^ 3 + 5 * cos x := by
  rw [show 5 * x = 2 * (2 * x) + x by ring, Real.cos_add]
  norm_num [Real.cos_two_mul, Real.sin_two_mul]; ring
  rw [Real.sin_sq]; ring

/-- f(x) = 5cos(x) - cos(5x) = 4cos³(x)(5 - 4cos²(x)) -/
lemma f_eq_poly (x : ℝ) :
    5 * cos x - cos (5 * x) = 4 * (cos x) ^ 3 * (5 - 4 * (cos x) ^ 2) := by
  rw [(by ring : 5 * x = 2 * (2 * x) + x), Real.cos_add]
  norm_num [Real.sin_two_mul, Real.cos_two_mul]; ring
  rw [Real.sin_sq]; ring

/-- The value at x = π/6 equals 3√3 -/
lemma f_val_pi_div_six :
    5 * cos (π / 6) - cos (5 * (π / 6)) = 3 * √3 := by
  rw [show 5 * (Real.pi / 6) = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub]
  norm_num; ring

/-- The upper bound: f(x) ≤ 3√3 for all x ∈ [0, π/4] -/
lemma f_upper_bound (x : ℝ) (hx : x ∈ Icc 0 (π / 4)) :
    5 * cos x - cos (5 * x) ≤ 3 * √3 := by
  rw [f_eq_poly x, mul_comm]
  have h_am_gm : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 → (5 - 4 * t ^ 2) * (4 * t ^ 3) ≤ 3 * Real.sqrt 3 := by
    intro t ht
    nlinarith [mul_nonneg ht.left (sq_nonneg (2 * t ^ 2 - 3 / 2)),
               Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three]
  exact h_am_gm _ ⟨Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos, hx.1], by linarith [Real.pi_pos, hx.2]⟩, Real.cos_le_one _⟩

/-! ### Problem 1: Maximum of 5cos(x) - cos(5x) on [0, π/4] -/

/-- **Problem 1**: The maximum of 5cos(x) - cos(5x) on [0, π/4] is 3√3. -/
theorem problem1_max :
    IsGreatest ((fun x => 5 * cos x - cos (5 * x)) '' Icc 0 (π / 4)) (3 * √3) := by
  constructor
  · exact ⟨π / 6, ⟨⟨by linarith [pi_pos], by linarith [pi_pos]⟩, f_val_pi_div_six⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact f_upper_bound x hx

/-! ### Problem 2: Existence of y with cos(y) ≤ cos(θ) -/

/-- **Problem 2**: For θ ∈ (0,π) and any a, there exists y ∈ [a-θ, a+θ] with cos(y) ≤ cos(θ).

The proof splits into two cases:
- **cos(θ) ≥ 0**: The endpoints a±θ satisfy cos(a+θ) + cos(a-θ) = 2cos(a)cos(θ),
  so min(cos(a+θ), cos(a-θ)) ≤ cos(a)cos(θ) ≤ cos(θ).
- **cos(θ) < 0**: The interval has length 2θ > π, so it contains a multiple nπ.
  If n is odd, cos(nπ) = −1 ≤ cos(θ). If n is even, an endpoint argument applies. -/
theorem problem2 (θ : ℝ) (hθ : θ ∈ Ioo 0 π) (a : ℝ) :
    ∃ y ∈ Icc (a - θ) (a + θ), cos y ≤ cos θ := by
  by_cases hcosθ : Real.cos θ ≥ 0
  · have h_cos_sum : Real.cos (a + θ) + Real.cos (a - θ) = 2 * Real.cos a * Real.cos θ := by
      linarith [Real.cos_add a θ, Real.cos_sub a θ]
    exact if h : Real.cos a ≤ 1 then
      ⟨if Real.cos (a + θ) ≤ Real.cos (a - θ) then a + θ else a - θ,
       by split_ifs <;> constructor <;> linarith [hθ.1, hθ.2],
       by split_ifs <;> nlinarith [Real.cos_sq' a, Real.cos_sq' θ]⟩
    else
      ⟨a, ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.1, hθ.2]⟩,
       by nlinarith [Real.cos_sq' a, Real.cos_sq' θ]⟩
  · by_contra h_contra
    obtain ⟨n, hn⟩ : ∃ n : ℤ, a - θ ≤ n * Real.pi ∧ n * Real.pi ≤ a + θ := by
      have h_length : 2 * θ > Real.pi :=
        not_le.mp fun h => hcosθ <| Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩
      exact ⟨⌈(a - θ) / Real.pi⌉,
        by nlinarith [Int.le_ceil ((a - θ) / Real.pi), Real.pi_pos,
                       mul_div_cancel₀ (a - θ) Real.pi_ne_zero],
        by nlinarith [Int.ceil_lt_add_one ((a - θ) / Real.pi), Real.pi_pos,
                       mul_div_cancel₀ (a - θ) Real.pi_ne_zero]⟩
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
      simp_all +decide [add_mul, mul_assoc, mul_left_comm]
    · by_cases h_case : a + θ ≥ k * (2 * Real.pi) + θ
      · have := h_contra (k * (2 * Real.pi) + θ) (by linarith) (by linarith)
        simp_all +decide [Real.cos_add]
        norm_num [show Real.sin (k * (2 * Real.pi)) = 0 from
          Real.sin_eq_zero_iff.mpr ⟨k * 2, by push_cast; ring⟩] at this
      · have := h_contra (k * (2 * Real.pi) - θ) (by linarith) (by linarith)
        simp_all +decide [Real.cos_sub, mul_assoc]
        norm_num [show Real.sin (k * (2 * Real.pi)) = 0 from
          Real.sin_eq_zero_iff.mpr ⟨k * 2, by push_cast; ring⟩] at this
    · have := h_contra (↑k * (2 * Real.pi) + Real.pi) (by linarith) (by linarith)
      simp_all +decide [Real.cos_add]
      linarith [Real.neg_one_le_cos θ]

/-! ### Auxiliary lemmas for Problem 3 -/

/-- For φ = 0, the bound 3√3 works for all x. -/
lemma problem3_achievable :
    ∀ x : ℝ, 5 * cos x - cos (5 * x + 0) ≤ 3 * √3 := by
  intro x
  by_cases h_cos : Real.cos x ≥ 0
  · have h_max : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 4 * t ^ 3 * (5 - 4 * t ^ 2) ≤ 3 * Real.sqrt 3 := by
      intro t ht₁ ht₂
      nlinarith [sq_nonneg (t ^ 2 - 3 / 4), mul_nonneg ht₁ (sq_nonneg (t - Real.sqrt 3 / 2)),
                 Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three]
    convert h_max (Real.cos x) h_cos (Real.cos_le_one x) using 1
    rw [show 5 * x = 2 * (2 * x) + x by ring]
    norm_num [Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul]; ring
    rw [Real.sin_sq]; ring
  · norm_num [(by ring : 5 * x = 2 * (2 * x) + x), Real.cos_add, Real.cos_two_mul,
              Real.sin_two_mul] at *
    ring_nf at *
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three, Real.sin_sq_add_cos_sq x,
               pow_two_nonneg (Real.sin x * Real.cos x), pow_two_nonneg (Real.sin x ^ 2),
               pow_two_nonneg (Real.cos x ^ 2)]

/-- Among 6 equally spaced points (spacing π/3), cos achieves ≥ √3/2 at one of them. -/
lemma exists_cos_ge (α : ℝ) : ∃ n : ℤ, cos (α + n * (π / 3)) ≥ √3 / 2 := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, |α + n * (Real.pi / 3)| ≤ Real.pi / 6 :=
    ⟨-⌊(3 * α + Real.pi / 2) / Real.pi⌋, by
      rw [abs_le]; constructor <;> push_cast <;>
        nlinarith [Int.floor_le ((3 * α + Real.pi / 2) / Real.pi),
                   Int.lt_floor_add_one ((3 * α + Real.pi / 2) / Real.pi),
                   Real.pi_pos, mul_div_cancel₀ (3 * α + Real.pi / 2) Real.pi_ne_zero]⟩
  exact ⟨n, by
    rw [← Real.cos_pi_div_six, ← Real.cos_abs (α + n * (Real.pi / 3))]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by linarith [Real.pi_pos, abs_le.mp hn]) (by linarith [Real.pi_pos, abs_le.mp hn])⟩

/-- cos(nπ - x) = -cos(x) when n is odd. -/
lemma cos_odd_mul_pi_sub (x : ℝ) (n : ℤ) (hn : ¬Even n) :
    cos (↑n * π - x) = -cos x := by
  simp +zetaDelta at *
  obtain ⟨k, rfl⟩ := hn
  norm_num [add_mul, mul_assoc, mul_left_comm, Real.cos_sub]
  exact Or.inl (Real.sin_eq_zero_iff.mpr ⟨k * 2, by push_cast; ring⟩)

/-- The lower bound: for any φ, the supremum of 5cos(x) - cos(5x+φ) is at least 3√3.

**Proof sketch**: For any φ, consider the critical points x₀ = ((2n+1)π − φ)/6.
At such points, 5x₀ + φ = (2n+1)π − x₀, so cos(5x₀+φ) = −cos(x₀),
giving F(x₀) = 6cos(x₀). By choosing n so that cos(x₀) ≥ √3/2
(which is always possible since the x₀ are π/3-spaced), we get F ≥ 3√3. -/
lemma problem3_lower_bound (b : ℝ) (φ : ℝ)
    (h : ∀ x : ℝ, 5 * cos x - cos (5 * x + φ) ≤ b) :
    b ≥ 3 * √3 := by
  set α := (Real.pi - φ) / 6
  obtain ⟨n, hn⟩ := exists_cos_ge α
  set x₀ := α + n * (Real.pi / 3) with hx₀_def
  have hx₀ : x₀ = ((2 * n + 1) * Real.pi - φ) / 6 := by ring
  have h_cos_eq : Real.cos (5 * x₀ + φ) = -Real.cos x₀ := by
    rw [← Real.cos_pi_sub, hx₀]; ring
    convert Real.cos_periodic.int_mul n _ using 2; ring
  linarith [h x₀]

/-! ### Problem 3: Minimum b -/

/-- **Problem 3**: The minimum b such that ∃ φ, ∀ x, 5cos(x) − cos(5x+φ) ≤ b is 3√3. -/
theorem problem3_min :
    IsLeast {b : ℝ | ∃ φ : ℝ, ∀ x : ℝ, 5 * cos x - cos (5 * x + φ) ≤ b} (3 * √3) := by
  constructor
  · exact ⟨0, problem3_achievable⟩
  · intro b ⟨φ, hφ⟩
    exact problem3_lower_bound b φ hφ

end
