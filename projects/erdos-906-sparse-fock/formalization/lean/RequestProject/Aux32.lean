import RequestProject.TwoTerm
import RequestProject.Radii

/-!
# Auxiliary estimates for the `p = 3/2` covering argument

Elementary real-analytic inequalities and the arithmetic of the sparse support
`ν_j = ⌊j^{3/2}⌋` used in the annular covering theorem.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-! ### Elementary auxiliary estimates -/

/-- `exp (-x) ≤ 256 / x ^ 4` for `x > 0`. -/
theorem exp_neg_le_inv_pow_four {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 256 / x ^ 4 := by
  have h1 : x / 4 ≤ Real.exp (x / 4) := by
    have := Real.add_one_le_exp (x / 4)
    linarith
  have h2 : (x / 4) ^ 4 ≤ (Real.exp (x / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (Real.exp (x / 4)) ^ 4 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h3] at h2
  have h4 : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  rw [inv_le_iff_one_le_mul₀ h4, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h2]

/-- `1 - exp (-x) ≥ x / 2` for `0 ≤ x ≤ 1`. -/
theorem one_sub_exp_neg_ge {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : (0:ℝ) < Real.exp x := Real.exp_pos x
  have h4 : 1 / Real.exp x ≤ 1 / (x + 1) := one_div_le_one_div_of_le (by linarith) h1
  have h5 : 1 / (x + 1) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < x + 1)]
    nlinarith
  rw [Real.exp_neg, ← one_div]
  linarith

/-- `exp x - 1 ≤ 3 x` for `0 ≤ x ≤ 1`. -/
theorem exp_sub_one_le_three_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 3 * x := by
  have hpos : (0:ℝ) < Real.exp x := Real.exp_pos x
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h2 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : Real.exp x ≤ 3 := by
    have hle : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.2 hx1
    linarith [Real.exp_one_lt_d9]
  have h4 : (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_right h1 hpos.le
  rw [h2] at h4
  nlinarith

/-! ### The `p = 3/2` support arithmetic -/

theorem rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : x ^ ((3:ℝ)/2) = x * Real.sqrt x := by
  rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- `ν_j ≤ j √j` for `p = 3/2`. -/
theorem nu32_le (j : ℕ) : ((nu (3/2) j : ℕ) : ℝ) ≤ (j : ℝ) * Real.sqrt j := by
  have h := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg j) ((3:ℝ)/2))
  have he : (j : ℝ) ^ ((3:ℝ)/2) = (j : ℝ) * Real.sqrt j :=
    rpow_three_halves _ (Nat.cast_nonneg j)
  simp only [nu]
  rw [← he]
  exact h

/-- `j √j - 1 ≤ ν_j` for `p = 3/2`. -/
theorem le_nu32 (j : ℕ) : (j : ℝ) * Real.sqrt j - 1 ≤ ((nu (3/2) j : ℕ) : ℝ) := by
  have h := Nat.lt_floor_add_one ((j : ℝ) ^ ((3:ℝ)/2))
  have he : (j : ℝ) ^ ((3:ℝ)/2) = (j : ℝ) * Real.sqrt j :=
    rpow_three_halves _ (Nat.cast_nonneg j)
  simp only [nu]
  rw [← he]
  linarith

theorem qgap32_le {j : ℕ} (hj : 1 ≤ j) :
    (qgap (3/2) j : ℝ) ≤ (3/2) * (Real.sqrt j + 1) + 1 := by
  have h := qgap_le (p := (3/2 : ℝ)) (by norm_num) hj
  have hrw : ((j : ℝ) + 1) ^ ((3:ℝ)/2 - 1) = Real.sqrt ((j : ℝ) + 1) := by
    rw [show (3:ℝ)/2 - 1 = 1/2 by norm_num, Real.sqrt_eq_rpow]
  rw [hrw] at h
  have hs : Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt j + 1 := by
    have h1 : (0:ℝ) ≤ Real.sqrt j := Real.sqrt_nonneg _
    have h2 : Real.sqrt j ^ 2 = (j : ℝ) := Real.sq_sqrt (Nat.cast_nonneg j)
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (j:ℝ) + 1 by positivity),
      Real.sqrt_nonneg ((j : ℝ) + 1), h2, h1,
      Real.sqrt_le_sqrt (show (j : ℝ) + 1 ≤ (Real.sqrt j + 1) ^ 2 by nlinarith)]
  linarith

theorem le_qgap32 {j : ℕ} (hj : 1 ≤ j) :
    (3/2) * Real.sqrt j - 1 ≤ (qgap (3/2) j : ℝ) := by
  have h := le_qgap (p := (3/2 : ℝ)) (by norm_num) hj
  have hrw : (j : ℝ) ^ ((3:ℝ)/2 - 1) = Real.sqrt j := by
    rw [show (3:ℝ)/2 - 1 = 1/2 by norm_num, Real.sqrt_eq_rpow]
  rw [hrw] at h
  exact h

/-- `v = ⁴√x` satisfies `v² = √x`. -/
theorem sqrt_sqrt_sq (x : ℝ) :
    Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x :=
  Real.sq_sqrt (Real.sqrt_nonneg x)

/-- `v = ⁴√x` satisfies `v⁴ = x`. -/
theorem sqrt_sqrt_pow_four (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) ^ 4 = x := by
  have h1 : Real.sqrt (Real.sqrt x) ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 := by ring
  rw [h1, sqrt_sqrt_sq x, Real.sq_sqrt hx]


end SparseFock
