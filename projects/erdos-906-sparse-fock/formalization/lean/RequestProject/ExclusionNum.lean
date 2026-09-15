import Mathlib

/-!
# The purely numerical inequalities of the exclusion argument

Four real-variable lemmas, isolated from the analytic argument so that they elaborate
independently:

* two size comparisons on the three-term block `[m_j, m_{j+2}]`;
* the passage from the numerical core's tail bound to the tail bound with the slope `c`;
* the final "sum of the two neighbours plus the tail is `< 1`" inequality.
-/

namespace SparseFock

/-- `exp (-x) ≤ 1 - x/2` for `0 ≤ x ≤ 1`. -/
theorem exp_neg_le_one_sub_half {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have h1 : (1:ℝ) + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x; linarith
  have h3 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h4 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [Real.exp_pos (-x)]
  have h5 : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `exp (-y/2) ≤ 2 / y` for `y > 0`. -/
theorem exp_neg_half_le {y : ℝ} (hy : 0 < y) : Real.exp (-(y/2)) ≤ 2 / y := by
  have h1 : y / 2 ≤ Real.exp (y / 2) := by
    have := Real.add_one_le_exp (y / 2); linarith
  have h3 : Real.exp (-(y/2)) * Real.exp (y/2) = 1 := by rw [← Real.exp_add]; simp
  rw [le_div_iff₀ hy]
  nlinarith [Real.exp_pos (-(y/2)), Real.exp_pos (y/2)]

/-- The three-term block is at most `(2B+6) v³` long. -/
theorem block_length_le {B v m q q' : ℝ} (hv3 : 3 ≤ v)
    (hm : m ≤ 2*B*v^3) (hq2 : q ≤ 2*v^2) (hq'2 : q' ≤ 2*v^2) :
    m + q + q' + 2 ≤ (2*B + 6) * v^3 := by
  have hvpos : (0:ℝ) < v := by linarith
  have h1 : v ^ 2 ≤ v ^ 3 / 3 := by nlinarith
  have h2 : (1:ℝ) ≤ v ^ 3 := by nlinarith
  nlinarith

/-- The slope bound at the right end of the three-term block. -/
theorem numeric_block_slope {B v q' T : ℝ} (hB : 2 ≤ B) (hv3 : 3 ≤ v)
    (hq' : v^2 ≤ q') (hTpos : 0 < T) (hT : T ≤ (2*B + 6) * v^3) :
    1/(32*B*v) ≤ (1/(2*T)) * (q' - 1)/2 := by
  have hvpos : (0:ℝ) < v := by linarith
  have hv29 : (9:ℝ) ≤ v ^ 2 := by nlinarith
  have hBpos : (0:ℝ) < B := by linarith
  have hstep1 : (1:ℝ)/(2*((2*B + 6) * v^3)) ≤ 1/(2*T) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hstep2 : v ^ 2 / 3 ≤ (q' - 1)/2 := by nlinarith
  have hmul : (1/(2*((2*B + 6) * v^3))) * (v ^ 2 / 3) ≤ (1/(2*T)) * ((q' - 1)/2) := by
    refine mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
  have heq : (1/(2*((2*B + 6) * v^3))) * (v ^ 2 / 3) = 1 / (6 * (2*B+6) * v) := by
    field_simp
    ring
  have hcmp : 1/(32*B*v) ≤ 1 / (6 * (2*B+6) * v) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hassoc : (1/(2*T)) * (q' - 1)/2 = (1/(2*T)) * ((q' - 1)/2) := by ring
  rw [hassoc]
  rw [heq] at hmul
  linarith

/-- The radial spacing bound on the three-term block. -/
theorem numeric_block_spacing {B v q q' T : ℝ} (hB : 2 ≤ B) (hv3 : 3 ≤ v)
    (hq : v^2 ≤ q) (hq' : v^2 ≤ q') (hTpos : 0 < T) (hT : T ≤ (2*B + 6) * v^3) :
    1/(2*(2*B + 6)*v) ≤ (1/(2*T)) * (q + q')/2 := by
  have hvpos : (0:ℝ) < v := by linarith
  have hstep1 : (1:ℝ)/(2*((2*B + 6) * v^3)) ≤ 1/(2*T) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hstep2 : v ^ 2 ≤ (q + q')/2 := by linarith
  have hmul : (1/(2*((2*B + 6) * v^3))) * (v ^ 2) ≤ (1/(2*T)) * ((q + q')/2) :=
    mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
  have heq : (1/(2*((2*B + 6) * v^3))) * (v ^ 2) = 1 / (2 * (2*B+6) * v) := by
    field_simp
  have hassoc : (1/(2*T)) * (q + q')/2 = (1/(2*T)) * ((q + q')/2) := by ring
  rw [hassoc]
  rw [heq] at hmul
  have : (1:ℝ)/(2*(2*B + 6)*v) = 1 / (2 * (2*B+6) * v) := by ring_nf
  linarith

/-- From the numerical core's tail bound to the tail bound with the full slope. -/
theorem tail_small_of_numeric {c γ c₀ Q Mm qγ E : ℝ}
    (hγpos : 0 < γ) (hγc : γ < c) (hQnn : 0 ≤ Q) (hMnn : 0 ≤ Mm) (hqγ : 0 ≤ qγ)
    (hE : 2 ≤ E)
    (hnum2 : E * (Real.exp (-(c - γ) * Q) *
        (Mm + Real.exp qγ / (1 - Real.exp (-(c - γ))))) < c₀ / 4) :
    Real.exp (-c * Q) * (Mm + 1 / (1 - Real.exp (-c))) ≤ c₀ / 8 := by
  have hden1 : 0 < 1 - Real.exp (-(c - γ)) := by
    have : Real.exp (-(c - γ)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hden2 : 0 < 1 - Real.exp (-c) := by
    have : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hmono1 : Real.exp (-c * Q) ≤ Real.exp (-(c - γ) * Q) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have he1 : Real.exp (-c) ≤ Real.exp (-(c - γ)) := Real.exp_le_exp.2 (by linarith)
  have he2 : (1:ℝ) ≤ Real.exp qγ := Real.one_le_exp hqγ
  have hmono2 : 1 / (1 - Real.exp (-c)) ≤ Real.exp qγ / (1 - Real.exp (-(c - γ))) := by
    have h1 : 1 / (1 - Real.exp (-c)) ≤ 1 / (1 - Real.exp (-(c - γ))) :=
      one_div_le_one_div_of_le hden1 (by linarith)
    have h2 : 1 / (1 - Real.exp (-(c - γ))) ≤ Real.exp qγ / (1 - Real.exp (-(c - γ))) := by
      rw [div_le_div_iff₀ hden1 hden1]
      nlinarith
    linarith
  have hnn1 : (0:ℝ) ≤ Mm + 1 / (1 - Real.exp (-c)) := by positivity
  have hprod : Real.exp (-c * Q) * (Mm + 1 / (1 - Real.exp (-c)))
      ≤ Real.exp (-(c - γ) * Q) * (Mm + Real.exp qγ / (1 - Real.exp (-(c - γ)))) :=
    mul_le_mul hmono1 (by linarith) hnn1 (Real.exp_pos _).le
  have hinner : (0:ℝ) ≤ Real.exp (-(c - γ) * Q)
      * (Mm + Real.exp qγ / (1 - Real.exp (-(c - γ)))) := by positivity
  nlinarith

/-- The final dominance inequality. -/
theorem dominance_sum_lt_one {c₀ dA dB T : ℝ} (hc₀pos : 0 < c₀) (hc₀ : c₀ ≤ 1/2)
    (hdA : c₀ < dA) (hdB : c₀ < dB) (hS : 16 / c₀ ≤ dA + dB) (hT : T ≤ c₀/8) :
    Real.exp (-dA) + Real.exp (-dB) + T < 1 := by
  have hc₀1 : c₀ ≤ 1 := by linarith
  have hbig : Real.exp (-c₀) ≤ 1 - c₀ / 2 := exp_neg_le_one_sub_half hc₀pos.le hc₀1
  have hSpos : (0:ℝ) < dA + dB := by
    have : (0:ℝ) < 16 / c₀ := by positivity
    linarith
  have hhalf : Real.exp (-((dA + dB)/2)) ≤ c₀ / 8 := by
    have h1 := exp_neg_half_le hSpos
    have h2 : 2 / (dA + dB) ≤ c₀ / 8 := by
      rw [div_le_div_iff₀ hSpos (by norm_num : (0:ℝ) < 8)]
      have h3 : 16 / c₀ ≤ dA + dB := hS
      rw [div_le_iff₀ hc₀pos] at h3
      nlinarith
    linarith
  rcases le_or_gt dA dB with hcase | hcase
  · have e1 : Real.exp (-dA) ≤ Real.exp (-c₀) := Real.exp_le_exp.2 (by linarith)
    have e2 : Real.exp (-dB) ≤ Real.exp (-((dA + dB)/2)) := Real.exp_le_exp.2 (by linarith)
    linarith
  · have e1 : Real.exp (-dB) ≤ Real.exp (-c₀) := Real.exp_le_exp.2 (by linarith)
    have e2 : Real.exp (-dA) ≤ Real.exp (-((dA + dB)/2)) := Real.exp_le_exp.2 (by linarith)
    linarith

/-- The principal weight `exp (m c₀ / q)` is at least `2` once `v` is large. -/
theorem exp_weight_ge_two {A c₀ v m q : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) (hv3 : 3 ≤ v)
    (hv6 : 6 / (A * c₀) ≤ v) (hm1 : A/3 * v^3 ≤ m) (hqpos : 0 < q) (hqup : q ≤ 2*v^2) :
    2 ≤ Real.exp (m * (c₀ / q)) := by
  have hvpos : (0:ℝ) < v := by linarith
  have hmnn : (0:ℝ) ≤ m := le_trans (by positivity) hm1
  have hfrac : c₀ / (2 * v^2) ≤ c₀ / q :=
    div_le_div_of_nonneg_left hc₀.le hqpos (by linarith)
  have h2' : (A/3) * v ^ 3 * (c₀ / (2 * v^2)) ≤ m * (c₀ / (2*v^2)) :=
    mul_le_mul_of_nonneg_right hm1 (by positivity)
  have h3' : m * (c₀ / (2*v^2)) ≤ m * (c₀/q) := mul_le_mul_of_nonneg_left hfrac hmnn
  have h4' : (A/3) * v ^ 3 * (c₀ / (2 * v^2)) = A * c₀ * v / 6 := by
    field_simp; ring
  have hmc : A * c₀ * v / 6 ≤ m * (c₀ / q) := by linarith
  have hge1 : (1:ℝ) ≤ A * c₀ * v / 6 := by
    rw [div_le_iff₀ (by positivity)] at hv6
    nlinarith
  have hle : Real.exp 1 ≤ Real.exp (m * (c₀/q)) := Real.exp_le_exp.2 (by linarith)
  have h2e : (2:ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  linarith

end SparseFock
