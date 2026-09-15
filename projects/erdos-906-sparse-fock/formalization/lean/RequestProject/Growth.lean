import Mathlib

/-!
# The Fock majorant `∑ r^k / √(k!)`

The Cauchy–Schwarz estimate (2.6) of the paper is proved here
*Zeros of high derivatives of sparse Fock series*:
for every `ε > 0`,
`∑_{k≥0} r^k/√(k!) ≤ √((1+ε)/ε) exp((1+ε) r² / 2)`,
together with the summability that it presupposes, and the specialisation `ε = r^{-2}`
which gives `∑_{k≥0} r^k/√(k!) ≤ √(1+r²) exp((1+r²)/2)`.
-/

namespace SparseFock

open scoped Nat BigOperators

/-- The majorant series converges for every radius. -/
theorem summable_pow_div_sqrt_factorial {r : ℝ} (hr : 0 ≤ r) :
    Summable fun k : ℕ => r ^ k / Real.sqrt (k !) := by
  have hsummable : Summable fun k : ℕ => (1/2 : ℝ) * ((1/2 : ℝ) ^ k + (2 * r ^ 2) ^ k / (k !)) := by
    refine Summable.mul_left _ (Summable.add ?_ ?_)
    · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
    · exact Real.summable_pow_div_factorial _
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsummable
  set a : ℝ := (1/2 : ℝ) ^ k with ha_def
  set b : ℝ := (2 * r ^ 2) ^ k / (k !) with hb_def
  have hfacpos : (0:ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have ha : 0 < a := by positivity
  have hb : 0 ≤ b := by positivity
  have hx : 0 ≤ r ^ k / Real.sqrt (k !) := by positivity
  have hab : a * b = (r ^ k / Real.sqrt (k !)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hfacpos), ha_def, hb_def]
    rw [div_eq_iff (ne_of_gt hfacpos)] at *
    field_simp
    rw [← mul_pow, ← pow_mul]
    ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (r ^ k / Real.sqrt (k !) - (a + b) / 2)]

/-- The Cauchy–Schwarz bound (2.6). -/
theorem tsum_pow_div_sqrt_factorial_le {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    ∑' k : ℕ, r ^ k / Real.sqrt (k !) ≤
      Real.sqrt ((1 + ε) / ε) * Real.exp ((1 + ε) * r ^ 2 / 2) := by
  have hε1 : (0:ℝ) < 1 + ε := by linarith
  set f : ℕ → ℝ := fun k => (1 / (1 + ε)) ^ k with hf_def
  set g : ℕ → ℝ := fun k => ((1 + ε) * r ^ 2) ^ k / (k !) with hg_def
  have hfnn : ∀ k, 0 ≤ f k := fun k => by positivity
  have hgnn : ∀ k, 0 ≤ g k := fun k => by positivity
  have hfsum : Summable f := summable_geometric_of_lt_one (by positivity) (by
    rw [div_lt_one hε1]; linarith)
  have hgsum : Summable g := Real.summable_pow_div_factorial _
  have hftsum : ∑' k, f k = (1 + ε) / ε := by
    rw [hf_def, tsum_geometric_of_lt_one (by positivity) (by rw [div_lt_one hε1]; linarith)]
    field_simp
    rw [show (1:ℝ) + ε - 1 = ε by ring]
    exact div_self (ne_of_gt hε)
  have hgtsum : ∑' k, g k = Real.exp ((1 + ε) * r ^ 2) := by
    rw [hg_def, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- the exponential of half the argument
  have hsqrt_exp : Real.sqrt (Real.exp ((1 + ε) * r ^ 2)) = Real.exp ((1 + ε) * r ^ 2 / 2) := by
    have : Real.exp ((1 + ε) * r ^ 2) = (Real.exp ((1 + ε) * r ^ 2 / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
      ring_nf
    rw [this, Real.sqrt_sq (le_of_lt (Real.exp_pos _))]
  refine Summable.tsum_le_of_sum_le (summable_pow_div_sqrt_factorial hr) (fun s => ?_)
  have hterm : ∀ k ∈ s, r ^ k / Real.sqrt (k !) = Real.sqrt (f k) * Real.sqrt (g k) := by
    intro k _
    rw [← Real.sqrt_mul (hfnn k)]
    have hprod : f k * g k = (r ^ k) ^ 2 / (k !) := by
      have key : (1 / (1 + ε)) ^ k * ((1 + ε) * r ^ 2) ^ k = (r ^ k) ^ 2 := by
        rw [← mul_pow, show (1 / (1 + ε)) * ((1 + ε) * r ^ 2) = r ^ 2 by field_simp, ← pow_mul,
          ← pow_mul, Nat.mul_comm]
      simp only [hf_def, hg_def]
      rw [← mul_div_assoc, key]
    rw [hprod, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  calc ∑ k ∈ s, r ^ k / Real.sqrt (k !)
      = ∑ k ∈ s, Real.sqrt (f k) * Real.sqrt (g k) := Finset.sum_congr rfl hterm
    _ ≤ Real.sqrt (∑ k ∈ s, f k) * Real.sqrt (∑ k ∈ s, g k) :=
        Real.sum_sqrt_mul_sqrt_le s hfnn hgnn
    _ ≤ Real.sqrt ((1 + ε) / ε) * Real.exp ((1 + ε) * r ^ 2 / 2) := by
        rw [← hsqrt_exp]
        apply mul_le_mul
        · exact Real.sqrt_le_sqrt (hftsum ▸ hfsum.sum_le_tsum s (fun k _ => hfnn k))
        · exact Real.sqrt_le_sqrt (hgtsum ▸ hgsum.sum_le_tsum s (fun k _ => hgnn k))
        · exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _

/-- The choice `ε = r^{-2}` in (2.6), which yields the growth bound
`log M_{F_p}(r) ≤ ½ r² + O(log r)`. -/
theorem tsum_pow_div_sqrt_factorial_le' {r : ℝ} (hr : 0 ≤ r) :
    ∑' k : ℕ, r ^ k / Real.sqrt (k !) ≤
      Real.sqrt (1 + r ^ 2) * Real.exp ((1 + r ^ 2) / 2) := by
  rcases eq_or_lt_of_le hr with h | hpos
  · -- `r = 0`: use `ε = 1`
    subst_vars
    have h1 := tsum_pow_div_sqrt_factorial_le (r := 0) (ε := 1) le_rfl one_pos
    have h2 : Real.sqrt ((1 + 1) / 1) * Real.exp ((1 + 1) * (0:ℝ) ^ 2 / 2) = Real.sqrt 2 := by
      norm_num
    rw [h2] at h1
    refine h1.trans ?_
    have hs2 : Real.sqrt 2 ≤ 1.5 := by
      rw [show (1.5:ℝ) = Real.sqrt (1.5 ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hexp : (1.5:ℝ) ≤ Real.exp ((1 + (0:ℝ) ^ 2) / 2) := by
      have := Real.add_one_le_exp ((1 + (0:ℝ) ^ 2) / 2)
      norm_num at this ⊢
      linarith
    have : Real.sqrt (1 + (0:ℝ) ^ 2) = 1 := by norm_num
    rw [this, one_mul]
    linarith
  · have hr2 : (0:ℝ) < r ^ 2 := by positivity
    have h := tsum_pow_div_sqrt_factorial_le (r := r) (ε := 1 / r ^ 2) hr (by positivity)
    have e1 : (1 + 1 / r ^ 2) / (1 / r ^ 2) = 1 + r ^ 2 := by
      field_simp
      ring
    have e2 : (1 + 1 / r ^ 2) * r ^ 2 / 2 = (1 + r ^ 2) / 2 := by
      field_simp
      ring
    rw [e1, e2] at h
    exact h

end SparseFock
