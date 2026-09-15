import RequestProject.Transition

/-!
# No zero when one term dominates

This is step 3 of the exclusion argument: if on the circle `|z| = r` one support term
strictly exceeds the sum of all the others, then `F_p^{(n)}` has no zero there.

The hypotheses are stated for a block `[m₀, m₀+q+q']` of three consecutive support
points, with the middle one `m₀+q` dominating its two neighbours by factors `e^{-dA}`,
`e^{-dB}`, and with the usual exponentially small tail outside the block.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

set_option maxHeartbeats 1000000 in
/-- **One-term dominance excludes zeros.** -/
theorem no_zero_of_dominant {p : ℝ} {n m₀ q q' Q : ℕ} {r c dA dB : ℝ}
    (hr : 0 < r) (hqq : 1 ≤ q + q') (hc : 0 < c)
    (hsupp₁ : IsSupp p (m₀ + q + n))
    (hcl : c ≤ dstep n r m₀) (hcr : dstep n r (m₀ + (q + q') - 1) ≤ -c)
    (hinner : ∀ m : ℕ, dcoeff p n m ≠ 0 → m₀ ≤ m → m ≤ m₀ + (q + q') →
        m = m₀ ∨ m = m₀ + q ∨ m = m₀ + (q + q'))
    (hleft : ∀ m : ℕ, dcoeff p n m ≠ 0 → m < m₀ → m + Q ≤ m₀)
    (hright : ∀ m : ℕ, dcoeff p n m ≠ 0 → m₀ + (q + q') < m → m₀ + (q + q') + Q ≤ m)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hPA : Phi n r m₀ ≤ Phi n r (m₀ + q) - dA)
    (hPB : Phi n r (m₀ + (q + q')) ≤ Phi n r (m₀ + q) - dB)
    (hsmall : Real.exp (-dA) + Real.exp (-dB)
        + Real.exp (-c * Q) * (((m₀ : ℝ) + 1) + 1 / (1 - Real.exp (-c))) < 1)
    {z : ℂ} (hznorm : ‖z‖ = r) :
    iteratedDeriv n (F p) z ≠ 0 := by
  set M : ℕ := m₀ + q with hM
  set L : ℕ := m₀ + (q + q') with hL
  have hx0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hx1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hEM : dcoeff p n M * r ^ M = Real.exp (Phi n r M) :=
    dcoeff_mul_pow_eq_exp_Phi p n M hr hsupp₁
  have hEMpos : (0:ℝ) < Real.exp (Phi n r M) := Real.exp_pos _
  -- the tail outside the block
  have htail := tail_outside_block (p := p) (n := n) (m₀ := m₀) (q := q + q') (Q := Q)
    (r := r) (c := c) hr hqq hc hcl hcr hleft hright
  -- the three summable pieces
  have hsum0 : Summable fun m : ℕ =>
      (if m₀ ≤ m ∧ m ≤ L then 0 else dcoeff p n m * r ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      (summable_dcoeff_mul_pow p n hr.le)
    · split
      · exact le_rfl
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
    · split
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
      · exact le_rfl
  have hsumA : Summable fun m : ℕ => (if m = m₀ then dcoeff p n m₀ * r ^ m₀ else 0) :=
    summable_of_ne_finset_zero (s := {m₀}) (fun m hm => if_neg (by simpa using hm))
  have hsumB : Summable fun m : ℕ => (if m = L then dcoeff p n L * r ^ L else 0) :=
    summable_of_ne_finset_zero (s := {L}) (fun m hm => if_neg (by simpa using hm))
  have hsumtot : Summable fun m : ℕ => (if m = M then 0 else dcoeff p n m * r ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      (summable_dcoeff_mul_pow p n hr.le)
    · split
      · exact le_rfl
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
    · split
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
      · exact le_rfl
  -- the pointwise comparison
  have hnn : ∀ m : ℕ, (0:ℝ) ≤ dcoeff p n m * r ^ m := fun m =>
    mul_nonneg (dcoeff_nonneg p n m) (by positivity)
  have hpt : ∀ m : ℕ, (if m = M then 0 else dcoeff p n m * r ^ m)
      ≤ (if m₀ ≤ m ∧ m ≤ L then 0 else dcoeff p n m * r ^ m)
        + (if m = m₀ then dcoeff p n m₀ * r ^ m₀ else 0)
        + (if m = L then dcoeff p n L * r ^ L else 0) := by
    intro m
    by_cases hmM : m = M
    · rw [if_pos hmM]
      split_ifs <;> linarith [hnn m, hnn m₀, hnn L]
    · rw [if_neg hmM]
      by_cases hin : m₀ ≤ m ∧ m ≤ L
      · rw [if_pos hin]
        by_cases hz : dcoeff p n m = 0
        · rw [hz, zero_mul]
          split_ifs <;> linarith [hnn m₀, hnn L]
        · rcases hinner m hz hin.1 hin.2 with h | h | h
          · rw [if_pos h, if_neg (by omega : ¬ (m = L)), h]
            linarith [hnn m₀]
          · exact absurd h hmM
          · rw [if_neg (by omega : ¬ (m = m₀)), if_pos h, h]
            linarith [hnn L]
      · rw [if_neg hin]
        split_ifs <;> linarith [hnn m, hnn m₀, hnn L]
  have hcmp : ∑' m : ℕ, (if m = M then 0 else dcoeff p n m * r ^ m)
      ≤ (∑' m : ℕ, (if m₀ ≤ m ∧ m ≤ L then 0 else dcoeff p n m * r ^ m))
        + dcoeff p n m₀ * r ^ m₀ + dcoeff p n L * r ^ L := by
    have h := Summable.tsum_le_tsum hpt hsumtot ((hsum0.add hsumA).add hsumB)
    rw [(hsum0.add hsumA).tsum_add hsumB, hsum0.tsum_add hsumA] at h
    have hA' : ∑' m : ℕ, (if m = m₀ then dcoeff p n m₀ * r ^ m₀ else 0)
        = dcoeff p n m₀ * r ^ m₀ := by
      rw [tsum_eq_single m₀ (fun b hb => if_neg hb), if_pos rfl]
    have hB' : ∑' m : ℕ, (if m = L then dcoeff p n L * r ^ L else 0)
        = dcoeff p n L * r ^ L := by
      rw [tsum_eq_single L (fun b hb => if_neg hb), if_pos rfl]
    rw [hA', hB'] at h
    linarith
  -- bound the three pieces by multiples of the dominant term
  have hbA : dcoeff p n m₀ * r ^ m₀ ≤ Real.exp (Phi n r M) * Real.exp (-dA) := by
    refine le_trans (dcoeff_mul_pow_le_exp_Phi p n m₀ hr) ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hbB : dcoeff p n L * r ^ L ≤ Real.exp (Phi n r M) * Real.exp (-dB) := by
    refine le_trans (dcoeff_mul_pow_le_exp_Phi p n L hr) ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hbT : (∑' m : ℕ, (if m₀ ≤ m ∧ m ≤ L then 0 else dcoeff p n m * r ^ m))
      ≤ Real.exp (Phi n r M)
          * (Real.exp (-c * Q) * (((m₀ : ℝ) + 1) + 1 / (1 - Real.exp (-c)))) := by
    refine le_trans htail ?_
    have he0 : Real.exp (Phi n r m₀) ≤ Real.exp (Phi n r M) :=
      Real.exp_le_exp.2 (by linarith)
    have heL : Real.exp (Phi n r L) ≤ Real.exp (Phi n r M) :=
      Real.exp_le_exp.2 (by linarith)
    have hcq : (0:ℝ) < Real.exp (-c * Q) := Real.exp_pos _
    have hm0 : (0:ℝ) ≤ (m₀ : ℝ) + 1 := by positivity
    have hden : (0:ℝ) < 1 - Real.exp (-c) := by linarith
    have h1 : ((m₀ : ℝ) + 1) * (Real.exp (Phi n r m₀) * Real.exp (-c * Q))
        ≤ ((m₀ : ℝ) + 1) * (Real.exp (Phi n r M) * Real.exp (-c * Q)) := by
      have := mul_le_mul_of_nonneg_right he0 hcq.le
      exact mul_le_mul_of_nonneg_left this hm0
    have h2 : Real.exp (Phi n r L) * Real.exp (-c * Q) / (1 - Real.exp (-c))
        ≤ Real.exp (Phi n r M) * Real.exp (-c * Q) / (1 - Real.exp (-c)) := by
      exact (div_le_div_iff_of_pos_right hden).2 (mul_le_mul_of_nonneg_right heL hcq.le)
    have hrw : Real.exp (Phi n r M)
        * (Real.exp (-c * Q) * (((m₀ : ℝ) + 1) + 1 / (1 - Real.exp (-c))))
        = ((m₀ : ℝ) + 1) * (Real.exp (Phi n r M) * Real.exp (-c * Q))
          + Real.exp (Phi n r M) * Real.exp (-c * Q) / (1 - Real.exp (-c)) := by
      field_simp
    rw [hrw]
    linarith
  -- conclude
  intro hz0
  have hsub := norm_sub_one_term_le p n M z
  rw [hz0, zero_sub, norm_neg, norm_mul, norm_pow, hznorm, Complex.norm_real,
    Real.norm_of_nonneg (dcoeff_nonneg p n M)] at hsub
  rw [hEM] at hsub
  have hfinal : Real.exp (Phi n r M)
      ≤ Real.exp (Phi n r M) * (Real.exp (-dA) + Real.exp (-dB)
          + Real.exp (-c * Q) * (((m₀ : ℝ) + 1) + 1 / (1 - Real.exp (-c)))) := by
    have := le_trans hsub (le_trans hcmp (by linarith [hbA, hbB, hbT] :
      (∑' m : ℕ, (if m₀ ≤ m ∧ m ≤ L then 0 else dcoeff p n m * r ^ m))
        + dcoeff p n m₀ * r ^ m₀ + dcoeff p n L * r ^ L
        ≤ Real.exp (Phi n r M) * (Real.exp (-dA) + Real.exp (-dB)
            + Real.exp (-c * Q) * (((m₀ : ℝ) + 1) + 1 / (1 - Real.exp (-c))))))
    exact this
  nlinarith [hEMpos, hsmall, hfinal]

end SparseFock
