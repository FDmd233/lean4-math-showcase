import RequestProject.Tail

/-!
# Tail domination outside a block, at an arbitrary radius

`Tail.tail_sum_bound` bounds the tail of `F_p^{(n)}` outside a *pair* of adjacent support
points, at a radius close to the crossing radius of that pair.  For the exclusion of
additional zeros one needs the same estimate outside a *block* `[m₀, m₀+q]` of arbitrary
length, at an arbitrary radius `r` at which the two block slopes are `≥ c` and `≤ -c`.

The statement below gives exactly that estimate and is used twice: with the block
`[m_j, m_{j+1}]` in the transition regime, and with the block `[m_j, m_{j+2}]` in the
one-term-dominant regime.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

variable {p : ℝ} {n m₀ q Q : ℕ} {r c : ℝ}

/-- Termwise bound to the left of the block, at the radius `r` itself. -/
theorem term_left_le (hr : 0 < r) (hcl : c ≤ dstep n r m₀) (hc : 0 ≤ c)
    {m : ℕ} (hm : m + Q ≤ m₀) :
    dcoeff p n m * r ^ m ≤ Real.exp (Phi n r m₀) * Real.exp (-c * Q) := by
  have h1 := dcoeff_mul_pow_le_exp_Phi p n m hr
  refine h1.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : Phi n r m ≤ Phi n r m₀ - c * ((m₀ : ℝ) - m) := Phi_le_left hcl (by omega)
  have hu : (Q : ℝ) ≤ (m₀ : ℝ) - m := by
    have : (m : ℝ) + Q ≤ m₀ := by exact_mod_cast hm
    linarith
  nlinarith

/-- Termwise bound to the right of the block, at the radius `r` itself. -/
theorem term_right_le (hr : 0 < r) (hq : 1 ≤ q) (hcr : dstep n r (m₀ + q - 1) ≤ -c)
    {m : ℕ} (hm : m₀ + q ≤ m) :
    dcoeff p n m * r ^ m
      ≤ Real.exp (Phi n r (m₀ + q)) * Real.exp (-c * ((m : ℝ) - (m₀ + q))) := by
  have h1 := dcoeff_mul_pow_le_exp_Phi p n m hr
  refine h1.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : Phi n r m ≤ Phi n r (m₀ + q) - c * ((m : ℝ) - (m₀ + q)) :=
    Phi_le_right hq hcr hm
  linarith

set_option maxHeartbeats 1000000 in
/-- **Tail domination outside a block.**  At a radius `r` at which the slope of the
logarithmic weight is `≥ c` at the left end of the block `[m₀, m₀+q]` and `≤ -c` at its
right end, and where every active support point outside the block is at distance at least
`Q` from it, the sum of all terms outside the block is exponentially small. -/
theorem tail_outside_block (hr : 0 < r) (hq : 1 ≤ q) (hc : 0 < c)
    (hcl : c ≤ dstep n r m₀) (hcr : dstep n r (m₀ + q - 1) ≤ -c)
    (hleft : ∀ m : ℕ, dcoeff p n m ≠ 0 → m < m₀ → m + Q ≤ m₀)
    (hright : ∀ m : ℕ, dcoeff p n m ≠ 0 → m₀ + q < m → m₀ + q + Q ≤ m) :
    ∑' m : ℕ, (if m₀ ≤ m ∧ m ≤ m₀ + q then 0 else dcoeff p n m * r ^ m)
      ≤ ((m₀ : ℝ) + 1) * (Real.exp (Phi n r m₀) * Real.exp (-c * Q))
        + Real.exp (Phi n r (m₀ + q)) * Real.exp (-c * Q) / (1 - Real.exp (-c)) := by
  have hx0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hx1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpow : ∀ j : ℕ, Real.exp (-c) ^ j = Real.exp (-c * j) := by
    intro j
    rw [← Real.exp_nat_mul]
    ring_nf
  set EL : ℝ := Real.exp (Phi n r m₀) with hEL
  set ER : ℝ := Real.exp (Phi n r (m₀ + q)) with hER
  have hELpos : 0 < EL := Real.exp_pos _
  have hERpos : 0 < ER := Real.exp_pos _
  set fL : ℕ → ℝ := fun m => if m ≤ m₀ then EL * Real.exp (-c * Q) else 0 with hfL
  set fR : ℕ → ℝ := fun m =>
    if m₀ + q + Q ≤ m then ER * Real.exp (-c * ((m : ℝ) - (m₀ + q))) else 0 with hfR
  have hfLnn : ∀ m, 0 ≤ fL m := by
    intro m; rw [hfL]; dsimp only; split
    · positivity
    · exact le_rfl
  have hfRnn : ∀ m, 0 ≤ fR m := by
    intro m; rw [hfR]; dsimp only; split
    · positivity
    · exact le_rfl
  have hfLsum : Summable fL := by
    refine summable_of_ne_finset_zero (s := Finset.range (m₀ + 1)) (fun m hm => ?_)
    rw [hfL]; dsimp only
    rw [if_neg]
    intro h
    exact hm (Finset.mem_range.2 (by omega))
  have hgeo : Summable fun j : ℕ => Real.exp (-c) ^ j :=
    summable_geometric_of_lt_one hx0.le hx1
  have hcongrR : ∀ j : ℕ, fR (j + (m₀ + q + Q))
      = (ER * Real.exp (-c * Q)) * Real.exp (-c) ^ j := by
    intro j
    rw [hfR]; dsimp only
    rw [if_pos (by omega)]
    have hcst : ((j + (m₀ + q + Q) : ℕ) : ℝ) - (m₀ + q) = (Q : ℝ) + j := by push_cast; ring
    rw [hcst, hpow j, show -c * ((Q : ℝ) + j) = -c * Q + -c * j by ring, Real.exp_add]
    ring
  have hfRsum : Summable fR := by
    have hshift : Summable fun j : ℕ => fR (j + (m₀ + q + Q)) :=
      (hgeo.mul_left (ER * Real.exp (-c * Q))).congr (fun j => (hcongrR j).symm)
    exact (summable_nat_add_iff (m₀ + q + Q)).1 hshift
  have hdom : ∀ m : ℕ,
      (if m₀ ≤ m ∧ m ≤ m₀ + q then 0 else dcoeff p n m * r ^ m) ≤ fL m + fR m := by
    intro m
    by_cases hme : m₀ ≤ m ∧ m ≤ m₀ + q
    · rw [if_pos hme]
      exact add_nonneg (hfLnn m) (hfRnn m)
    · rw [if_neg hme]
      by_cases hz : dcoeff p n m = 0
      · rw [hz, zero_mul]
        exact add_nonneg (hfLnn m) (hfRnn m)
      · rcases Nat.lt_or_ge m m₀ with hlt | hge
        · have hL := hleft m hz hlt
          have hb := term_left_le (p := p) (Q := Q) hr hcl hc.le hL
          have hfLm : fL m = EL * Real.exp (-c * Q) := by
            rw [hfL]; dsimp only; rw [if_pos (by omega)]
          rw [hfLm]
          linarith [hfRnn m]
        · have hgt : m₀ + q < m := by
            by_contra hcon
            exact hme ⟨hge, by omega⟩
          have hR := hright m hz hgt
          have hb := term_right_le (p := p) hr hq hcr (show m₀ + q ≤ m by omega)
          have hfRm : fR m = ER * Real.exp (-c * ((m : ℝ) - (m₀ + q))) := by
            rw [hfR]; dsimp only; rw [if_pos hR]
          rw [hfRm]
          linarith [hfLnn m]
  have htailsum : Summable fun m : ℕ =>
      (if m₀ ≤ m ∧ m ≤ m₀ + q then 0 else dcoeff p n m * r ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      (summable_dcoeff_mul_pow p n hr.le)
    · split
      · exact le_rfl
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
    · split
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
      · exact le_rfl
  refine le_trans (Summable.tsum_le_tsum hdom htailsum (hfLsum.add hfRsum)) ?_
  rw [hfLsum.tsum_add hfRsum]
  have hLval : ∑' m : ℕ, fL m = ((m₀ : ℝ) + 1) * (EL * Real.exp (-c * Q)) := by
    have h0 : ∀ m ∉ Finset.range (m₀ + 1), fL m = 0 := by
      intro m hm
      have hnot : ¬ (m ≤ m₀) := by
        intro h
        exact hm (Finset.mem_range.2 (by omega))
      rw [hfL]; dsimp only; rw [if_neg hnot]
    rw [tsum_eq_sum h0]
    have hall : ∀ m ∈ Finset.range (m₀ + 1), fL m = EL * Real.exp (-c * Q) := by
      intro m hm
      have hle : m ≤ m₀ := by
        have := Finset.mem_range.1 hm
        omega
      rw [hfL]; dsimp only; rw [if_pos hle]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range]
    ring
  have hRval : ∑' m : ℕ, fR m
      = ER * Real.exp (-c * Q) * (1 - Real.exp (-c))⁻¹ := by
    have hsplit := hfRsum.sum_add_tsum_nat_add (m₀ + q + Q)
    have hzero : ∑ i ∈ Finset.range (m₀ + q + Q), fR i = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hlt : i < m₀ + q + Q := Finset.mem_range.1 hi
      rw [hfR]; dsimp only; rw [if_neg (by omega)]
    rw [← hsplit, hzero, zero_add, tsum_congr hcongrR, hgeo.tsum_mul_left,
      tsum_geometric_of_lt_one hx0.le hx1]
  rw [hLval, hRval]
  refine le_of_eq ?_
  field_simp

end SparseFock
