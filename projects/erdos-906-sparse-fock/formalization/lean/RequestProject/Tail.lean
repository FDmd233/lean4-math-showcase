import RequestProject.Fock
import RequestProject.Concavity

/-!
# Global tail domination at a crossing radius

Let `n` be the order of the derivative and let `m₀`, `m₀ + q` be two adjacent points of
the active sparse support (`m = ν_j - n`).  At the crossing radius `ρ` the two
corresponding terms of `F_p^{(n)}` have equal modulus, i.e. `Phi n ρ (m₀+q) = Phi n ρ m₀`.

This file proves that, on the whole circle of radius `ρ e^σ` for `|σ|` small, the sum of
*all* remaining terms — both the full left tail and the full right tail — is bounded by
an explicitly small multiple of the modulus of the principal term.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- The coefficient of `z^m` in the `n`-th derivative `F_p^{(n)}`. -/
noncomputable def dcoeff (p : ℝ) (n m : ℕ) : ℝ :=
  if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0

variable {p : ℝ} {n m₀ q Q : ℕ} {ρ σ c γ : ℝ}

theorem dcoeff_nonneg (p : ℝ) (n m : ℕ) : 0 ≤ dcoeff p n m := by
  unfold dcoeff
  split
  · positivity
  · exact le_rfl

theorem iteratedDeriv_F_eq_dcoeff (p : ℝ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (F p) z = ∑' m : ℕ, ((dcoeff p n m : ℝ) : ℂ) * z ^ m :=
  iteratedDeriv_F p n z

theorem summable_dcoeff_mul_pow (p : ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun m : ℕ => dcoeff p n m * x ^ m :=
  summable_iteratedDeriv_coeff p n hx

theorem summable_dcoeff_mul_pow_complex (p : ℝ) (n : ℕ) (z : ℂ) :
    Summable fun m : ℕ => ((dcoeff p n m : ℝ) : ℂ) * z ^ m := by
  refine Summable.of_norm ?_
  refine (summable_dcoeff_mul_pow p n (norm_nonneg z)).congr (fun m => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (dcoeff_nonneg p n m)]

/-- The modulus of the `m`-th term of `F_p^{(n)}` at radius `r` is at most `exp (Phi n r m)`. -/
theorem dcoeff_mul_pow_le_exp_Phi (p : ℝ) (n m : ℕ) {r : ℝ} (hr : 0 < r) :
    dcoeff p n m * r ^ m ≤ Real.exp (Phi n r m) := by
  have hfac : (0:ℝ) < ((n + m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmfac : (0:ℝ) < ((m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hval : Real.exp (Phi n r m) = Real.sqrt ((n + m)! ) / (m !) * r ^ m := by
    rw [Phi, Real.exp_add, Real.exp_sub]
    have h1 : Real.exp ((1 / 2) * Real.log ((n + m)! : ℝ)) = Real.sqrt ((n + m)! : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hfac]
      ring_nf
    have h2 : Real.exp (Real.log ((m)! : ℝ)) = ((m)! : ℝ) := Real.exp_log hmfac
    have h3 : Real.exp ((m : ℝ) * Real.log r) = r ^ m := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hr, Real.rpow_natCast]
    rw [h1, h2, h3]
  rw [hval, dcoeff]
  have hnm : (m + n)! = (n + m)! := by rw [Nat.add_comm]
  split
  · rw [hnm]
  · have : (0:ℝ) ≤ Real.sqrt ((n + m)! ) / (m !) * r ^ m := by positivity
    simpa using this

/-- `Phi` at radius `ρ e^σ` differs from `Phi` at radius `ρ` by `m σ`. -/
theorem Phi_exp_shift (n m : ℕ) {ρ σ : ℝ} (hρ : 0 < ρ) :
    Phi n (ρ * Real.exp σ) m = Phi n ρ m + m * σ := by
  rw [Phi, Phi, Real.log_mul (ne_of_gt hρ) (ne_of_gt (Real.exp_pos σ)), Real.log_exp]
  ring

/-! ### The termwise decay estimate -/

/-- The termwise bound to the left of the block. -/
theorem tail_term_left (hρ : 0 < ρ) (hσ : |σ| ≤ γ) (hγc : γ ≤ c) (hcl : c ≤ dstep n ρ m₀)
    {m : ℕ} (hm : m + Q ≤ m₀) :
    dcoeff p n m * (ρ * Real.exp σ) ^ m
      ≤ Real.exp (Phi n ρ m₀ + m₀ * σ) * Real.exp (-(c - γ) * Q) := by
  have hRpos : 0 < ρ * Real.exp σ := by positivity
  have h1 := dcoeff_mul_pow_le_exp_Phi p n m hRpos
  rw [Phi_exp_shift n m hρ] at h1
  refine h1.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : Phi n ρ m ≤ Phi n ρ m₀ - c * ((m₀ : ℝ) - m) := Phi_le_left hcl (by omega)
  have hQ0 : (0:ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg _
  have hu : (Q : ℝ) ≤ (m₀ : ℝ) - m := by
    have : (m : ℝ) + Q ≤ m₀ := by exact_mod_cast hm
    linarith
  have habs : -γ ≤ σ := neg_le_of_abs_le hσ
  have hγ0 : 0 ≤ γ := le_trans (abs_nonneg σ) hσ
  have hA : 0 ≤ ((m₀ : ℝ) - m - Q) * (c + σ) := mul_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ (Q : ℝ) * (σ + γ) := mul_nonneg hQ0 (by linarith)
  have hexp1 : ((m₀ : ℝ) - m - Q) * (c + σ)
      = (m₀ : ℝ) * c + (m₀ : ℝ) * σ - (m : ℝ) * c - (m : ℝ) * σ
        - (Q : ℝ) * c - (Q : ℝ) * σ := by ring
  have hexp2 : c * ((m₀ : ℝ) - m) = c * (m₀ : ℝ) - c * (m : ℝ) := by ring
  have hexp3 : (Q : ℝ) * (σ + γ) = (Q : ℝ) * σ + (Q : ℝ) * γ := by ring
  have hexp4 : -(c - γ) * (Q : ℝ) = -((Q : ℝ) * c) + (Q : ℝ) * γ := by ring
  rw [hexp1] at hA
  rw [hexp2] at h2
  rw [hexp3] at hB
  rw [hexp4]
  nlinarith [h2, hA, hB]

/-- The termwise bound to the right of the block. -/
theorem tail_term_right (hρ : 0 < ρ) (hq : 1 ≤ q) (hσ : |σ| ≤ γ)
    (hcross : Phi n ρ (m₀ + q) = Phi n ρ m₀)
    (hcr : dstep n ρ (m₀ + q - 1) ≤ -c)
    {m : ℕ} (hm : m₀ + q + Q ≤ m) :
    dcoeff p n m * (ρ * Real.exp σ) ^ m
      ≤ Real.exp (Phi n ρ m₀ + m₀ * σ) * Real.exp (q * γ)
        * Real.exp (-(c - γ) * ((m : ℝ) - (m₀ + q))) := by
  have hRpos : 0 < ρ * Real.exp σ := by positivity
  have h1 := dcoeff_mul_pow_le_exp_Phi p n m hRpos
  rw [Phi_exp_shift n m hρ] at h1
  refine h1.trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : Phi n ρ m ≤ Phi n ρ (m₀ + q) - c * ((m : ℝ) - (m₀ + q)) :=
    Phi_le_right hq hcr (by omega)
  rw [hcross] at h2
  have hmge : ((m₀ : ℝ) + q) ≤ (m : ℝ) := by exact_mod_cast (by omega : m₀ + q ≤ m)
  have hv : (0:ℝ) ≤ (m : ℝ) - (m₀ + q) := by linarith
  have habs' : σ ≤ γ := le_of_abs_le hσ
  have hq0 : (0:ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hA : ((m : ℝ) - (m₀ + q)) * σ ≤ ((m : ℝ) - (m₀ + q)) * γ :=
    mul_le_mul_of_nonneg_left habs' hv
  have hB : (q : ℝ) * σ ≤ (q : ℝ) * γ := mul_le_mul_of_nonneg_left habs' hq0
  have hsplit : (m : ℝ) * σ = (m₀ : ℝ) * σ + (q : ℝ) * σ + ((m : ℝ) - (m₀ + q)) * σ := by ring
  rw [hsplit]
  nlinarith [h2, hA, hB]

/-! ### Summing the tail -/

/-- The full tail sum at the crossing radius is exponentially small compared with the
modulus of the principal term.  This is the global tail domination statement. -/
theorem tail_sum_bound (hρ : 0 < ρ) (hq : 1 ≤ q) (hσ : |σ| ≤ γ) (hγc : γ < c)
    (hcross : Phi n ρ (m₀ + q) = Phi n ρ m₀)
    (hcl : c ≤ dstep n ρ m₀) (hcr : dstep n ρ (m₀ + q - 1) ≤ -c)
    (hsupp : ∀ m : ℕ, dcoeff p n m ≠ 0 → m ≠ m₀ → m ≠ m₀ + q →
      (m + Q ≤ m₀ ∨ m₀ + q + Q ≤ m)) :
    ∑' m : ℕ, (if m = m₀ ∨ m = m₀ + q then 0 else dcoeff p n m * (ρ * Real.exp σ) ^ m)
      ≤ Real.exp (Phi n ρ m₀ + m₀ * σ) * Real.exp (-(c - γ) * Q)
          * (((m₀ : ℝ) + 1) + Real.exp (q * γ) / (1 - Real.exp (-(c - γ)))) := by
  have hδpos : 0 < c - γ := by linarith
  set E0 : ℝ := Real.exp (Phi n ρ m₀ + m₀ * σ) with hE0
  have hE0pos : 0 < E0 := Real.exp_pos _
  have hx0 : 0 < Real.exp (-(c - γ)) := Real.exp_pos _
  have hx1 : Real.exp (-(c - γ)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpow : ∀ j : ℕ, Real.exp (-(c - γ)) ^ j = Real.exp (-(c - γ) * j) := by
    intro j
    rw [← Real.exp_nat_mul]
    ring_nf
  -- majorants
  set fL : ℕ → ℝ := fun m => if m ≤ m₀ then E0 * Real.exp (-(c - γ) * Q) else 0 with hfL
  set fR : ℕ → ℝ := fun m =>
    if m₀ + q + Q ≤ m then
      E0 * Real.exp (q * γ) * Real.exp (-(c - γ) * ((m : ℝ) - (m₀ + q)))
    else 0 with hfR
  have hfLnn : ∀ m, 0 ≤ fL m := by
    intro m
    rw [hfL]
    dsimp only
    split
    · positivity
    · exact le_rfl
  have hfRnn : ∀ m, 0 ≤ fR m := by
    intro m
    rw [hfR]
    dsimp only
    split
    · positivity
    · exact le_rfl
  have hfLsum : Summable fL := by
    refine summable_of_ne_finset_zero (s := Finset.range (m₀ + 1)) (fun m hm => ?_)
    rw [hfL]
    dsimp only
    rw [if_neg]
    intro h
    exact hm (Finset.mem_range.2 (by omega))
  have hgeo : Summable fun j : ℕ => Real.exp (-(c - γ)) ^ j :=
    summable_geometric_of_lt_one hx0.le hx1
  have hcongrR : ∀ j : ℕ, fR (j + (m₀ + q + Q))
      = (E0 * Real.exp (q * γ) * Real.exp (-(c - γ) * Q)) * Real.exp (-(c - γ)) ^ j := by
    intro j
    rw [hfR]
    dsimp only
    rw [if_pos (by omega)]
    have hc : ((j + (m₀ + q + Q) : ℕ) : ℝ) - (m₀ + q) = (Q : ℝ) + j := by push_cast; ring
    rw [hc, hpow j, show -(c - γ) * ((Q : ℝ) + j) = -(c - γ) * Q + -(c - γ) * j by ring,
      Real.exp_add]
    ring
  have hfRsum : Summable fR := by
    have hshift : Summable fun j : ℕ => fR (j + (m₀ + q + Q)) := by
      refine (hgeo.mul_left (E0 * Real.exp (q * γ) * Real.exp (-(c - γ) * Q))).congr
        (fun j => (hcongrR j).symm)
    exact (summable_nat_add_iff (m₀ + q + Q)).1 hshift
  -- termwise domination
  have hdom : ∀ m : ℕ,
      (if m = m₀ ∨ m = m₀ + q then 0 else dcoeff p n m * (ρ * Real.exp σ) ^ m)
        ≤ fL m + fR m := by
    intro m
    by_cases hme : m = m₀ ∨ m = m₀ + q
    · rw [if_pos hme]
      exact add_nonneg (hfLnn m) (hfRnn m)
    · rw [if_neg hme]
      push_neg at hme
      by_cases hz : dcoeff p n m = 0
      · rw [hz, zero_mul]
        exact add_nonneg (hfLnn m) (hfRnn m)
      rcases hsupp m hz hme.1 hme.2 with hL | hR
      · have hb := tail_term_left (p := p) (Q := Q) hρ hσ hγc.le hcl hL
        have hfLm : fL m = E0 * Real.exp (-(c - γ) * Q) := by
          rw [hfL]
          dsimp only
          rw [if_pos (by omega)]
        rw [hfLm]
        linarith [hfRnn m]
      · have hb := tail_term_right (p := p) hρ hq hσ hcross hcr hR
        have hfRm : fR m
            = E0 * Real.exp (q * γ) * Real.exp (-(c - γ) * ((m : ℝ) - (m₀ + q))) := by
          rw [hfR]
          dsimp only
          rw [if_pos hR]
        rw [hfRm]
        linarith [hfLnn m]
  have htailsum : Summable fun m : ℕ =>
      (if m = m₀ ∨ m = m₀ + q then 0 else dcoeff p n m * (ρ * Real.exp σ) ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      (summable_dcoeff_mul_pow p n (le_of_lt (by positivity : (0:ℝ) < ρ * Real.exp σ)))
    · split
      · exact le_rfl
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
    · split
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
      · exact le_rfl
  refine le_trans (Summable.tsum_le_tsum hdom htailsum (hfLsum.add hfRsum)) ?_
  rw [hfLsum.tsum_add hfRsum]
  have hLval : ∑' m : ℕ, fL m = ((m₀ : ℝ) + 1) * (E0 * Real.exp (-(c - γ) * Q)) := by
    have h0 : ∀ m ∉ Finset.range (m₀ + 1), fL m = 0 := by
      intro m hm
      have hnot : ¬ (m ≤ m₀) := by
        intro h
        exact hm (Finset.mem_range.2 (by omega))
      rw [hfL]
      dsimp only
      rw [if_neg hnot]
    rw [tsum_eq_sum h0]
    have hall : ∀ m ∈ Finset.range (m₀ + 1), fL m = E0 * Real.exp (-(c - γ) * Q) := by
      intro m hm
      have hle : m ≤ m₀ := by
        have := Finset.mem_range.1 hm
        omega
      rw [hfL]
      dsimp only
      rw [if_pos hle]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range]
    ring
  have hRval : ∑' m : ℕ, fR m
      = E0 * Real.exp (q * γ) * Real.exp (-(c - γ) * Q) * (1 - Real.exp (-(c - γ)))⁻¹ := by
    have hsplit := hfRsum.sum_add_tsum_nat_add (m₀ + q + Q)
    have hzero : ∑ i ∈ Finset.range (m₀ + q + Q), fR i = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hlt : i < m₀ + q + Q := Finset.mem_range.1 hi
      rw [hfR]
      dsimp only
      rw [if_neg (by omega)]
    rw [← hsplit, hzero, zero_add, tsum_congr hcongrR, hgeo.tsum_mul_left,
      tsum_geometric_of_lt_one hx0.le hx1]
  rw [hLval, hRval]
  refine le_of_eq ?_
  field_simp

end SparseFock
