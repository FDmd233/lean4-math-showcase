import RequestProject.Curvature

/-!
# Consequences of the discrete concavity of the logarithmic weights

The logarithmic weight `Phi n r m = ½ log ((n+m)!) - log (m!) + m log r` is strictly
concave in `m` (`dstep_sub_dstep_succ_pos`).  The next lemmas turn that concavity, together
with the quantitative curvature bound of `Curvature.lean`, into the *decay* statements
used for the tail estimate of Section 3 of the paper:

at a crossing radius, where `Phi n r m₀ = Phi n r (m₀ + q)` for two adjacent points of
the sparse support, the weight drops at least linearly with rate `c = κ (q-1)/2` on both
sides of the block `[m₀, m₀+q]`.
-/

namespace SparseFock

open scoped BigOperators Nat

variable {n : ℕ} {r : ℝ}

/-- `∑_{i<q} i = q(q-1)/2`, over the reals. -/
theorem sum_range_cast (q : ℕ) : ∑ i ∈ Finset.range q, (i : ℝ) = q * (q - 1) / 2 := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `∑_{i<q} (q-1-i) = q(q-1)/2`, over the reals. -/
theorem sum_range_cast_rev (q : ℕ) :
    ∑ i ∈ Finset.range q, ((q : ℝ) - 1 - i) = q * (q - 1) / 2 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, sum_range_cast]
  simp [nsmul_eq_mul]
  ring

/-- Telescoping: the increment of `Phi` over a block is the sum of the forward
differences. -/
theorem Phi_sub_Phi (n : ℕ) (r : ℝ) (m k : ℕ) :
    Phi n r (m + k) - Phi n r m = ∑ i ∈ Finset.range k, dstep n r (m + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, dstep, show m + (k + 1) = (m + k) + 1 by omega]
    ring

/-- The forward differences of `Phi` are decreasing (strict discrete concavity). -/
theorem dstep_antitone (n : ℕ) (r : ℝ) : Antitone (dstep n r) := by
  refine antitone_nat_of_succ_le (fun m => ?_)
  have := dstep_sub_dstep_succ_pos n r m
  linarith

/-- Quantitative concavity on a window: if the discrete curvature is at least `κ` on
`[m₀, m₀+q)`, then the forward differences decrease at rate at least `κ` there. -/
theorem dstep_gap {κ : ℝ} {m₀ q : ℕ}
    (hcurv : ∀ t, m₀ ≤ t → t < m₀ + q → κ ≤ dstep n r t - dstep n r (t + 1)) :
    ∀ i j : ℕ, m₀ ≤ i → i ≤ j → j ≤ m₀ + q →
      κ * ((j : ℝ) - i) ≤ dstep n r i - dstep n r j := by
  intro i j hi hij hj
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    simp
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hij' : i ≤ j := by omega
      have h1 := ih hij' (by omega)
      have h2 : κ ≤ dstep n r j - dstep n r (j + 1) := hcurv j (by omega) (by omega)
      push_cast
      push_cast at h1
      linarith
    · have : i = j + 1 := by omega
      subst this
      simp

/-- At a crossing (`Phi n r (m₀+q) = Phi n r m₀`) the left slope is at least
`κ (q-1)/2`. -/
theorem crossing_slope_left {κ : ℝ} {m₀ q : ℕ} (hq : 1 ≤ q)
    (hcross : Phi n r (m₀ + q) = Phi n r m₀)
    (hcurv : ∀ t, m₀ ≤ t → t < m₀ + q → κ ≤ dstep n r t - dstep n r (t + 1)) :
    κ * ((q : ℝ) - 1) / 2 ≤ dstep n r m₀ := by
  have hsum : ∑ i ∈ Finset.range q, dstep n r (m₀ + i) = 0 := by
    have := Phi_sub_Phi n r m₀ q
    rw [hcross] at this
    linarith [this]
  have hbd : ∀ i ∈ Finset.range q,
      dstep n r (m₀ + i) ≤ dstep n r m₀ - κ * i := by
    intro i hi
    have hi' : i < q := Finset.mem_range.1 hi
    have := dstep_gap hcurv m₀ (m₀ + i) le_rfl (by omega) (by omega)
    push_cast at this
    linarith
  have hle : (0:ℝ) ≤ ∑ i ∈ Finset.range q, (dstep n r m₀ - κ * i) := by
    rw [← hsum]
    exact Finset.sum_le_sum hbd
  have hcalc : ∑ i ∈ Finset.range q, (dstep n r m₀ - κ * (i : ℝ))
      = q * dstep n r m₀ - κ * (q * (q - 1) / 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, sum_range_cast]
    simp [nsmul_eq_mul]
  rw [hcalc] at hle
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have : κ * ((q : ℝ) - 1) / 2 * q ≤ dstep n r m₀ * q := by nlinarith
  exact le_of_mul_le_mul_right (by linarith) hqpos

/-- At a crossing the right slope is at most `-κ (q-1)/2`. -/
theorem crossing_slope_right {κ : ℝ} {m₀ q : ℕ} (hq : 1 ≤ q)
    (hcross : Phi n r (m₀ + q) = Phi n r m₀)
    (hcurv : ∀ t, m₀ ≤ t → t < m₀ + q → κ ≤ dstep n r t - dstep n r (t + 1)) :
    dstep n r (m₀ + q - 1) ≤ -(κ * ((q : ℝ) - 1) / 2) := by
  have hsum : ∑ i ∈ Finset.range q, dstep n r (m₀ + i) = 0 := by
    have := Phi_sub_Phi n r m₀ q
    rw [hcross] at this
    linarith [this]
  have hbd : ∀ i ∈ Finset.range q,
      dstep n r (m₀ + q - 1) + κ * ((q : ℝ) - 1 - i) ≤ dstep n r (m₀ + i) := by
    intro i hi
    have hi' : i < q := Finset.mem_range.1 hi
    have := dstep_gap hcurv (m₀ + i) (m₀ + q - 1) (by omega) (by omega) (by omega)
    have hcast : ((m₀ + q - 1 : ℕ) : ℝ) - ((m₀ + i : ℕ) : ℝ) = (q : ℝ) - 1 - i := by
      have : m₀ + q - 1 = m₀ + (q - 1) := by omega
      rw [this]
      push_cast [Nat.cast_sub hq]
      ring
    rw [hcast] at this
    linarith
  have hge : ∑ i ∈ Finset.range q, (dstep n r (m₀ + q - 1) + κ * ((q : ℝ) - 1 - i)) ≤ 0 := by
    rw [← hsum]
    exact Finset.sum_le_sum hbd
  have hcalc : ∑ i ∈ Finset.range q, (dstep n r (m₀ + q - 1) + κ * ((q : ℝ) - 1 - i))
      = q * dstep n r (m₀ + q - 1) + κ * (q * (q - 1) / 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, sum_range_cast_rev]
    simp [nsmul_eq_mul]
  rw [hcalc] at hge
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have : dstep n r (m₀ + q - 1) * q ≤ -(κ * ((q : ℝ) - 1) / 2) * q := by nlinarith
  exact le_of_mul_le_mul_right (by linarith) hqpos

/-- Linear decay of the weight to the left of the block. -/
theorem Phi_le_left {c : ℝ} {m₀ : ℕ} (hc : c ≤ dstep n r m₀) {m : ℕ} (hm : m ≤ m₀) :
    Phi n r m ≤ Phi n r m₀ - c * ((m₀ : ℝ) - m) := by
  obtain ⟨k, hk⟩ : ∃ k, m₀ = m + k := ⟨m₀ - m, by omega⟩
  subst hk
  have h := Phi_sub_Phi n r m k
  have hbd : ∀ i ∈ Finset.range k, c ≤ dstep n r (m + i) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.1 hi
    exact le_trans hc (dstep_antitone n r (by omega))
  have : (k : ℝ) * c ≤ ∑ i ∈ Finset.range k, dstep n r (m + i) := by
    have := Finset.sum_le_sum hbd
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  push_cast
  push_cast at h
  linarith

/-- Linear decay of the weight to the right of the block. -/
theorem Phi_le_right {c : ℝ} {m₀ q : ℕ} (hq : 1 ≤ q)
    (hc : dstep n r (m₀ + q - 1) ≤ -c) {m : ℕ} (hm : m₀ + q ≤ m) :
    Phi n r m ≤ Phi n r (m₀ + q) - c * ((m : ℝ) - (m₀ + q)) := by
  obtain ⟨k, hk⟩ : ∃ k, m = (m₀ + q) + k := ⟨m - (m₀ + q), by omega⟩
  subst hk
  have h := Phi_sub_Phi n r (m₀ + q) k
  have hbd : ∀ i ∈ Finset.range k, dstep n r ((m₀ + q) + i) ≤ -c := by
    intro i hi
    have hi' : i < k := Finset.mem_range.1 hi
    exact le_trans (dstep_antitone n r (by omega)) hc
  have : ∑ i ∈ Finset.range k, dstep n r ((m₀ + q) + i) ≤ (k : ℝ) * (-c) := by
    have := Finset.sum_le_sum hbd
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  push_cast
  push_cast at h
  linarith

end SparseFock
