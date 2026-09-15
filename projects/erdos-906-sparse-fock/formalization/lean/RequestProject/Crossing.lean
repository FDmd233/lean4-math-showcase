import RequestProject.Aux32

/-!
# The crossing identities and the local curvature bounds

At the crossing radius `ρ_j` the two adjacent principal terms of `F_{3/2}^{(n)}` have
equal modulus; the lemmas here record that identity, the sparse-support gap structure, and
the two slope bounds coming from the discrete concavity of the logarithmic weights.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- The support point `m_j` is active. -/
theorem isSupp_mOf {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j) :
    IsSupp (3/2) (mOf (3/2) n j + n) := by
  refine ⟨j, hj, ?_⟩
  simp only [mOf]
  omega

theorem nu32_mono {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) : nu (3/2) i ≤ nu (3/2) k := by
  rcases eq_or_lt_of_le hik with h | h
  · rw [h]
  · exact (nu_lt_nu (by norm_num) hi h).le

/-- Every active support point other than the two principal ones is at distance at least
`Q = min (q_{j-1}) (q_{j+1})` from the block `[m_j, m_j + q_j]`. -/
theorem supp_gap {n j : ℕ} (hj : 2 ≤ j) (hn : n ≤ nu (3/2) j) {m : ℕ}
    (hm : dcoeff (3/2) n m ≠ 0) (hne1 : m ≠ mOf (3/2) n j)
    (hne2 : m ≠ mOf (3/2) n j + qgap (3/2) j) :
    m + min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) ≤ mOf (3/2) n j ∨
      mOf (3/2) n j + qgap (3/2) j + min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) ≤ m := by
  have hj1 : 1 ≤ j := by omega
  have hsupp : IsSupp (3/2) (m + n) := by
    by_contra h
    exact hm (by rw [dcoeff, if_neg h])
  obtain ⟨s, hs1, hs2⟩ := hsupp
  -- the basic identities
  have hnuj : nu (3/2) j = n + mOf (3/2) n j := nu_eq_add_mOf hn
  have hgapj : nu (3/2) j + qgap (3/2) j = nu (3/2) (j + 1) := nu_add_qgap (by norm_num) hj1
  have hgapjm : nu (3/2) (j - 1) + qgap (3/2) (j - 1) = nu (3/2) j := by
    have h := nu_add_qgap (p := (3/2 : ℝ)) (by norm_num) (show 1 ≤ j - 1 by omega)
    rwa [show j - 1 + 1 = j by omega] at h
  have hgapj1 : nu (3/2) (j + 1) + qgap (3/2) (j + 1) = nu (3/2) (j + 2) := by
    have h := nu_add_qgap (p := (3/2 : ℝ)) (by norm_num) (show 1 ≤ j + 1 by omega)
    rwa [show j + 1 + 1 = j + 2 by omega] at h
  rcases lt_trichotomy s j with hlt | heq | hgt
  · -- `s ≤ j - 1`
    left
    have hle : nu (3/2) s ≤ nu (3/2) (j - 1) := nu32_mono hs1 (by omega)
    have hmin : min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) ≤ qgap (3/2) (j - 1) :=
      min_le_left _ _
    omega
  · rw [heq] at hs2
    exact absurd (by omega : m = mOf (3/2) n j) hne1
  · rcases eq_or_lt_of_le (show j + 1 ≤ s by omega) with heq1 | hgt1
    · rw [← heq1] at hs2
      exact absurd (by omega : m = mOf (3/2) n j + qgap (3/2) j) hne2
    · right
      have hle : nu (3/2) (j + 2) ≤ nu (3/2) s := nu32_mono (by omega) (by omega)
      have hmin : min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) ≤ qgap (3/2) (j + 1) :=
        min_le_right _ _
      omega

/-- At the crossing radius the two adjacent principal weights agree. -/
theorem crossing_Phi {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j) :
    Phi n (rho (3/2) n j) (mOf (3/2) n j + qgap (3/2) j)
      = Phi n (rho (3/2) n j) (mOf (3/2) n j) := by
  have hq : 1 ≤ qgap (3/2) j := one_le_qgap (by norm_num) hj
  have hqR : (0:ℝ) < ((qgap (3/2) j : ℕ) : ℝ) := by exact_mod_cast hq
  have hsum := Phi_sub_Phi n (rho (3/2) n j) (mOf (3/2) n j) (qgap (3/2) j)
  have hlog := log_rho_eq_range (p := (3/2 : ℝ)) (by norm_num) hj hn
  have hd : ∀ t : ℕ,
      dstep n (rho (3/2) n j) t = Real.log (rho (3/2) n j) - fterm n t := by
    intro t
    rw [dstep_eq, fterm]
    ring
  have hrewrite :
      ∑ i ∈ Finset.range (qgap (3/2) j), dstep n (rho (3/2) n j) (mOf (3/2) n j + i)
        = ((qgap (3/2) j : ℕ) : ℝ) * Real.log (rho (3/2) n j)
          - ∑ i ∈ Finset.range (qgap (3/2) j), fterm n (mOf (3/2) n j + i) := by
    simp only [hd]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  rw [hrewrite] at hsum
  have hval : ∑ i ∈ Finset.range (qgap (3/2) j), fterm n (mOf (3/2) n j + i)
      = ((qgap (3/2) j : ℕ) : ℝ) * Real.log (rho (3/2) n j) := by
    rw [hlog]
    field_simp
  rw [hval] at hsum
  linarith

/-- The crossing identity for the coefficients. -/
theorem crossing_dcoeff {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j) :
    dcoeff (3/2) n (mOf (3/2) n j) * (rho (3/2) n j) ^ (mOf (3/2) n j)
      = dcoeff (3/2) n (mOf (3/2) n j + qgap (3/2) j) *
        (rho (3/2) n j) ^ (mOf (3/2) n j + qgap (3/2) j) := by
  have hsupp0 : IsSupp (3/2) (mOf (3/2) n j + n) := isSupp_mOf hj hn
  have hn1 : n ≤ nu (3/2) (j + 1) := le_trans hn (nu_lt_nu_succ (by norm_num) hj).le
  have hsupp1 : IsSupp (3/2) (mOf (3/2) n j + qgap (3/2) j + n) := by
    refine ⟨j + 1, by omega, ?_⟩
    have h := mOf_succ (p := (3/2 : ℝ)) (by norm_num) hj hn
    simp only [mOf] at h ⊢
    omega
  rw [dcoeff_mul_pow_eq_exp_Phi _ _ _ (rho_pos _ _ _) hsupp0,
    dcoeff_mul_pow_eq_exp_Phi _ _ _ (rho_pos _ _ _) hsupp1, crossing_Phi hj hn]

/-- The two slope bounds at a crossing radius, with `κ = 1/(2(m+q+2))`. -/
theorem crossing_slopes32 {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j)
    (hsmall : mOf (3/2) n j + qgap (3/2) j + 2 ≤ n) :
    (1 / (2 * (((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2)))
        * (((qgap (3/2) j : ℕ) : ℝ) - 1) / 2
        ≤ dstep n (rho (3/2) n j) (mOf (3/2) n j) ∧
      dstep n (rho (3/2) n j) (mOf (3/2) n j + qgap (3/2) j - 1)
        ≤ -((1 / (2 * (((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2)))
          * (((qgap (3/2) j : ℕ) : ℝ) - 1) / 2) := by
  have hq : 1 ≤ qgap (3/2) j := one_le_qgap (by norm_num) hj
  have hcross := crossing_Phi hj hn
  have hcurv : ∀ t : ℕ, mOf (3/2) n j ≤ t → t < mOf (3/2) n j + qgap (3/2) j →
      (1 / (2 * (((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2)))
        ≤ dstep n (rho (3/2) n j) t - dstep n (rho (3/2) n j) (t + 1) := by
    intro t ht1 ht2
    refine le_trans ?_ (dstep_curvature_lower n (rho (3/2) n j) t)
    have hMpos : (0:ℝ) < ((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2 := by
      have h1 : (0:ℝ) ≤ ((mOf (3/2) n j : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : (0:ℝ) ≤ ((qgap (3/2) j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have htcast : (t : ℝ) + 2 ≤ ((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2 := by
      have : (t : ℝ) ≤ ((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : t ≤ mOf (3/2) n j + qgap (3/2) j)
      linarith
    have h1 : 1 / (((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2) ≤ 1 / ((t : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) htcast
    have hncast : ((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2 ≤ (n : ℝ) := by
      exact_mod_cast hsmall
    have h2 : 1 / (2 * ((n : ℝ) + t + 1))
        ≤ 1 / (2 * (((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2)) := by
      refine one_div_le_one_div_of_le (by linarith) ?_
      have ht0 : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
      linarith
    have hhalf : 1 / (2 * (((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2))
        = (1 / (((mOf (3/2) n j : ℕ) : ℝ) + ((qgap (3/2) j : ℕ) : ℝ) + 2)) / 2 := by
      field_simp
    rw [hhalf] at h2 ⊢
    linarith
  exact ⟨crossing_slope_left hq hcross hcurv, crossing_slope_right hq hcross hcurv⟩

end SparseFock
