import RequestProject.ExclusionAux

/-!
# Zeros in a transition region lie in a model disk

If the radius `r = ρ e^σ` is so close to a crossing radius `ρ = ρ_j` that
`|q_j σ| ≤ 2`, and if the tail of `F_p^{(n)}` outside the two principal terms is at most
`K` times the principal term, then every zero of `F_p^{(n)}` on that circle satisfies
`|1 + (z/ρ)^{q_j}| ≤ K`, hence (by `RootLoc.exists_model_root_near`) lies within
`16 K ρ / q_j` of one of the model centers `ρ exp((2ℓ+1)π i / q_j)`.

This is steps 4–6 of the exclusion argument.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- **Zeros in a transition region.** -/
theorem zero_in_model_disk_of_transition {p : ℝ} {n m₀ q : ℕ} {ρ σ K : ℝ}
    (hρ : 0 < ρ) (hq : 1 ≤ q)
    (hsupp₀ : IsSupp p (m₀ + n))
    (hcrossA : dcoeff p n m₀ * ρ ^ m₀ = dcoeff p n (m₀ + q) * ρ ^ (m₀ + q))
    (hσ : |(q : ℝ) * σ| ≤ 2) (hKnn : 0 ≤ K) (hK4 : K ≤ 1/4)
    (htail : ∑' m : ℕ, (if m = m₀ ∨ m = m₀ + q then 0
        else dcoeff p n m * (ρ * Real.exp σ) ^ m)
        ≤ Real.exp (Phi n ρ m₀ + (m₀ : ℝ) * σ) * K)
    {z : ℂ} (hznorm : ‖z‖ = ρ * Real.exp σ)
    (hz0 : iteratedDeriv n (F p) z = 0) :
    ∃ l : ℕ, l < q ∧
      ‖z - (ρ : ℂ) * Complex.exp ((((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ)) : ℝ) * Complex.I)‖
        ≤ 16 * K * ρ / (q : ℝ) := by
  have hqR : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  have hzpos : 0 < ‖z‖ := by rw [hznorm]; positivity
  have hzne : z ≠ 0 := norm_pos_iff.1 hzpos
  have hρC : ((ρ : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hρ
  set w : ℂ := z / (ρ : ℂ) with hwdef
  have hwnorm : ‖w‖ = Real.exp σ := by
    rw [hwdef, norm_div, hznorm, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    field_simp
  have hwne : w ≠ 0 := by
    rw [hwdef]
    exact div_ne_zero hzne hρC
  have hlogw : Real.log ‖w‖ = σ := by rw [hwnorm, Real.log_exp]
  -- the coefficient identity
  have hA₀pos : 0 < dcoeff p n m₀ := dcoeff_pos_of_isSupp p n m₀ hsupp₀
  have hA₁ρ : dcoeff p n (m₀ + q) * ρ ^ q = dcoeff p n m₀ := by
    have hρm : (0:ℝ) < ρ ^ m₀ := by positivity
    have h : dcoeff p n m₀ * ρ ^ m₀ = dcoeff p n (m₀ + q) * ρ ^ q * ρ ^ m₀ := by
      rw [hcrossA, pow_add]; ring
    exact (mul_right_cancel₀ (ne_of_gt hρm) h).symm
  -- the two principal terms
  have hprin : ((dcoeff p n m₀ : ℝ) : ℂ) * z ^ m₀
      + ((dcoeff p n (m₀ + q) : ℝ) : ℂ) * z ^ (m₀ + q)
      = ((dcoeff p n m₀ : ℝ) : ℂ) * z ^ m₀ * (1 + w ^ q) := by
    have hA : ((dcoeff p n (m₀ + q) : ℝ) : ℂ) * ((ρ : ℂ) ^ q)
        = ((dcoeff p n m₀ : ℝ) : ℂ) := by
      have h := congrArg (fun t : ℝ => (t : ℂ)) hA₁ρ
      push_cast at h
      exact h
    have h1 : ((dcoeff p n m₀ : ℝ) : ℂ) * z ^ m₀ * w ^ q
        = ((dcoeff p n (m₀ + q) : ℝ) : ℂ) * z ^ (m₀ + q) := by
      rw [hwdef, div_pow, pow_add, ← hA]
      have hρq : ((ρ : ℂ)) ^ q ≠ 0 := pow_ne_zero _ hρC
      field_simp
    rw [mul_add, mul_one, h1]
  -- the modulus of the principal term
  have hmodprin : ‖((dcoeff p n m₀ : ℝ) : ℂ) * z ^ m₀‖ = Real.exp (Phi n ρ m₀ + (m₀ : ℝ) * σ) := by
    rw [norm_mul, norm_pow, hznorm, Complex.norm_real, Real.norm_of_nonneg hA₀pos.le]
    rw [← Phi_exp_shift n m₀ hρ]
    exact dcoeff_mul_pow_eq_exp_Phi p n m₀ (by positivity) hsupp₀
  -- the estimate
  have hbound := norm_sub_two_terms_le p n m₀ q hq z
  rw [hz0, hprin, zero_sub, norm_neg, hznorm] at hbound
  have hkey : ‖((dcoeff p n m₀ : ℝ) : ℂ) * z ^ m₀‖ * ‖1 + w ^ q‖
      ≤ Real.exp (Phi n ρ m₀ + (m₀ : ℝ) * σ) * K := by
    rw [← norm_mul]
    exact le_trans hbound htail
  rw [hmodprin] at hkey
  have hEpos : (0:ℝ) < Real.exp (Phi n ρ m₀ + (m₀ : ℝ) * σ) := Real.exp_pos _
  have hclose : ‖1 + w ^ q‖ ≤ K := le_of_mul_le_mul_left (by linarith [hkey]) hEpos
  -- root localisation
  have hmod : |(q : ℝ) * Real.log ‖w‖| ≤ 2 := by rw [hlogw]; exact hσ
  obtain ⟨l, hl, hdist⟩ := exists_model_root_near hq hwne hKnn hK4 hmod hclose
  refine ⟨l, hl, ?_⟩
  have hz : z - (ρ : ℂ)
      * Complex.exp ((((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ)) : ℝ) * Complex.I)
      = (ρ : ℂ) * (w - Complex.exp ((((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ)) : ℝ) * Complex.I))
      := by
    rw [hwdef]
    field_simp
  rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  calc ρ * ‖w - Complex.exp ((((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ)) : ℝ) * Complex.I)‖
      ≤ ρ * (16 * K / (q : ℝ)) := mul_le_mul_of_nonneg_left hdist hρ.le
    _ = 16 * K * ρ / (q : ℝ) := by ring

end SparseFock
