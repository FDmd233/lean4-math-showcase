import RequestProject.TwoTerm
import RequestProject.ZeroCount

/-!
# Specialisation of the local zero count to the sparse Fock series

`ZeroCount.lean` proves an abstract statement: under a two-term domination near a model
center, a function has at most one zero in a small disc and every zero there is simple.
Here that statement is specialised to `f = F_p^{(n)}`, with the two principal terms
`A_j z^{m_j} + A_{j+1} z^{m_j + q_j}` and the model centre `ρ e^{iθ}`, `(e^{iθ})^q = -1`.

The tail is fed in exactly as in `TwoTerm.exists_zero_near_model`, through the bound of
`Tail.tail_sum_bound`.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

variable {p : ℝ} {n m₀ q : ℕ}

/-- Small logarithmic deviation: if `|x| ≤ 2 s` with `2 s ≤ 1/4`, then
`|log (1 + x)| ≤ 4 s`. -/
theorem abs_log_le_of_near_one {y s : ℝ} (hs : 0 < s) (hs4 : 2 * s ≤ 1/4)
    (hy : |y - 1| ≤ 2 * s) : |Real.log y| ≤ 4 * s := by
  have hy1 : 1 - 2 * s ≤ y := by
    have := abs_le.1 hy
    linarith [this.1]
  have hy2 : y ≤ 1 + 2 * s := by
    have := abs_le.1 hy
    linarith [this.2]
  have hypos : 0 < y := by linarith
  rw [abs_le]
  constructor
  · -- `log y ≥ -4 s`
    have hexp : Real.exp (-(4 * s)) ≤ 1 - 2 * s := by
      have h1 : Real.exp (-(4 * s)) * Real.exp (4 * s) = 1 := by
        rw [← Real.exp_add]; simp
      have h2 : 1 + 4 * s ≤ Real.exp (4 * s) := by
        have := Real.add_one_le_exp (4 * s)
        linarith
      have h3 : (1 - 2 * s) * (1 + 4 * s) ≥ 1 := by nlinarith
      have h4 : (0:ℝ) < Real.exp (4 * s) := Real.exp_pos _
      nlinarith [Real.exp_pos (-(4 * s))]
    have := Real.exp_le_exp (x := -(4 * s)) (y := Real.log y)
    have hlog : Real.exp (Real.log y) = y := Real.exp_log hypos
    have : Real.exp (-(4 * s)) ≤ Real.exp (Real.log y) := by rw [hlog]; linarith
    exact (Real.exp_le_exp).1 this
  · -- `log y ≤ 4 s`
    have h2 : 1 + 2 * s ≤ Real.exp (2 * s) := by
      have := Real.add_one_le_exp (2 * s)
      linarith
    have h3 : y ≤ Real.exp (4 * s) := by
      have : Real.exp (2 * s) ≤ Real.exp (4 * s) := Real.exp_le_exp.2 (by linarith)
      linarith
    have hlog : Real.exp (Real.log y) = y := Real.exp_log hypos
    have : Real.exp (Real.log y) ≤ Real.exp (4 * s) := by rw [hlog]; exact h3
    exact (Real.exp_le_exp).1 this

/-- **At most one zero near a model zero, and it is simple.**  Companion of
`exists_zero_near_model`: with the same tail hypothesis, the derivative `F_p^{(n)}` has at
most one zero in the disc of radius `ρ s` about the model zero `ρ e^{iθ}`, and any zero
there is simple. -/
theorem unique_zero_near_model
    {ρ θ s K : ℝ}
    (hρ : 0 < ρ) (hq : 1 ≤ q)
    (hphase : (Complex.exp ((θ : ℝ) * Complex.I)) ^ q = -1)
    (hsupp₀ : IsSupp p (m₀ + n))
    (hcrossA : dcoeff p n m₀ * ρ ^ m₀ = dcoeff p n (m₀ + q) * ρ ^ (m₀ + q))
    (hs : 0 < s) (hqs : (q : ℝ) * s ≤ 1/8) (hK : 0 ≤ K)
    (htail : ∀ σ : ℝ, |σ| ≤ 4 * s →
      ∑' m : ℕ, (if m = m₀ ∨ m = m₀ + q then 0
        else dcoeff p n m * (ρ * Real.exp σ) ^ m)
        ≤ Real.exp (Phi n ρ m₀ + (m₀ : ℝ) * σ) * K)
    (hKs : K < (q : ℝ) * s / 2) :
    (∀ z₁ z₂ : ℂ,
        ‖z₁ - (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ ≤ ρ * s →
        ‖z₂ - (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ ≤ ρ * s →
        iteratedDeriv n (F p) z₁ = 0 → iteratedDeriv n (F p) z₂ = 0 → z₁ = z₂) ∧
      (∀ z : ℂ, ‖z - (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ ≤ ρ * s →
        iteratedDeriv n (F p) z = 0 → deriv (iteratedDeriv n (F p)) z ≠ 0) := by
  have hqR : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : s ≤ 1/8 := by nlinarith
  set z₀ : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) with hz₀def
  have hz₀norm : ‖z₀‖ = ρ := by
    rw [hz₀def, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
  have hA₀pos : 0 < dcoeff p n m₀ := dcoeff_pos_of_isSupp p n m₀ hsupp₀
  set A : ℂ := ((dcoeff p n m₀ : ℝ) : ℂ) with hAdef
  have hAne : A ≠ 0 := by
    rw [hAdef]
    simpa using ne_of_gt hA₀pos
  have hAnorm : ‖A‖ = dcoeff p n m₀ := by
    rw [hAdef, Complex.norm_real, Real.norm_of_nonneg hA₀pos.le]
  have hA₁ρ : dcoeff p n (m₀ + q) * ρ ^ q = dcoeff p n m₀ := by
    have hρm : (0:ℝ) < ρ ^ m₀ := by positivity
    have h : dcoeff p n m₀ * ρ ^ m₀ = dcoeff p n (m₀ + q) * ρ ^ q * ρ ^ m₀ := by
      rw [hcrossA, pow_add]; ring
    exact (mul_right_cancel₀ (ne_of_gt hρm) h).symm
  have hSexp : dcoeff p n m₀ * ρ ^ m₀ = Real.exp (Phi n ρ m₀) :=
    dcoeff_mul_pow_eq_exp_Phi p n m₀ hρ hsupp₀
  -- the model in the form `A z^{m₀} (1 - (z/z₀)^q)`
  have hmodel : ∀ z : ℂ,
      A * z ^ m₀ * (1 - (z / z₀) ^ q)
        = ((dcoeff p n m₀ : ℝ) : ℂ) * z ^ m₀
          + ((dcoeff p n (m₀ + q) : ℝ) : ℂ) * z ^ (m₀ + q) := by
    intro z
    have hz₀ne : z₀ ≠ 0 := by
      intro h; rw [h] at hz₀norm; simp at hz₀norm; exact absurd hz₀norm.symm (ne_of_gt hρ)
    have hz₀q : z₀ ^ q = -((ρ : ℂ) ^ q) := by
      rw [hz₀def, mul_pow, hphase]; ring
    have hρq : ((ρ : ℂ)) ^ q ≠ 0 := by
      refine pow_ne_zero _ ?_
      simpa using ne_of_gt hρ
    have hA : ((dcoeff p n (m₀ + q) : ℝ) : ℂ) * ((ρ : ℂ) ^ q) = A := by
      have h := congrArg (fun t : ℝ => (t : ℂ)) hA₁ρ
      push_cast at h ⊢
      rw [hAdef]; exact h
    have hdiv : (z / z₀) ^ q = z ^ q / z₀ ^ q := div_pow _ _ _
    rw [hdiv, hz₀q]
    have hexpand : A * z ^ m₀ * (1 - z ^ q / -((ρ:ℂ) ^ q))
        = A * z ^ m₀ + (A / ((ρ:ℂ)^q)) * z ^ (m₀ + q) := by
      field_simp
      ring
    have hAdiv : A / ((ρ:ℂ)^q) = ((dcoeff p n (m₀ + q) : ℝ) : ℂ) := by
      rw [← hA]
      field_simp
    rw [hexpand, hAdiv, hAdef]
  -- the domination hypothesis in `z`-coordinates
  have hdom : ∀ z : ℂ, ‖z - z₀‖ ≤ 2 * ρ * s →
      ‖iteratedDeriv n (F p) z - A * z ^ m₀ * (1 - (z / z₀) ^ q)‖ ≤ ‖A‖ * ‖z‖ ^ m₀ * K := by
    intro z hz
    have hznorm1 : |‖z‖ - ρ| ≤ 2 * ρ * s := by
      have h := abs_norm_sub_norm_le z z₀
      rw [hz₀norm] at h
      exact le_trans h hz
    have hzpos : 0 < ‖z‖ := by
      have := abs_le.1 hznorm1
      nlinarith [this.1, hρ, hs]
    set σ : ℝ := Real.log (‖z‖ / ρ) with hσdef
    have hratio : |‖z‖ / ρ - 1| ≤ 2 * s := by
      have hrw : ‖z‖ / ρ - 1 = (‖z‖ - ρ) / ρ := by field_simp
      rw [hrw, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
      calc |‖z‖ - ρ| ≤ 2 * ρ * s := hznorm1
        _ = 2 * s * ρ := by ring
    have hσ : |σ| ≤ 4 * s := abs_log_le_of_near_one hs (by linarith) hratio
    have hexpσ : ρ * Real.exp σ = ‖z‖ := by
      rw [hσdef, Real.exp_log (by positivity)]
      field_simp
    have h1 := norm_sub_two_terms_le p n m₀ q hq z
    rw [hmodel z]
    refine le_trans h1 ?_
    have h2 := htail σ hσ
    rw [hexpσ] at h2
    refine le_trans h2 (le_of_eq ?_)
    rw [Real.exp_add, ← hSexp, hAnorm]
    have h3 : Real.exp ((m₀ : ℝ) * σ) = (Real.exp σ) ^ m₀ := by
      rw [← Real.exp_nat_mul]
    have h4 : ‖z‖ ^ m₀ = ρ ^ m₀ * (Real.exp σ) ^ m₀ := by
      rw [← mul_pow, hexpσ]
    rw [h3, h4]
    ring
  exact unique_zero_of_two_term (iteratedDeriv_F_differentiable p n) hz₀norm hρ hAne hq
    hs hqs hK hdom hKs

end SparseFock
