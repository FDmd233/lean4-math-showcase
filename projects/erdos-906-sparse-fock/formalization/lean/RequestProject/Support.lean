import Mathlib

/-!
# The sparse support `ν_j = ⌊j^p⌋` and its gaps

This file develops the elementary part of Lemma 2.1 of the paper
*Zeros of high derivatives of sparse Fock series*: the exponents `ν_j = ⌊j ^ p⌋`
are strictly increasing (for `p ≥ 1`, `j ≥ 1`) and the gaps
`q_j = ν_{j+1} - ν_j` satisfy `p j^{p-1} - 1 ≤ q_j ≤ p (j+1)^{p-1} + 1`.
-/

namespace SparseFock

open scoped BigOperators

/-- The support exponents `ν_j = ⌊j ^ p⌋`. -/
noncomputable def nu (p : ℝ) (j : ℕ) : ℕ := ⌊(j : ℝ) ^ p⌋₊

/-- The gap `q_j = ν_{j+1} - ν_j`. -/
noncomputable def qgap (p : ℝ) (j : ℕ) : ℕ := nu p (j + 1) - nu p j

variable {p : ℝ} {i j : ℕ}

theorem nu_one (p : ℝ) : nu p 1 = 1 := by
  simp [nu]

/-- Mean value bounds for the increment of `t ↦ t^p` over a unit interval. -/
theorem rpow_succ_sub_rpow_bounds (hp : 1 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    p * x ^ (p - 1) ≤ (x + 1) ^ p - x ^ p ∧ (x + 1) ^ p - x ^ p ≤ p * (x + 1) ^ (p - 1) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hderiv : ∀ y ∈ Set.Ioo x (x + 1), HasDerivAt (fun t : ℝ => t ^ p) (p * y ^ (p - 1)) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (lt_trans hx0 hy.1)
    simpa [mul_comm] using Real.hasDerivAt_rpow_const (p := p) (Or.inl hy0)
  have hcont : ContinuousOn (fun t : ℝ => t ^ p) (Set.Icc x (x + 1)) :=
    ContinuousOn.rpow_const (f := fun t : ℝ => t) continuousOn_id
      (fun y hy => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 hy.1)))
  obtain ⟨c, hc, hceq⟩ :=
    exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ p) (fun y => p * y ^ (p - 1))
      (by linarith : x < x + 1) hcont hderiv
  have hc0 : (0:ℝ) < c := lt_trans hx0 hc.1
  have hslope : (x + 1) ^ p - x ^ p = p * c ^ (p - 1) := by
    have : ((x + 1) ^ p - x ^ p) / (x + 1 - x) = (x + 1) ^ p - x ^ p := by
      norm_num
    rw [← this, ← hceq]
  have hmono : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → u ^ (p - 1) ≤ v ^ (p - 1) := by
    intro u v hu huv
    exact Real.rpow_le_rpow hu huv (by linarith)
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  constructor
  · rw [hslope]
    exact mul_le_mul_of_nonneg_left (hmono (le_of_lt hx0) (le_of_lt hc.1)) (le_of_lt hp0)
  · rw [hslope]
    exact mul_le_mul_of_nonneg_left (hmono (le_of_lt hc0) (le_of_lt hc.2)) (le_of_lt hp0)

/-- The increment of `t ↦ t^p` over a unit interval starting at `x ≥ 1` is at least one. -/
theorem one_le_rpow_succ_sub_rpow (hp : 1 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ (x + 1) ^ p - x ^ p := by
  refine le_trans ?_ (rpow_succ_sub_rpow_bounds hp hx).1
  have h1 : (1:ℝ) ≤ x ^ (p - 1) := Real.one_le_rpow hx (by linarith)
  nlinarith

/-- For `p ≥ 1` the exponent `ν_j` is at least `j`. -/
theorem le_nu (hp : 1 ≤ p) (j : ℕ) : j ≤ nu p j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · simp [h]
  · have hx : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast h
    have : (j : ℝ) ≤ (j : ℝ) ^ p := by
      calc (j : ℝ) = (j : ℝ) ^ (1:ℝ) := by rw [Real.rpow_one]
        _ ≤ (j : ℝ) ^ p := Real.rpow_le_rpow_of_exponent_le hx hp
    exact Nat.le_floor (by exact_mod_cast this)

/-- Strict monotonicity of the support exponents (Lemma 2.1). -/
theorem nu_lt_nu_succ (hp : 1 ≤ p) (hj : 1 ≤ j) : nu p j < nu p (j + 1) := by
  have hx : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hstep : ((j : ℝ)) ^ p + 1 ≤ ((j : ℝ) + 1) ^ p := by
    have := one_le_rpow_succ_sub_rpow hp hx
    linarith
  have hfl : ((nu p j : ℝ)) ≤ ((j : ℝ)) ^ p :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have : ((nu p j + 1 : ℕ) : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) ^ p := by
    push_cast
    push_cast at hfl
    linarith
  have := Nat.le_floor this
  simpa [nu] using this

theorem one_le_qgap (hp : 1 ≤ p) (hj : 1 ≤ j) : 1 ≤ qgap p j := by
  have := nu_lt_nu_succ hp hj
  simp only [qgap]
  omega

theorem nu_add_qgap (hp : 1 ≤ p) (hj : 1 ≤ j) : nu p j + qgap p j = nu p (j + 1) := by
  have := (nu_lt_nu_succ hp hj).le
  simp only [qgap]
  omega

theorem nu_lt_nu (hp : 1 ≤ p) (hi : 1 ≤ i) (hij : i < j) : nu p i < nu p j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact lt_trans (ih h) (nu_lt_nu_succ hp (le_trans hi (by omega)))
    · subst h
      exact nu_lt_nu_succ hp hi

/-- The gap is bounded above by the derivative of `t ↦ t^p` at the right endpoint, plus one. -/
theorem qgap_le (hp : 1 ≤ p) (hj : 1 ≤ j) :
    (qgap p j : ℝ) ≤ p * ((j : ℝ) + 1) ^ (p - 1) + 1 := by
  have hx : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hcast : (qgap p j : ℝ) = (nu p (j + 1) : ℝ) - (nu p j : ℝ) := by
    have := (nu_lt_nu_succ hp hj).le
    simp only [qgap]
    push_cast [Nat.cast_sub this]
    ring
  have h1 : ((nu p (j + 1) : ℝ)) ≤ (((j : ℝ) + 1)) ^ p := by
    have := Nat.floor_le (Real.rpow_nonneg (le_of_lt (by positivity : (0:ℝ) < (j:ℝ) + 1)) p)
    simpa [nu] using this
  have h2 : ((j : ℝ)) ^ p - 1 ≤ ((nu p j : ℝ)) := by
    have := Nat.lt_floor_add_one (((j : ℝ)) ^ p)
    simp only [nu]
    linarith
  have h3 := (rpow_succ_sub_rpow_bounds hp hx).2
  rw [hcast]
  linarith

/-- The gap is bounded below by the derivative of `t ↦ t^p` at the left endpoint, minus one. -/
theorem le_qgap (hp : 1 ≤ p) (hj : 1 ≤ j) :
    p * (j : ℝ) ^ (p - 1) - 1 ≤ (qgap p j : ℝ) := by
  have hx : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hcast : (qgap p j : ℝ) = (nu p (j + 1) : ℝ) - (nu p j : ℝ) := by
    have := (nu_lt_nu_succ hp hj).le
    simp only [qgap]
    push_cast [Nat.cast_sub this]
    ring
  have h1 : (((j : ℝ) + 1)) ^ p - 1 ≤ ((nu p (j + 1) : ℝ)) := by
    have := Nat.lt_floor_add_one ((((j : ℕ) + 1 : ℝ)) ^ p)
    have hnu : nu p (j + 1) = ⌊(((j : ℝ) + 1)) ^ p⌋₊ := by
      simp [nu]
    rw [hnu]
    linarith
  have h2 : ((nu p j : ℝ)) ≤ ((j : ℝ)) ^ p :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have h3 := (rpow_succ_sub_rpow_bounds hp hx).1
  rw [hcast]
  linarith

theorem tendsto_nu_atTop (hp : 1 ≤ p) :
    Filter.Tendsto (nu p) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono (le_nu hp) Filter.tendsto_id

end SparseFock
