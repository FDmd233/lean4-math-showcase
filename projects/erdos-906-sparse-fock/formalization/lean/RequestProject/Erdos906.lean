import RequestProject.Covering32

/-!
# Erdős Problem 906 for the sparse Fock series with `p = 3/2`

The main theorem of this development: the entire function

`F_{3/2}(z) = ∑_{j ≥ 1} z^{ν_j} / √(ν_j !)`,  `ν_j = ⌊j^{3/2}⌋`,

has the *cofinite* high-derivative zero-hitting property required by Erdős
Problem 906: for every nonempty open set `U ⊆ ℂ` there is an `N` such that for
**every** `n ≥ N` the `n`-th derivative `F_{3/2}^{(n)}` has a zero in `U`.
-/

namespace SparseFock

open scoped BigOperators

/-- Any nonempty open subset of `ℂ` contains a nonzero point. -/
theorem exists_ne_zero_mem_of_isOpen {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ w ∈ U, w ≠ 0 := by
  obtain ⟨w, hw⟩ := hne
  by_cases hw0 : w = 0
  · subst hw0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 hw
    refine ⟨((ε / 2 : ℝ) : ℂ), hball ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
      linarith
    · simp only [ne_eq, Complex.ofReal_eq_zero]
      intro h
      linarith
  · exact ⟨w, hw, hw0⟩

/-- **Erdős Problem 906 for the `p = 3/2` sparse Fock construction.**
For every nonempty open `U ⊆ ℂ` there is `N` such that for every `n ≥ N` the `n`-th
derivative of `F_{3/2}` has a zero in `U`. -/
theorem erdos906_sparse_fock_p32 (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z ∈ U, iteratedDeriv n (F (3/2)) z = 0 := by
  obtain ⟨w, hwU, hw0⟩ := exists_ne_zero_mem_of_isOpen hU hne
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU w hwU
  set δ : ℝ := min (ε / 2) (‖w‖ / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨N, hN⟩ := annular_covering (a := ‖w‖ / 2) (b := 2 * ‖w‖) (η := δ)
    (by linarith) (by linarith) hδpos
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz0, hzd⟩ := hN n hn w (by linarith) (by linarith)
  refine ⟨z, ?_, hz0⟩
  refine hball ?_
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hzd hδε

end SparseFock
