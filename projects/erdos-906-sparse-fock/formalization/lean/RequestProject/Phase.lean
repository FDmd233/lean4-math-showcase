import RequestProject.Aux32

/-!
# The model phases

The zeros of the two-term model `A z^{m} + A' z^{m+q}` on the crossing circle of radius
`ρ` are the points `ρ e^{iθ}` with `(e^{iθ})^q = -1`, i.e. `θ = (2l+1)π/q`.  They have
angular mesh `2π/q`, so every prescribed angle is within `π/q` of one of them.
-/

namespace SparseFock

open scoped BigOperators

/-- There is a `q`-th model phase within `π / q` of any prescribed angle. -/
theorem exists_phase (q : ℕ) (hq : 1 ≤ q) (ang : ℝ) :
    ∃ θ : ℝ, (Complex.exp ((θ : ℝ) * Complex.I)) ^ q = -1 ∧ |θ - ang| ≤ Real.pi / q := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨l, hl⟩ : ∃ l : ℤ, |(ang * q / Real.pi - 1) / 2 - (l : ℝ)| ≤ 1 / 2 :=
    ⟨round ((ang * q / Real.pi - 1) / 2), abs_sub_round _⟩
  refine ⟨((2 * l + 1 : ℤ) : ℝ) * Real.pi / q, ?_, ?_⟩
  · have hstep : ((q : ℂ)) * (((((2 * l + 1 : ℤ) : ℝ) * Real.pi / q : ℝ) : ℂ) * Complex.I)
        = (l : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      have hq0 : (q : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      push_cast
      field_simp
    calc (Complex.exp (((((2 * l + 1 : ℤ) : ℝ) * Real.pi / q : ℝ) : ℂ) * Complex.I)) ^ q
        = Complex.exp ((q : ℂ) * (((((2 * l + 1 : ℤ) : ℝ) * Real.pi / q : ℝ) : ℂ)
            * Complex.I)) := (Complex.exp_nat_mul _ _).symm
      _ = Complex.exp ((l : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
            + (Real.pi : ℂ) * Complex.I) := by rw [hstep]
      _ = -1 := by
          rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
          ring
  · have hexpr : (((2 * l + 1 : ℤ) : ℝ) * Real.pi / q) - ang
        = 2 * Real.pi * ((l : ℝ) - (ang * q / Real.pi - 1) / 2) / q := by
      field_simp
      push_cast
      ring
    rw [hexpr, abs_div, abs_of_pos hqR]
    refine (div_le_div_iff_of_pos_right hqR).mpr ?_
    have habs : |(l : ℝ) - (ang * q / Real.pi - 1) / 2| ≤ 1 / 2 := by
      rw [abs_sub_comm]
      exact hl
    calc |2 * Real.pi * ((l : ℝ) - (ang * q / Real.pi - 1) / 2)|
        = 2 * Real.pi * |(l : ℝ) - (ang * q / Real.pi - 1) / 2| := by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      _ ≤ 2 * Real.pi * (1 / 2) := by
          exact mul_le_mul_of_nonneg_left habs (by positivity)
      _ = Real.pi := by ring

end SparseFock
