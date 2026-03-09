import LeanShowcase.TrigonometricExtrema
import LeanShowcase.LogExtrema

/-!
# LeanShowcase

这个文件提供仓库的统一导入入口。
-/

namespace LeanShowcase

theorem trigMaximumOnIcc :
    IsGreatest {f : ℝ | ∃ (x : ℝ), x ∈ Set.Icc (0 : ℝ) (Real.pi / 4) ∧ f = 5 * Real.cos x - Real.cos (5 * x)}
      (3 * Real.sqrt 3) :=
  trig_maximum_on_Icc

theorem cosineIntervalWitness
    (θ a : ℝ) (hθ_left : 0 < θ) (hθ_right : θ < Real.pi) :
    ∃ y : ℝ, y ∈ Set.Icc (a - θ) (a + θ) ∧ Real.cos y ≤ Real.cos θ :=
  cosine_interval_witness θ a hθ_left hθ_right

theorem leastPhaseShiftUpperBound :
    IsLeast {b : ℝ | ∃ (φ : ℝ), ∀ x : ℝ, 5 * Real.cos x - Real.cos (5 * x + φ) ≤ b}
      (3 * Real.sqrt 3) :=
  least_phase_shift_upper_bound

theorem tangentLineAtOne :
    let a := 0
    (f a 1 = tangent_line_y 1) ∧ (deriv (f a) 1 = deriv tangent_line_y 1) :=
  tangent_line_at_one

theorem twoExtremaSumBounds
    (a : ℝ) (x₁ x₂ : ℝ) (h₁ : 0 < x₁) (h₂ : 0 < x₂) (h_order : x₁ < x₂)
    (hx1 : IsLocalExtr (f a) x₁) (hx2 : IsLocalExtr (f a) x₂) :
    2 < x₁ + x₂ ∧ x₁ + x₂ < 3 * Real.exp (a - 1) - 1 :=
  two_extrema_sum_bounds a x₁ x₂ h₁ h₂ h_order hx1 hx2

end LeanShowcase