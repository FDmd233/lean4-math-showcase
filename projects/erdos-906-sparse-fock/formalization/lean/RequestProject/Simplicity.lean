import RequestProject.Annulus

/-!
# Eventual simplicity of the annular zeros (`p = 3/2`)

Combining

* `annular_zero_exclusion_p32` — every zero in the annulus `a ≤ |z| ≤ b` lies in a model
  disk attached to a crossing radius in `[a/2, 2b]`, and
* `model_disk_zero_count_one_p32` — each such model disk contains exactly one zero of
  `F_{3/2}^{(n)}`, and that zero is simple,

gives Theorem 1.3 of the manuscript in the annular form: for every fixed annulus away
from the origin, all zeros of all sufficiently high derivatives are simple.

The restriction to an annulus is essential: `z = 0` is a zero of large multiplicity of
`F_{3/2}^{(n)}` for many `n`, so no global simplicity statement can hold.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- **Eventual simplicity of all zeros in a fixed annulus** (`p = 3/2`). -/
theorem annular_zeros_simple_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b →
      iteratedDeriv n (F (3/2)) z = 0 → iteratedDeriv (n + 1) (F (3/2)) z ≠ 0 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨c, hc, -, N₁, hN₁⟩ :=
    model_disk_zero_count_one_p32 (a := a/2) (b := 2*b) (by linarith) (by linarith)
  obtain ⟨N₂, hN₂⟩ := annular_zero_exclusion_p32 ha hab hc
  refine ⟨max N₁ N₂, fun n hn z hza hzb hz0 => ?_⟩
  obtain ⟨j, l, hj1, hjn, hρa, hρb, -, hmem⟩ :=
    hN₂ n (le_trans (le_max_right _ _) hn) z hza hzb hz0
  have hsimple :=
    (hN₁ n (le_trans (le_max_left _ _) hn) j hj1 hjn hρa hρb l).2 z hmem hz0
  rw [iteratedDeriv_succ]
  exact hsimple

/-- The same statement in the `deriv` formulation. -/
theorem annular_zeros_simple_deriv_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b →
      iteratedDeriv n (F (3/2)) z = 0 → deriv (iteratedDeriv n (F (3/2))) z ≠ 0 := by
  obtain ⟨N, hN⟩ := annular_zeros_simple_p32 ha hab
  refine ⟨N, fun n hn z hza hzb hz0 => ?_⟩
  have := hN n hn z hza hzb hz0
  rwa [iteratedDeriv_succ] at this

end SparseFock
