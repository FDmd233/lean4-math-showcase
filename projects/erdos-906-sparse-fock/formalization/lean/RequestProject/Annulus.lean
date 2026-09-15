import RequestProject.Exclusion

/-!
# Every annular zero lies in a model disk (`p = 3/2`)

The lemmas below assemble the two halves of the exclusion argument
(`transition_zero_p32` and `no_zero_dominant_p32`) into the statement of
Proposition 3.3 of the manuscript:

for a fixed annulus `a ≤ |z| ≤ b` with `0 < a ≤ b` and any fixed disk constant
`c > 0`, all sufficiently high derivatives `F_{3/2}^{(n)}` have **all** of their
zeros in the annulus inside the model-disk family.

Combining this with the one-zero-per-disk theorem `model_disk_zero_count_one_p32`
gives eventual simplicity of every annular zero.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- `e^{1/2} ≤ 2`. -/
theorem exp_half_le_two : Real.exp (1/2) ≤ 2 := by
  by_contra h
  push_neg at h
  have h2 : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1/2)]

set_option maxHeartbeats 1000000 in
/-- **Exclusion of additional zeros on a fixed annulus** (`p = 3/2`).

For `0 < a ≤ b` and any `c > 0` there is `N` such that for `n ≥ N` *every* zero `z`
of `iteratedDeriv n (F (3/2))` with `a ≤ ‖z‖ ≤ b` lies in one of the model disks
`modelDisk c n j l` attached to a crossing radius `ρ_{n,j} ∈ [a/2, 2b]`. -/
theorem annular_zero_exclusion_p32 {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b →
      iteratedDeriv n (F (3/2)) z = 0 →
      ∃ j l : ℕ, 1 ≤ j ∧ n ≤ nu (3/2) j ∧ a/2 ≤ rho (3/2) n j ∧
        rho (3/2) n j ≤ 2*b ∧ l < qgap (3/2) j ∧ z ∈ modelDisk c n j l := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set B : ℝ := max (2*b) 2 with hBdef
  have hB2 : (2:ℝ) ≤ B := le_max_right _ _
  have h2bB : 2*b ≤ B := le_max_left _ _
  have hBpos : (0:ℝ) < B := by linarith
  have hbB : b ≤ B := by linarith
  have hA : (0:ℝ) < a/2 := by linarith
  have hAB : a/2 ≤ B := by linarith
  set c₀ : ℝ := min (1/2) (1/(256*B^2)) with hc₀def
  have hc₀pos : 0 < c₀ := lt_min (by norm_num) (by positivity)
  have hc₀half : c₀ ≤ 1/2 := min_le_left _ _
  have hc₀B : c₀ ≤ 1/(256*B^2) := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := transition_zero_p32 hA hAB hc₀pos hc₀half hc₀B hc
  obtain ⟨N₂, hN₂⟩ := no_zero_dominant_p32 hA hAB hB2 hc₀pos hc₀half hc₀B
  obtain ⟨N₃, hN₃⟩ := exists_small_crossing ha
  refine ⟨max (max N₁ N₂) N₃, fun n hn z hza hzb hz0 => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ _)) hn
  have hn3 : N₃ ≤ n := le_trans (le_max_right _ _) hn
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le ha hza
  obtain ⟨j₀, hj₀1, hj₀n, hj₀r⟩ := hN₃ n hn3
  obtain ⟨j, hj1, hjn, hjle, hjgt⟩ :=
    exists_crossing_index (n := n) (r := ‖z‖) hzpos ⟨j₀, hj₀1, hj₀n, le_trans hj₀r hza⟩
  have hρpos : 0 < rho (3/2) n j := rho_pos _ _ _
  have hρ'pos : 0 < rho (3/2) n (j + 1) := rho_pos _ _ _
  have hq1 : 1 ≤ qgap (3/2) j := one_le_qgap (by norm_num) hj1
  have hq'1 : 1 ≤ qgap (3/2) (j + 1) := one_le_qgap (by norm_num) (by omega)
  have hqR : (1:ℝ) ≤ ((qgap (3/2) j : ℕ) : ℝ) := by exact_mod_cast hq1
  have hq'R : (1:ℝ) ≤ ((qgap (3/2) (j + 1) : ℕ) : ℝ) := by exact_mod_cast hq'1
  have hjn1 : n ≤ nu (3/2) (j + 1) := le_trans hjn (nu_lt_nu_succ (by norm_num) hj1).le
  have hAρ' : a/2 ≤ rho (3/2) n (j + 1) := by linarith
  have hρB : rho (3/2) n j ≤ B := le_trans hjle (le_trans hzb hbB)
  -- the two small-quotient bounds
  have hc₀q : c₀ / ((qgap (3/2) j : ℕ) : ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hc₀q' : c₀ / ((qgap (3/2) (j + 1) : ℕ) : ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set σ : ℝ := Real.log (‖z‖ / rho (3/2) n j) with hσdef
  set τ : ℝ := Real.log (rho (3/2) n (j + 1) / ‖z‖) with hτdef
  have hσnn : 0 ≤ σ := Real.log_nonneg (by rw [le_div_iff₀ hρpos]; linarith)
  have hτnn : 0 ≤ τ := Real.log_nonneg (by rw [le_div_iff₀ hzpos]; linarith)
  have hznorm : ‖z‖ = rho (3/2) n j * Real.exp σ := by
    rw [hσdef, Real.exp_log (by positivity)]; field_simp
  have hznorm' : rho (3/2) n (j + 1) = ‖z‖ * Real.exp τ := by
    rw [hτdef, Real.exp_log (by positivity)]; field_simp
  rcases le_or_gt σ (c₀ / ((qgap (3/2) j : ℕ) : ℝ)) with hcase1 | hcase1
  · -- the transition region around `ρ_j`
    obtain ⟨l, hl, hmem⟩ := hN₁ n hn1 j hj1 hjn hAρ' hρB z hzpos
      (by rw [abs_of_nonneg hσnn]; exact hcase1) hz0
    refine ⟨j, l, hj1, hjn, ?_, ?_, hl, hmem⟩
    · have hexp : Real.exp σ ≤ 2 :=
        le_trans (Real.exp_le_exp.2 (by linarith)) exp_half_le_two
      nlinarith [Real.exp_pos σ]
    · linarith
  rcases le_or_gt τ (c₀ / ((qgap (3/2) (j + 1) : ℕ) : ℝ)) with hcase2 | hcase2
  · -- the transition region around `ρ_{j+1}`
    have hrev : Real.log (‖z‖ / rho (3/2) n (j + 1)) = -τ := by
      rw [hτdef, ← Real.log_inv, inv_div]
    have hexp' : Real.exp τ ≤ 2 :=
      le_trans (Real.exp_le_exp.2 (by linarith)) exp_half_le_two
    have hρ'le : rho (3/2) n (j + 1) ≤ 2 * b := by
      rw [hznorm']; nlinarith [Real.exp_pos τ]
    obtain ⟨l, hl, hmem⟩ := hN₁ n hn1 (j + 1) (by omega) hjn1
      (by
        have := rho_lt_rho_succ (p := (3/2:ℝ)) (n := n) (j := j + 1) (by norm_num)
          (by omega) hjn1
        linarith)
      (le_trans hρ'le h2bB) z hzpos
      (by rw [hrev, abs_neg, abs_of_nonneg hτnn]; exact hcase2) hz0
    exact ⟨j + 1, l, by omega, hjn1, by linarith, hρ'le, hl, hmem⟩
  · -- one term dominates: there is no zero at all
    exact absurd hz0
      (hN₂ n hn2 j hj1 hjn hAρ' hρB z hjle hjgt hcase1 hcase2)

end SparseFock
