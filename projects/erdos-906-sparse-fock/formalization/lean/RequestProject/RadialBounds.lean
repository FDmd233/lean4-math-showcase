import RequestProject.Aux32

/-!
# Consequences of the position of a crossing radius

Quantitative consequences of `ρ_j ≤ b` and `a ≤ ρ_{j+1}` for the exponent `m_j`, and
the bound on the spacing of consecutive crossing radii.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- If the crossing radius `ρ_j` is at most `b`, then `m_j + 1 ≤ b² + b √n`. -/
theorem mOf_add_one_le_of_rho_le {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j)
    {b : ℝ} (hb0 : 0 < b) (hb : rho (3/2) n j ≤ b) :
    ((mOf (3/2) n j : ℕ) : ℝ) + 1 ≤ b ^ 2 + b * Real.sqrt n := by
  have h := sq_le_of_rho_le (p := (3/2 : ℝ)) (by norm_num) hj hn hb
  have hs : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs0 : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hm0 : (0:ℝ) ≤ ((mOf (3/2) n j : ℕ) : ℝ) := Nat.cast_nonneg _
  by_contra hcon
  push_neg at hcon
  have hkey : 0 < (((mOf (3/2) n j : ℕ) : ℝ) + 1 - (b ^ 2 + b * Real.sqrt n)) *
      (((mOf (3/2) n j : ℕ) : ℝ) + 1 + b * Real.sqrt n) := by
    refine mul_pos (by linarith) ?_
    have : (0:ℝ) ≤ b * Real.sqrt n := mul_nonneg hb0.le hs0
    linarith
  have hb3 : (0:ℝ) ≤ b ^ 3 * Real.sqrt n := by positivity
  nlinarith [h, hkey, hs, hb3]

/-- If `a ≤ ρ_{j+1}`, then `a √n ≤ m_{j+1} + q_{j+1}`. -/
theorem le_mOf_add_qgap {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j)
    {a : ℝ} (ha : 0 < a) (ha' : a ≤ rho (3/2) n (j + 1)) :
    a * Real.sqrt n ≤ ((mOf (3/2) n (j + 1) : ℕ) : ℝ) + ((qgap (3/2) (j + 1) : ℕ) : ℝ) := by
  have hj1 : 1 ≤ j + 1 := by omega
  have hn1 : n ≤ nu (3/2) (j + 1) := le_trans hn (nu_lt_nu_succ (by norm_num) hj).le
  obtain ⟨-, hup⟩ := rho_squeeze (p := (3/2 : ℝ)) (by norm_num) hj1 hn1
  set M : ℝ := ((mOf (3/2) n (j + 1) : ℕ) : ℝ) + ((qgap (3/2) (j + 1) : ℕ) : ℝ) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    positivity
  have hD : (0:ℝ) < Real.sqrt ((n : ℝ) + ((mOf (3/2) n (j + 1) : ℕ) : ℝ)
      + ((qgap (3/2) (j + 1) : ℕ) : ℝ)) := by
    refine Real.sqrt_pos.2 ?_
    have h1 : 1 ≤ qgap (3/2) (j + 1) := one_le_qgap (by norm_num) hj1
    have : (1:ℝ) ≤ ((qgap (3/2) (j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ ((mOf (3/2) n (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hsq : Real.sqrt n ≤ Real.sqrt ((n : ℝ) + ((mOf (3/2) n (j + 1) : ℕ) : ℝ)
      + ((qgap (3/2) (j + 1) : ℕ) : ℝ)) := by
    refine Real.sqrt_le_sqrt ?_
    have h3 : (0:ℝ) ≤ ((mOf (3/2) n (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : (0:ℝ) ≤ ((qgap (3/2) (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hstep : a ≤ M / Real.sqrt ((n : ℝ) + ((mOf (3/2) n (j + 1) : ℕ) : ℝ)
      + ((qgap (3/2) (j + 1) : ℕ) : ℝ)) := le_trans ha' hup
  rw [le_div_iff₀ hD] at hstep
  nlinarith [hstep, hsq, ha.le, Real.sqrt_nonneg (n : ℝ)]

/-- Consecutive crossing radii are close: `ρ_{j+1} - ρ_j ≤ ρ_j (q_j + q_{j+1})/(m_j+1)`. -/
theorem rho_succ_sub_rho_le {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j) :
    rho (3/2) n (j + 1) - rho (3/2) n j
      ≤ rho (3/2) n j * ((((qgap (3/2) j : ℕ) : ℝ) + ((qgap (3/2) (j + 1) : ℕ) : ℝ))
          / (((mOf (3/2) n j : ℕ) : ℝ) + 1)) := by
  have hj1 : 1 ≤ j + 1 := by omega
  have hn1 : n ≤ nu (3/2) (j + 1) := le_trans hn (nu_lt_nu_succ (by norm_num) hj).le
  have hqa : 1 ≤ qgap (3/2) j := one_le_qgap (by norm_num) hj
  have hqb : 1 ≤ qgap (3/2) (j + 1) := one_le_qgap (by norm_num) hj1
  have hmsucc : mOf (3/2) n (j + 1) = mOf (3/2) n j + qgap (3/2) j :=
    mOf_succ (by norm_num) hj hn
  obtain ⟨hlow, -⟩ := rho_squeeze (p := (3/2 : ℝ)) (by norm_num) hj hn
  obtain ⟨-, hup⟩ := rho_squeeze (p := (3/2 : ℝ)) (by norm_num) hj1 hn1
  rw [hmsucc] at hup
  push_cast at hup
  set m : ℝ := ((mOf (3/2) n j : ℕ) : ℝ) with hm
  set qa : ℝ := ((qgap (3/2) j : ℕ) : ℝ) with hqa'
  set qb : ℝ := ((qgap (3/2) (j + 1) : ℕ) : ℝ) with hqb'
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hqa1 : (1:ℝ) ≤ qa := by rw [hqa']; exact_mod_cast hqa
  have hqb1 : (1:ℝ) ≤ qb := by rw [hqb']; exact_mod_cast hqb
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hD1 : (0:ℝ) < Real.sqrt ((n : ℝ) + m + 1) := Real.sqrt_pos.2 (by linarith)
  have hD2 : (0:ℝ) < Real.sqrt ((n : ℝ) + (m + qa) + qb) := Real.sqrt_pos.2 (by linarith)
  have hDle : Real.sqrt ((n : ℝ) + m + 1) ≤ Real.sqrt ((n : ℝ) + (m + qa) + qb) :=
    Real.sqrt_le_sqrt (by linarith)
  -- push the upper bound for `ρ_{j+1}` through the smaller denominator
  have hnum : (0:ℝ) ≤ m + qa + qb := by linarith
  have hup' : rho (3/2) n (j + 1) ≤ (m + 1 + (qa + qb)) / Real.sqrt ((n : ℝ) + m + 1) := by
    refine le_trans hup (le_trans (div_le_div_of_nonneg_left hnum hD1 hDle) ?_)
    exact (div_le_div_iff_of_pos_right hD1).mpr (by linarith)
  have hlow' : (m + 1) / Real.sqrt ((n : ℝ) + m + 1) ≤ rho (3/2) n j := hlow
  have hkey : rho (3/2) n (j + 1) ≤ rho (3/2) n j * ((m + 1 + (qa + qb)) / (m + 1)) := by
    have hratio : (0:ℝ) ≤ (m + 1 + (qa + qb)) / (m + 1) := by positivity
    have hstep : (m + 1) / Real.sqrt ((n : ℝ) + m + 1) * ((m + 1 + (qa + qb)) / (m + 1))
        = (m + 1 + (qa + qb)) / Real.sqrt ((n : ℝ) + m + 1) := by
      field_simp
    calc rho (3/2) n (j + 1)
        ≤ (m + 1 + (qa + qb)) / Real.sqrt ((n : ℝ) + m + 1) := hup'
      _ = (m + 1) / Real.sqrt ((n : ℝ) + m + 1) * ((m + 1 + (qa + qb)) / (m + 1)) := hstep.symm
      _ ≤ rho (3/2) n j * ((m + 1 + (qa + qb)) / (m + 1)) :=
          mul_le_mul_of_nonneg_right hlow' hratio
  have hexpand : rho (3/2) n j * ((m + 1 + (qa + qb)) / (m + 1))
      = rho (3/2) n j + rho (3/2) n j * ((qa + qb) / (m + 1)) := by
    field_simp
  rw [hexpand] at hkey
  linarith

end SparseFock
