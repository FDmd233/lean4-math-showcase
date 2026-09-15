import RequestProject.Crossing

/-!
# The lower bound for the radial spacing of the crossing circles

This file proves the missing half of equation (2.16) of the manuscript,

`log ρ_{j+1} - log ρ_j ≥ κ (q_j + q_{j+1}) / 2`,

where `κ` is any lower bound for the increments of the weight function
`f_n(t) = log(t+1) - ½ log(n+t+1)` on the two consecutive blocks.  The proof is the one
of the manuscript: `log ρ_j` is the average of `f_n` over the block `[m_j, m_j+q_j)` and
`log ρ_{j+1}` the average over `[m_{j+1}, m_{j+1}+q_{j+1})`, and the mean index jumps by
`(q_j + q_{j+1})/2`.

The `p = 3/2` corollary makes `κ` explicit, exactly as `crossing_slopes32` does for the
block slopes.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- Telescoping lower bound for the increments of the weight function. -/
theorem fterm_sub_ge {n : ℕ} {κ : ℝ} {s : ℕ} :
    ∀ t : ℕ, s ≤ t → (∀ u : ℕ, s ≤ u → u < t → κ ≤ fterm n (u + 1) - fterm n u) →
      κ * ((t : ℝ) - (s : ℝ)) ≤ fterm n t - fterm n s := by
  intro t
  induction t with
  | zero =>
      intro hst _
      have : s = 0 := by omega
      subst this
      simp
  | succ t ih =>
      intro hst hκ
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · have hst' : s ≤ t := by omega
        have h1 : κ * ((t : ℝ) - (s : ℝ)) ≤ fterm n t - fterm n s :=
          ih hst' (fun u hu1 hu2 => hκ u hu1 (by omega))
        have h2 : κ ≤ fterm n (t + 1) - fterm n t := hκ t hst' (by omega)
        push_cast
        push_cast at h1
        linarith
      · have : s = t + 1 := by omega
        subst this
        simp

/-- **Radial spacing, lower bound.**  If every increment of `f_n` over the two consecutive
blocks starting at `m_j` is at least `κ`, then the logarithmic spacing of the crossing
radii is at least `κ (q_j + q_{j+1}) / 2`. -/
theorem log_rho_spacing_lower {p : ℝ} {n j : ℕ} (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j)
    {κ : ℝ}
    (hκ : ∀ t : ℕ, mOf p n j ≤ t → t < mOf p n j + qgap p j + qgap p (j + 1) →
        κ ≤ fterm n (t + 1) - fterm n t) :
    κ * ((((qgap p j : ℕ)) : ℝ) + (((qgap p (j + 1) : ℕ)) : ℝ)) / 2
      ≤ Real.log (rho p n (j + 1)) - Real.log (rho p n j) := by
  set m : ℕ := mOf p n j with hmdef
  set q : ℕ := qgap p j with hqdef
  set q' : ℕ := qgap p (j + 1) with hq'def
  have hq1 : 1 ≤ q := one_le_qgap hp hj
  have hq'1 : 1 ≤ q' := one_le_qgap hp (by omega)
  have hqR : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq'R : (0:ℝ) < (q' : ℝ) := by exact_mod_cast hq'1
  have hn1 : n ≤ nu p (j + 1) := le_trans hn (nu_lt_nu_succ hp hj).le
  have hmsucc : mOf p n (j + 1) = m + q := mOf_succ hp hj hn
  -- the two averaging formulas
  have hA : Real.log (rho p n j)
      = 1 / (q : ℝ) * (∑ i ∈ Finset.range q, fterm n (m + i)) :=
    log_rho_eq_range hp hj hn
  have hB : Real.log (rho p n (j + 1))
      = 1 / (q' : ℝ) * (∑ i ∈ Finset.range q', fterm n (m + q + i)) := by
    have h := log_rho_eq_range hp (show 1 ≤ j + 1 by omega) hn1
    rw [hmsucc] at h
    exact h
  -- upper bound for the first average
  have hleft : ∀ i ∈ Finset.range q,
      fterm n (m + i) ≤ fterm n (m + q - 1) - κ * (((q : ℝ)) - 1 - (i : ℝ)) := by
    intro i hi
    have hi' : i < q := Finset.mem_range.1 hi
    have hst : m + i ≤ m + q - 1 := by omega
    have h := fterm_sub_ge (n := n) (κ := κ) (s := m + i) (m + q - 1) hst
      (fun u hu1 hu2 => hκ u (by omega) (by omega))
    have hcast : ((m + q - 1 : ℕ) : ℝ) - ((m + i : ℕ) : ℝ) = ((q : ℝ)) - 1 - (i : ℝ) := by
      have h1 : (m + q - 1 : ℕ) = m + (q - 1) := by omega
      have h2 : ((m + (q - 1) : ℕ) : ℝ) = (m : ℝ) + ((q : ℝ) - 1) := by
        push_cast [Nat.cast_sub hq1]
        ring
      rw [h1, h2]
      push_cast
      ring
    rw [hcast] at h
    linarith
  have hsumleft : (∑ i ∈ Finset.range q, fterm n (m + i))
      ≤ (q : ℝ) * fterm n (m + q - 1) - κ * ((q : ℝ) * ((q : ℝ) - 1) / 2) := by
    have h1 : (∑ i ∈ Finset.range q, fterm n (m + i))
        ≤ ∑ i ∈ Finset.range q, (fterm n (m + q - 1) - κ * (((q : ℝ)) - 1 - (i : ℝ))) :=
      Finset.sum_le_sum hleft
    have h2 : (∑ i ∈ Finset.range q, (fterm n (m + q - 1) - κ * (((q : ℝ)) - 1 - (i : ℝ))))
        = (q : ℝ) * fterm n (m + q - 1) - κ * ((q : ℝ) * ((q : ℝ) - 1) / 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
        sum_range_cast_rev]
      simp [nsmul_eq_mul]
    linarith
  -- lower bound for the second average
  have hright : ∀ i ∈ Finset.range q',
      fterm n (m + q) + κ * (i : ℝ) ≤ fterm n (m + q + i) := by
    intro i hi
    have hi' : i < q' := Finset.mem_range.1 hi
    have h := fterm_sub_ge (n := n) (κ := κ) (s := m + q) (m + q + i) (by omega)
      (fun u hu1 hu2 => hκ u (by omega) (by omega))
    have hcast : ((m + q + i : ℕ) : ℝ) - ((m + q : ℕ) : ℝ) = (i : ℝ) := by
      push_cast; ring
    rw [hcast] at h
    linarith
  have hsumright : (q' : ℝ) * fterm n (m + q) + κ * ((q' : ℝ) * ((q' : ℝ) - 1) / 2)
      ≤ (∑ i ∈ Finset.range q', fterm n (m + q + i)) := by
    have h1 : (∑ i ∈ Finset.range q', (fterm n (m + q) + κ * (i : ℝ)))
        ≤ ∑ i ∈ Finset.range q', fterm n (m + q + i) := Finset.sum_le_sum hright
    have h2 : (∑ i ∈ Finset.range q', (fterm n (m + q) + κ * (i : ℝ)))
        = (q' : ℝ) * fterm n (m + q) + κ * ((q' : ℝ) * ((q' : ℝ) - 1) / 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
        sum_range_cast]
      simp [nsmul_eq_mul]
    linarith
  -- the single step between the blocks
  have hstep : κ ≤ fterm n (m + q) - fterm n (m + q - 1) := by
    have hrw : m + q = (m + q - 1) + 1 := by omega
    rw [hrw]
    exact hκ (m + q - 1) (by omega) (by omega)
  -- assemble
  have hAle : Real.log (rho p n j) ≤ fterm n (m + q - 1) - κ * (((q : ℝ)) - 1) / 2 := by
    rw [hA, show (1:ℝ) / (q : ℝ) * (∑ i ∈ Finset.range q, fterm n (m + i))
        = (∑ i ∈ Finset.range q, fterm n (m + i)) / (q : ℝ) by ring, div_le_iff₀ hqR]
    have heq : ((fterm n (m + q - 1) - κ * (((q : ℝ)) - 1) / 2)) * (q : ℝ)
        = (q : ℝ) * fterm n (m + q - 1) - κ * ((q : ℝ) * ((q : ℝ) - 1) / 2) := by ring
    rw [heq]
    exact hsumleft
  have hBge : fterm n (m + q) + κ * (((q' : ℝ)) - 1) / 2 ≤ Real.log (rho p n (j + 1)) := by
    rw [hB, show (1:ℝ) / (q' : ℝ) * (∑ i ∈ Finset.range q', fterm n (m + q + i))
        = (∑ i ∈ Finset.range q', fterm n (m + q + i)) / (q' : ℝ) by ring, le_div_iff₀ hq'R]
    have heq : ((fterm n (m + q) + κ * (((q' : ℝ)) - 1) / 2)) * (q' : ℝ)
        = (q' : ℝ) * fterm n (m + q) + κ * ((q' : ℝ) * ((q' : ℝ) - 1) / 2) := by ring
    rw [heq]
    exact hsumright
  linarith

/-- **Radial spacing for `p = 3/2`, with an explicit curvature constant.** -/
theorem rho_log_spacing32 {n j : ℕ} (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j)
    (hsmall : mOf (3/2) n j + qgap (3/2) j + qgap (3/2) (j + 1) + 2 ≤ n) :
    (1 / (2 * ((((mOf (3/2) n j : ℕ)) : ℝ) + (((qgap (3/2) j : ℕ)) : ℝ)
        + (((qgap (3/2) (j + 1) : ℕ)) : ℝ) + 2)))
        * ((((qgap (3/2) j : ℕ)) : ℝ) + (((qgap (3/2) (j + 1) : ℕ)) : ℝ)) / 2
      ≤ Real.log (rho (3/2) n (j + 1)) - Real.log (rho (3/2) n j) := by
  set m : ℕ := mOf (3/2) n j with hmdef
  set q : ℕ := qgap (3/2) j with hqdef
  set q' : ℕ := qgap (3/2) (j + 1) with hq'def
  set M : ℝ := (m : ℝ) + (q : ℝ) + (q' : ℝ) + 2 with hMdef
  have hMpos : 0 < M := by
    have h1 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ (q' : ℝ) := Nat.cast_nonneg _
    rw [hMdef]; linarith
  set κ : ℝ := 1 / (2 * M) with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  have hκ : ∀ t : ℕ, m ≤ t → t < m + q + q' → κ ≤ fterm n (t + 1) - fterm n t := by
    intro t ht1 ht2
    have hcurv := dstep_curvature_lower n 1 t
    have hfe : ∀ u : ℕ, fterm n u = -dstep n 1 u := fterm_eq_neg_dstep n
    have hdiff : fterm n (t + 1) - fterm n t = dstep n 1 t - dstep n 1 (t + 1) := by
      rw [hfe, hfe]; ring
    rw [hdiff]
    refine le_trans ?_ hcurv
    have htR : (t : ℝ) + 2 ≤ M := by
      have : (t : ℝ) ≤ (m : ℝ) + (q : ℝ) + (q' : ℝ) := by
        exact_mod_cast (by omega : t ≤ m + q + q')
      rw [hMdef]; linarith
    have hnR : M ≤ (n : ℝ) := by
      have : ((m + q + q' + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsmall
      push_cast at this
      rw [hMdef]; linarith
    have h1 : 1 / M ≤ 1 / ((t : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) htR
    have h2 : 1 / (2 * ((n : ℝ) + (t : ℝ) + 1)) ≤ 1 / (2 * M) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have ht0 : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
      linarith
    have hhalf : 1 / (2 * M) = (1 / M) / 2 := by field_simp
    rw [hκdef, hhalf]
    linarith
  have hmain := log_rho_spacing_lower (p := 3/2) (by norm_num) hj hn hκ
  rw [hκdef, hMdef] at hmain
  have hrw : 1 / (2 * ((m : ℝ) + (q : ℝ) + (q' : ℝ) + 2)) * ((q : ℝ) + (q' : ℝ)) / 2
      = 1 / (2 * ((m : ℝ) + (q : ℝ) + (q' : ℝ) + 2)) * (((q : ℝ)) + ((q' : ℝ))) / 2 := rfl
  linarith [hmain]

end SparseFock
