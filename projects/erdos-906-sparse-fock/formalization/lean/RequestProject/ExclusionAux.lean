import RequestProject.ModelDisk
import RequestProject.Spacing
import RequestProject.TailGeneral
import RequestProject.RootLoc

/-!
# Auxiliary facts for the exclusion of additional zeros

Four elementary ingredients:

* the behaviour of the discrete slope `dstep` under a change of radius;
* the description of the active support inside a block of three consecutive support
  points;
* the support gap outside such a block;
* the estimate of `F_p^{(n)}` by a single principal term.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- Changing the radius shifts every discrete slope by `log` of the ratio. -/
theorem dstep_exp_shift (n m : ℕ) {ρ σ : ℝ} (hρ : 0 < ρ) :
    dstep n (ρ * Real.exp σ) m = dstep n ρ m + σ := by
  rw [dstep_eq, dstep_eq, Real.log_mul (ne_of_gt hρ) (ne_of_gt (Real.exp_pos σ)),
    Real.log_exp]
  ring

variable {n j : ℕ}

/-- Inside the block spanned by three consecutive support points, the only active
exponents are the three support points themselves. -/
theorem dcoeff_zero_in_block3 (hj : 1 ≤ j) (hn : n ≤ nu (3/2) j) {m : ℕ}
    (h1 : mOf (3/2) n j ≤ m)
    (h2 : m ≤ mOf (3/2) n j + qgap (3/2) j + qgap (3/2) (j + 1))
    (hne0 : m ≠ mOf (3/2) n j)
    (hne1 : m ≠ mOf (3/2) n j + qgap (3/2) j)
    (hne2 : m ≠ mOf (3/2) n j + qgap (3/2) j + qgap (3/2) (j + 1)) :
    dcoeff (3/2) n m = 0 := by
  by_contra hz
  have hsupp : IsSupp (3/2) (m + n) := by
    by_contra h
    exact hz (by rw [dcoeff, if_neg h])
  obtain ⟨s, hs1, hs2⟩ := hsupp
  have hnuj : nu (3/2) j = n + mOf (3/2) n j := nu_eq_add_mOf hn
  have hg0 : nu (3/2) j + qgap (3/2) j = nu (3/2) (j + 1) :=
    nu_add_qgap (by norm_num) hj
  have hg1 : nu (3/2) (j + 1) + qgap (3/2) (j + 1) = nu (3/2) (j + 2) := by
    have h := nu_add_qgap (p := (3/2 : ℝ)) (by norm_num) (show 1 ≤ j + 1 by omega)
    rwa [show j + 1 + 1 = j + 2 by omega] at h
  have hsj : j ≤ s := by
    by_contra hcon
    push_neg at hcon
    have : nu (3/2) s < nu (3/2) j := nu_lt_nu (by norm_num) hs1 hcon
    omega
  have hsj2 : s ≤ j + 2 := by
    by_contra hcon
    push_neg at hcon
    have : nu (3/2) (j + 2) < nu (3/2) s := nu_lt_nu (by norm_num) (by omega) hcon
    omega
  have hcases : s = j ∨ s = j + 1 ∨ s = j + 2 := by omega
  rcases hcases with h | h | h <;> subst h <;> omega

/-- Outside the block spanned by three consecutive support points, every active exponent
is at distance at least `min (q_{j-1}) (q_{j+2})` from the block. -/
theorem supp_gap3 (hj : 2 ≤ j) (hn : n ≤ nu (3/2) j) {m : ℕ}
    (hm : dcoeff (3/2) n m ≠ 0) :
    (m < mOf (3/2) n j →
        m + min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 2)) ≤ mOf (3/2) n j) ∧
      (mOf (3/2) n j + qgap (3/2) j + qgap (3/2) (j + 1) < m →
        mOf (3/2) n j + qgap (3/2) j + qgap (3/2) (j + 1)
          + min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 2)) ≤ m) := by
  have hj1 : 1 ≤ j := by omega
  have hsupp : IsSupp (3/2) (m + n) := by
    by_contra h
    exact hm (by rw [dcoeff, if_neg h])
  obtain ⟨s, hs1, hs2⟩ := hsupp
  have hnuj : nu (3/2) j = n + mOf (3/2) n j := nu_eq_add_mOf hn
  have hg0 : nu (3/2) j + qgap (3/2) j = nu (3/2) (j + 1) := nu_add_qgap (by norm_num) hj1
  have hg1 : nu (3/2) (j + 1) + qgap (3/2) (j + 1) = nu (3/2) (j + 2) := by
    have h := nu_add_qgap (p := (3/2 : ℝ)) (by norm_num) (show 1 ≤ j + 1 by omega)
    rwa [show j + 1 + 1 = j + 2 by omega] at h
  have hgm : nu (3/2) (j - 1) + qgap (3/2) (j - 1) = nu (3/2) j := by
    have h := nu_add_qgap (p := (3/2 : ℝ)) (by norm_num) (show 1 ≤ j - 1 by omega)
    rwa [show j - 1 + 1 = j by omega] at h
  have hg2 : nu (3/2) (j + 2) + qgap (3/2) (j + 2) = nu (3/2) (j + 3) := by
    have h := nu_add_qgap (p := (3/2 : ℝ)) (by norm_num) (show 1 ≤ j + 2 by omega)
    rwa [show j + 2 + 1 = j + 3 by omega] at h
  have hmin1 : min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 2)) ≤ qgap (3/2) (j - 1) :=
    min_le_left _ _
  have hmin2 : min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 2)) ≤ qgap (3/2) (j + 2) :=
    min_le_right _ _
  constructor
  · intro hlt
    have hsle : s ≤ j - 1 := by
      by_contra hcon
      push_neg at hcon
      have : nu (3/2) j ≤ nu (3/2) s := nu32_mono hj1 (by omega)
      omega
    have : nu (3/2) s ≤ nu (3/2) (j - 1) := nu32_mono hs1 hsle
    omega
  · intro hgt
    have hsge : j + 3 ≤ s := by
      by_contra hcon
      push_neg at hcon
      have : nu (3/2) s ≤ nu (3/2) (j + 2) := nu32_mono hs1 (by omega)
      omega
    have : nu (3/2) (j + 3) ≤ nu (3/2) s := nu32_mono (by omega) hsge
    omega

/-- The derivative differs from a single one of its terms by at most the sum of all the
others. -/
theorem norm_sub_one_term_le (p : ℝ) (n m₁ : ℕ) (z : ℂ) :
    ‖iteratedDeriv n (F p) z - ((dcoeff p n m₁ : ℝ) : ℂ) * z ^ m₁‖
      ≤ ∑' m : ℕ, (if m = m₁ then 0 else dcoeff p n m * ‖z‖ ^ m) := by
  classical
  set a : ℕ → ℂ := fun m => ((dcoeff p n m : ℝ) : ℂ) * z ^ m with ha
  have hsum : Summable a := summable_dcoeff_mul_pow_complex p n z
  have hs1 : Summable fun m : ℕ => (if m = m₁ then a m₁ else 0) :=
    summable_of_ne_finset_zero (s := {m₁}) (fun m hm => if_neg (by simpa using hm))
  have hnormb : ∀ m : ℕ,
      ‖(if m = m₁ then 0 else a m)‖ = (if m = m₁ then 0 else dcoeff p n m * ‖z‖ ^ m) := by
    intro m
    by_cases hm : m = m₁
    · rw [if_pos hm, if_pos hm, norm_zero]
    · rw [if_neg hm, if_neg hm, ha]
      dsimp only
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (dcoeff_nonneg p n m)]
  have htarget : Summable fun m : ℕ => (if m = m₁ then 0 else dcoeff p n m * ‖z‖ ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      (summable_dcoeff_mul_pow p n (norm_nonneg z))
    · split
      · exact le_rfl
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
    · split
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
      · exact le_rfl
  have hnsum : Summable fun m : ℕ => ‖(if m = m₁ then 0 else a m)‖ :=
    htarget.congr (fun m => (hnormb m).symm)
  have hbeq : ∀ m : ℕ, (if m = m₁ then 0 else a m) = a m - (if m = m₁ then a m₁ else 0) := by
    intro m
    by_cases h1 : m = m₁
    · subst h1; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg h1, if_neg h1]; ring
  have htsum : ∑' m, (if m = m₁ then 0 else a m) = (∑' m, a m) - a m₁ := by
    have he1 : ∑' m : ℕ, (if m = m₁ then a m₁ else 0) = a m₁ := by
      rw [tsum_eq_single m₁ (fun b hb => if_neg hb), if_pos rfl]
    rw [tsum_congr hbeq, hsum.tsum_sub hs1, he1]
  have hval : iteratedDeriv n (F p) z - a m₁ = ∑' m, (if m = m₁ then 0 else a m) := by
    rw [htsum, iteratedDeriv_F_eq_dcoeff]
  rw [hval]
  exact le_trans (norm_tsum_le_tsum_norm hnsum) (le_of_eq (tsum_congr hnormb))

end SparseFock
