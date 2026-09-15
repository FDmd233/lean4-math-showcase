import Mathlib

/-!
# Discrete curvature of the logarithmic weights

This module records Lemma 2.3 (discrete curvature) and the elementary factorial
bounds (2.7) of the paper *Zeros of high derivatives of sparse Fock series*.

For `n : ℕ`, `r : ℝ` and `m : ℕ` (so `m = k - n` in the notation of the paper),
`Phi n r m = ½ log ((n+m)!) - log (m!) + m log r`
is the logarithm of the modulus of the `m`-th term of the `n`-th derivative at radius `r`,
and `dstep n r m` is its forward difference.
-/

namespace SparseFock

open scoped Nat

/-- `Φ_{n,r}(k)` of the paper, written in terms of `m = k - n`. -/
noncomputable def Phi (n : ℕ) (r : ℝ) (m : ℕ) : ℝ :=
  (1 / 2) * Real.log ((n + m)! ) - Real.log (m !) + m * Real.log r

/-- The forward difference `d_{n,r}(k)` of the paper. -/
noncomputable def dstep (n : ℕ) (r : ℝ) (m : ℕ) : ℝ := Phi n r (m + 1) - Phi n r m

variable {n m : ℕ} {r : ℝ}

/-- Formula (2.8): the forward difference in closed form. -/
theorem dstep_eq (n : ℕ) (r : ℝ) (m : ℕ) :
    dstep n r m = Real.log r + (1 / 2) * Real.log ((n : ℝ) + m + 1) - Real.log ((m : ℝ) + 1) := by
  have hfac1 : ((n + (m + 1))! : ℝ) = ((n : ℝ) + m + 1) * ((n + m)! : ℝ) := by
    have h : n + (m + 1) = (n + m) + 1 := by omega
    rw [h, Nat.factorial_succ]
    push_cast
    ring
  have hfac2 : (((m + 1))! : ℝ) = ((m : ℝ) + 1) * ((m)! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hpos1 : (0:ℝ) < ((n + m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpos2 : (0:ℝ) < ((m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hn1 : (0:ℝ) < (n : ℝ) + m + 1 := by positivity
  have hm1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  simp only [dstep, Phi, hfac1, hfac2, Real.log_mul (ne_of_gt hn1) (ne_of_gt hpos1),
    Real.log_mul (ne_of_gt hm1) (ne_of_gt hpos2)]
  push_cast
  ring

/-- Formula (2.9): the discrete second difference in closed form. -/
theorem dstep_sub_dstep_succ (n : ℕ) (r : ℝ) (m : ℕ) :
    dstep n r m - dstep n r (m + 1)
      = Real.log (1 + 1 / ((m : ℝ) + 1)) - (1 / 2) * Real.log (1 + 1 / ((n : ℝ) + m + 1)) := by
  have hm1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0:ℝ) < (m : ℝ) + 1 + 1 := by positivity
  have hn1 : (0:ℝ) < (n : ℝ) + m + 1 := by positivity
  have hn2 : (0:ℝ) < (n : ℝ) + m + 1 + 1 := by positivity
  have e1 : (1:ℝ) + 1 / ((m : ℝ) + 1) = ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1) := by
    field_simp
  have e2 : (1:ℝ) + 1 / ((n : ℝ) + m + 1) = ((n : ℝ) + m + 1 + 1) / ((n : ℝ) + m + 1) := by
    field_simp
  rw [dstep_eq, dstep_eq, e1, e2, Real.log_div (ne_of_gt hm2) (ne_of_gt hm1),
    Real.log_div (ne_of_gt hn2) (ne_of_gt hn1)]
  push_cast
  ring_nf

/-- Strict discrete concavity: the forward differences strictly decrease. -/
theorem dstep_sub_dstep_succ_pos (n : ℕ) (r : ℝ) (m : ℕ) :
    0 < dstep n r m - dstep n r (m + 1) := by
  have hm1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hn1 : (0:ℝ) < (n : ℝ) + m + 1 := by positivity
  have hle : 1 / ((n : ℝ) + m + 1) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hm1
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlog_le : Real.log (1 + 1 / ((n : ℝ) + m + 1)) ≤ Real.log (1 + 1 / ((m : ℝ) + 1)) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hlog_pos : 0 < Real.log (1 + 1 / ((n : ℝ) + m + 1)) := by
    apply Real.log_pos
    have : 0 < 1 / ((n : ℝ) + m + 1) := by positivity
    linarith
  rw [dstep_sub_dstep_succ]
  linarith

/-- The elementary lower bound for the discrete curvature. -/
theorem dstep_curvature_lower (n : ℕ) (r : ℝ) (m : ℕ) :
    1 / ((m : ℝ) + 2) - 1 / (2 * ((n : ℝ) + m + 1)) ≤ dstep n r m - dstep n r (m + 1) := by
  have hm1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hn1 : (0:ℝ) < (n : ℝ) + m + 1 := by positivity
  -- lower bound `log (1+x) ≥ x/(1+x)`
  have hlow : 1 / ((m : ℝ) + 2) ≤ Real.log (1 + 1 / ((m : ℝ) + 1)) := by
    have hx : (0:ℝ) < 1 + 1 / ((m : ℝ) + 1) := by positivity
    have h := Real.log_le_sub_one_of_pos (x := 1 / (1 + 1 / ((m : ℝ) + 1))) (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one] at h
    have hval : 1 / (1 + 1 / ((m : ℝ) + 1)) = ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
      field_simp
      ring
    rw [hval] at h
    have heq : ((m : ℝ) + 1) / ((m : ℝ) + 2) - 1 = -(1 / ((m : ℝ) + 2)) := by
      field_simp
      ring
    rw [heq] at h
    linarith
  -- upper bound `log (1+y) ≤ y`
  have hup : Real.log (1 + 1 / ((n : ℝ) + m + 1)) ≤ 1 / ((n : ℝ) + m + 1) := by
    have h := Real.log_le_sub_one_of_pos (x := 1 + 1 / ((n : ℝ) + m + 1)) (by positivity)
    linarith
  have h2 : (1 / 2) * Real.log (1 + 1 / ((n : ℝ) + m + 1)) ≤ 1 / (2 * ((n : ℝ) + m + 1)) := by
    have hrw : 1 / (2 * ((n : ℝ) + m + 1)) = (1/2) * (1 / ((n : ℝ) + m + 1)) := by
      rw [one_div_mul_one_div]
    rw [hrw]
    linarith
  rw [dstep_sub_dstep_succ]
  linarith

/-- Uniform curvature lower bound on the saddle range `0 ≤ m ≤ B √n`:
for every `B > 0` and all large `n`, the discrete curvature is at least
`1 / (4 (B+1) √n)`. -/
theorem dstep_curvature_lower_sqrt {B : ℝ} (hB : 0 < B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (r : ℝ) (m : ℕ), (m : ℝ) ≤ B * Real.sqrt n →
      1 / (4 * (B + 1) * Real.sqrt n) ≤ dstep n r m - dstep n r (m + 1) := by
  refine ⟨4 * ⌈(B + 1) ^ 2⌉₊ + 4, ?_⟩
  intro n hn r m hm
  have hB1 : (1:ℝ) < B + 1 := by linarith
  have hNle : (4 : ℝ) * (B + 1) ^ 2 ≤ (n : ℝ) := by
    have h1 : ((B + 1) ^ 2 : ℝ) ≤ (⌈(B + 1) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((4 * ⌈(B + 1) ^ 2⌉₊ + 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at h2
    linarith
  set t : ℝ := Real.sqrt n with ht_def
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have ht : 2 * (B + 1) ≤ t := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)), Real.sqrt_nonneg (n : ℝ)]
  have ht2 : (2:ℝ) ≤ t := by nlinarith
  have htpos : 0 < t := by linarith
  have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- bound the two terms of `dstep_curvature_lower`
  have h1 : 1 / ((B + 1) * t) ≤ 1 / ((m : ℝ) + 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h2 : 1 / (2 * ((n : ℝ) + m + 1)) ≤ 1 / (4 * (B + 1) * t) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h3 : 1 / (4 * (B + 1) * t) ≤ 1 / ((B + 1) * t) - 1 / (4 * (B + 1) * t) := by
    have hexp : 1 / ((B + 1) * t) = 4 * (1 / (4 * (B + 1) * t)) := by
      field_simp
    have hpos : 0 < 1 / (4 * (B + 1) * t) := by positivity
    rw [hexp]
    linarith
  have := dstep_curvature_lower n r m
  linarith

/-- Formula (2.7), lower half: `k log k - k + 1 ≤ log (k!)`. -/
theorem log_factorial_lower (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * Real.log k - k + 1 ≤ Real.log (k !) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      norm_num
    · have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have ihk := ih hk0
      have hfac : (((k + 1))! : ℝ) = ((k : ℝ) + 1) * ((k)! : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hposk : (0:ℝ) < ((k)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hlog : Real.log ((((k + 1))! : ℕ) : ℝ) = Real.log ((k : ℝ) + 1) + Real.log ((k)! : ℝ) := by
        rw [show ((((k+1))! : ℕ) : ℝ) = ((k : ℝ) + 1) * ((k)! : ℝ) from hfac,
          Real.log_mul (by positivity) (ne_of_gt hposk)]
      -- key: `k log (1 + 1/k) ≤ 1`
      have hkey : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (x := ((k : ℝ) + 1) / (k : ℝ)) (by positivity)
        rw [Real.log_div (by positivity) (ne_of_gt hkpos)] at h
        have hh : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by field_simp; ring
        rw [hh] at h
        have : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ (k : ℝ) * (1 / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left h (le_of_lt hkpos)
        rwa [mul_one_div, div_self (ne_of_gt hkpos)] at this
      push_cast [hlog]
      push_cast at ihk
      nlinarith

/-- Formula (2.7), upper half: `log (k!) ≤ k log k - k + 1 + log k`. -/
theorem log_factorial_upper (k : ℕ) (hk : 1 ≤ k) :
    Real.log (k !) ≤ (k : ℝ) * Real.log k - k + 1 + Real.log k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      norm_num
    · have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have ihk := ih hk0
      have hposk : (0:ℝ) < ((k)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hfac : (((k + 1))! : ℝ) = ((k : ℝ) + 1) * ((k)! : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hlog : Real.log ((((k + 1))! : ℕ) : ℝ) = Real.log ((k : ℝ) + 1) + Real.log ((k)! : ℝ) := by
        rw [show ((((k+1))! : ℕ) : ℝ) = ((k : ℝ) + 1) * ((k)! : ℝ) from hfac,
          Real.log_mul (by positivity) (ne_of_gt hposk)]
      -- key: `(k+1) log (1 + 1/k) ≥ 1`
      have hkey : 1 ≤ ((k : ℝ) + 1) * (Real.log ((k : ℝ) + 1) - Real.log k) := by
        have h := Real.log_le_sub_one_of_pos (x := (k : ℝ) / ((k : ℝ) + 1)) (by positivity)
        rw [Real.log_div (ne_of_gt hkpos) (by positivity)] at h
        have hh : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by field_simp; ring
        rw [hh] at h
        have h' : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by linarith
        have := mul_le_mul_of_nonneg_left h' (by positivity : (0:ℝ) ≤ (k : ℝ) + 1)
        rwa [mul_one_div, div_self (by positivity : ((k : ℝ) + 1) ≠ 0)] at this
      push_cast [hlog]
      push_cast at ihk
      nlinarith

end SparseFock
