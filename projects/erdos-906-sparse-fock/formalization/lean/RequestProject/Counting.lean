import Mathlib

/-!
# The majorant `S_n(r)` used for the zero-count upper bound

The estimates (5.1) and (5.2) of the paper are formalised here
*Zeros of high derivatives of sparse Fock series*:
for `S_n(r) = ∑_{m ≥ 0} √((n+m)!)/m! · r^m` one has, for `0 < t < 1`,
`S_n(r) ≤ √(n!) (1-t)^{-(n+1)/2} exp(r²/(2t))`,
and, choosing `t = r/(r+√n)`,
`log S_n(r) ≤ ½ log (n!) + r √n + (r + r²)/2`.
-/

namespace SparseFock

open scoped Nat BigOperators

/-- The majorant `S_n(r) = ∑_{m≥0} √((n+m)!)/m! · r^m`. -/
noncomputable def Ssum (n : ℕ) (r : ℝ) : ℝ := ∑' m : ℕ, Real.sqrt ((n + m)! ) / (m !) * r ^ m

section

variable {r t : ℝ}

/-- The Cauchy–Schwarz splitting of the `m`-th term of `S_n(r)`. -/
theorem Ssum_term_eq (n m : ℕ) (hr : 0 ≤ r) (ht0 : 0 < t) :
    Real.sqrt ((n + m)! ) / (m !) * r ^ m
      = Real.sqrt (n !) *
        (Real.sqrt (((m + n).choose n : ℝ) * t ^ m) * Real.sqrt ((r ^ 2 / t) ^ m / (m !))) := by
  have hmfac : (0:ℝ) < ((m)! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hnfac : (0:ℝ) < ((n)! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnmfac : (0:ℝ) < (((n + m))! : ℝ) := by exact_mod_cast Nat.factorial_pos (n + m)
  have hchoose : (((m + n).choose n : ℕ) : ℝ) * (n ! : ℝ) * (m ! : ℝ) = (((m + n)! : ℕ) : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ m + n)
    have h2 : (m + n) - n = m := by omega
    rw [h2] at this
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  have hcomm : ((n + m)! : ℝ) = (((m + n)! : ℕ) : ℝ) := by
    rw [show n + m = m + n by omega]
  have hf : (0:ℝ) ≤ ((m + n).choose n : ℝ) * t ^ m := by positivity
  have hg : (0:ℝ) ≤ (r ^ 2 / t) ^ m / (m !) := by positivity
  have hL : (0:ℝ) ≤ Real.sqrt ((n + m)! ) / (m !) * r ^ m := by positivity
  have hprod : ((m + n).choose n : ℝ) * t ^ m * ((r ^ 2 / t) ^ m / (m !))
      = ((m + n).choose n : ℝ) * r ^ (2 * m) / (m !) := by
    rw [pow_mul]
    have : t ^ m * (r ^ 2 / t) ^ m = (r ^ 2) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc ((m + n).choose n : ℝ) * t ^ m * ((r ^ 2 / t) ^ m / (m !))
        = ((m + n).choose n : ℝ) * (t ^ m * (r ^ 2 / t) ^ m) / (m !) := by ring
      _ = ((m + n).choose n : ℝ) * (r ^ 2) ^ m / (m !) := by rw [this]
  have hsq : (Real.sqrt ((n + m)! ) / (m !) * r ^ m) ^ 2
      = (n ! : ℝ) * (((m + n).choose n : ℝ) * t ^ m * ((r ^ 2 / t) ^ m / (m !))) := by
    rw [hprod, mul_pow, div_pow, Real.sq_sqrt (le_of_lt hnmfac), ← pow_mul, hcomm, ← hchoose]
    field_simp
    ring
  have hcomb : Real.sqrt (n !) * Real.sqrt (((m + n).choose n : ℝ) * t ^ m
      * ((r ^ 2 / t) ^ m / (m !)))
      = Real.sqrt ((n ! : ℝ) * (((m + n).choose n : ℝ) * t ^ m * ((r ^ 2 / t) ^ m / (m !)))) :=
    (Real.sqrt_mul (le_of_lt hnfac) _).symm
  rw [← Real.sqrt_mul hf, hcomb, ← hsq, Real.sqrt_sq hL]

theorem summable_choose_geom (n : ℕ) (ht0 : 0 < t) (ht1 : t < 1) :
    Summable fun m : ℕ => ((m + n).choose n : ℝ) * t ^ m :=
  summable_choose_mul_geometric_of_norm_lt_one n (by rwa [Real.norm_of_nonneg (le_of_lt ht0)])

theorem tsum_choose_geom (n : ℕ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∑' m : ℕ, ((m + n).choose n : ℝ) * t ^ m = 1 / (1 - t) ^ (n + 1) :=
  tsum_choose_mul_geometric_of_norm_lt_one n (by rwa [Real.norm_of_nonneg (le_of_lt ht0)])

theorem summable_Ssum (n : ℕ) (hr : 0 ≤ r) :
    Summable fun m : ℕ => Real.sqrt ((n + m)! ) / (m !) * r ^ m := by
  set t : ℝ := 1 / 2 with ht_def
  have ht0 : (0:ℝ) < t := by norm_num [ht_def]
  have ht1 : t < 1 := by norm_num [ht_def]
  have hsum : Summable fun m : ℕ =>
      (1 / 2 : ℝ) * (Real.sqrt (n !) * (((m + n).choose n : ℝ) * t ^ m
        + (r ^ 2 / t) ^ m / (m !))) :=
    (((summable_choose_geom n ht0 ht1).add
      (Real.summable_pow_div_factorial (r ^ 2 / t))).mul_left _).mul_left _
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hsum
  rw [Ssum_term_eq n m hr ht0]
  have hf : (0:ℝ) ≤ ((m + n).choose n : ℝ) * t ^ m := by positivity
  have hg : (0:ℝ) ≤ (r ^ 2 / t) ^ m / (m !) := by positivity
  have hamgm : Real.sqrt (((m + n).choose n : ℝ) * t ^ m) * Real.sqrt ((r ^ 2 / t) ^ m / (m !))
      ≤ (1 / 2) * (((m + n).choose n : ℝ) * t ^ m + (r ^ 2 / t) ^ m / (m !)) := by
    nlinarith [sq_nonneg (Real.sqrt (((m + n).choose n : ℝ) * t ^ m)
        - Real.sqrt ((r ^ 2 / t) ^ m / (m !))), Real.sq_sqrt hf, Real.sq_sqrt hg,
      Real.sqrt_nonneg (((m + n).choose n : ℝ) * t ^ m),
      Real.sqrt_nonneg ((r ^ 2 / t) ^ m / (m !))]
  have hnfac : (0:ℝ) ≤ Real.sqrt (n !) := Real.sqrt_nonneg _
  calc Real.sqrt (n !) * (Real.sqrt (((m + n).choose n : ℝ) * t ^ m)
        * Real.sqrt ((r ^ 2 / t) ^ m / (m !)))
      ≤ Real.sqrt (n !) * ((1 / 2) * (((m + n).choose n : ℝ) * t ^ m
          + (r ^ 2 / t) ^ m / (m !))) := mul_le_mul_of_nonneg_left hamgm hnfac
    _ = (1 / 2 : ℝ) * (Real.sqrt (n !) * (((m + n).choose n : ℝ) * t ^ m
          + (r ^ 2 / t) ^ m / (m !))) := by ring

/-- Estimate (5.1), obtained from Cauchy–Schwarz and the negative binomial series. -/
theorem Ssum_le (n : ℕ) (hr : 0 ≤ r) (ht0 : 0 < t) (ht1 : t < 1) :
    Ssum n r ≤ Real.sqrt (n !) * (1 - t) ^ (-((n : ℝ) + 1) / 2) * Real.exp (r ^ 2 / (2 * t)) := by
  have ht : (0:ℝ) < 1 - t := by linarith
  set f : ℕ → ℝ := fun m => ((m + n).choose n : ℝ) * t ^ m with hf_def
  set g : ℕ → ℝ := fun m => (r ^ 2 / t) ^ m / (m !) with hg_def
  have hfnn : ∀ m, 0 ≤ f m := fun m => by positivity
  have hgnn : ∀ m, 0 ≤ g m := fun m => by positivity
  have hfsum : Summable f := summable_choose_geom n ht0 ht1
  have hgsum : Summable g := Real.summable_pow_div_factorial _
  have hftsum : ∑' m, f m = 1 / (1 - t) ^ (n + 1) := tsum_choose_geom n ht0 ht1
  have hgtsum : ∑' m, g m = Real.exp (r ^ 2 / t) := by
    rw [hg_def, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- the two square roots on the right-hand side
  have hsqrt_f : Real.sqrt (1 / (1 - t) ^ (n + 1)) = (1 - t) ^ (-((n : ℝ) + 1) / 2) := by
    have hpos : (0:ℝ) < (1 - t) ^ (-((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos ht _
    have hsq : ((1 - t) ^ (-((n : ℝ) + 1) / 2)) ^ 2 = 1 / (1 - t) ^ (n + 1) := by
      rw [← Real.rpow_natCast ((1 - t) ^ (-((n : ℝ) + 1) / 2)) 2, ← Real.rpow_mul (le_of_lt ht),
        show (-((n : ℝ) + 1) / 2) * ((2 : ℕ) : ℝ) = -((n : ℝ) + 1) by push_cast; ring,
        Real.rpow_neg (le_of_lt ht), ← Real.rpow_natCast (1 - t) (n + 1)]
      push_cast
      rw [one_div]
    rw [← hsq, Real.sqrt_sq (le_of_lt hpos)]
  have hsqrt_g : Real.sqrt (Real.exp (r ^ 2 / t)) = Real.exp (r ^ 2 / (2 * t)) := by
    have : Real.exp (r ^ 2 / t) = (Real.exp (r ^ 2 / (2 * t))) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
      ring
    rw [this, Real.sqrt_sq (le_of_lt (Real.exp_pos _))]
  refine Summable.tsum_le_of_sum_le (summable_Ssum n hr) (fun s => ?_)
  have hterm : ∀ m ∈ s, Real.sqrt ((n + m)! ) / (m !) * r ^ m
      = Real.sqrt (n !) * (Real.sqrt (f m) * Real.sqrt (g m)) :=
    fun m _ => Ssum_term_eq n m hr ht0
  calc ∑ m ∈ s, Real.sqrt ((n + m)! ) / (m !) * r ^ m
      = Real.sqrt (n !) * ∑ m ∈ s, Real.sqrt (f m) * Real.sqrt (g m) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hterm
    _ ≤ Real.sqrt (n !) * (Real.sqrt (∑ m ∈ s, f m) * Real.sqrt (∑ m ∈ s, g m)) := by
        exact mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s hfnn hgnn)
          (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (n !) * (Real.sqrt (1 / (1 - t) ^ (n + 1)) * Real.sqrt (Real.exp (r ^ 2 / t))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt (hftsum ▸ hfsum.sum_le_tsum s (fun m _ => hfnn m))
        · exact Real.sqrt_le_sqrt (hgtsum ▸ hgsum.sum_le_tsum s (fun m _ => hgnn m))
    _ = Real.sqrt (n !) * (1 - t) ^ (-((n : ℝ) + 1) / 2) * Real.exp (r ^ 2 / (2 * t)) := by
        rw [hsqrt_f, hsqrt_g]
        ring

theorem Ssum_pos (n : ℕ) (hr : 0 ≤ r) : 0 < Ssum n r := by
  have hsum := summable_Ssum n hr
  have hnn : ∀ m : ℕ, 0 ≤ Real.sqrt ((n + m)! ) / (m !) * r ^ m := fun m => by positivity
  have h0 : 0 < Real.sqrt ((n + 0)! ) / ((0)! ) * r ^ 0 := by
    have : (0:ℝ) < ((n + 0)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have := Real.sqrt_pos.2 this
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
    exact this
  exact lt_of_lt_of_le h0 (hsum.le_tsum 0 (fun m _ => hnn m))

end

/-- Estimate (5.2): the choice `t = r/(r+√n)` in (5.1). -/
theorem log_Ssum_le {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    Real.log (Ssum n r) ≤ (1 / 2) * Real.log (n !) + r * Real.sqrt n + (r + r ^ 2) / 2 := by
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (1:ℝ) ≤ Real.sqrt n := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hnR
  have hsnpos : (0:ℝ) < Real.sqrt n := lt_of_lt_of_le zero_lt_one hsn
  have hsnsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  set t : ℝ := r / (r + Real.sqrt n) with ht_def
  have hden : (0:ℝ) < r + Real.sqrt n := by linarith
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by
    rw [ht_def, div_lt_one hden]
    linarith
  have hone_sub : 1 - t = Real.sqrt n / (r + Real.sqrt n) := by
    rw [ht_def]
    field_simp
    ring
  have hnfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hbound := Ssum_le n (le_of_lt hr) ht0 ht1
  have hpos : 0 < Real.sqrt (n !) * (1 - t) ^ (-((n : ℝ) + 1) / 2) * Real.exp (r ^ 2 / (2 * t)) := by
    have h1 : 0 < Real.sqrt ((n ! : ℕ) : ℝ) := Real.sqrt_pos.2 hnfac
    have h2 : (0:ℝ) < (1 - t) ^ (-((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hlog := Real.log_le_log (Ssum_pos n (le_of_lt hr)) hbound
  refine hlog.trans ?_
  -- expand the logarithm of the right-hand side
  have hlog_expand : Real.log (Real.sqrt (n !) * (1 - t) ^ (-((n : ℝ) + 1) / 2)
      * Real.exp (r ^ 2 / (2 * t)))
      = (1 / 2) * Real.log (n !) + (-((n : ℝ) + 1) / 2) * Real.log (1 - t) + r ^ 2 / (2 * t) := by
    have h1 : 0 < Real.sqrt ((n ! : ℕ) : ℝ) := Real.sqrt_pos.2 hnfac
    have h2 : (0:ℝ) < (1 - t) ^ (-((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
      Real.log_mul (ne_of_gt h1) (ne_of_gt h2), Real.log_exp,
      Real.log_rpow (by linarith : (0:ℝ) < 1 - t), Real.log_sqrt (le_of_lt hnfac)]
    ring
  rw [hlog_expand]
  -- bound the two remaining terms
  have hlog1 : -Real.log (1 - t) ≤ r / Real.sqrt n := by
    have h1 : Real.log (1 - t) = -Real.log ((r + Real.sqrt n) / Real.sqrt n) := by
      rw [hone_sub, ← Real.log_inv]
      congr 1
      field_simp
    have h2 : Real.log ((r + Real.sqrt n) / Real.sqrt n) ≤ r / Real.sqrt n := by
      have hx : (0:ℝ) < (r + Real.sqrt n) / Real.sqrt n := by positivity
      have := Real.log_le_sub_one_of_pos hx
      have heq : (r + Real.sqrt n) / Real.sqrt n - 1 = r / Real.sqrt n := by
        field_simp
        ring
      linarith [heq ▸ this]
    linarith
  have hterm2 : r ^ 2 / (2 * t) = r ^ 2 / 2 + r * Real.sqrt n / 2 := by
    rw [ht_def]
    field_simp
  have hcoef : (-((n : ℝ) + 1) / 2) * Real.log (1 - t) ≤ ((n : ℝ) + 1) / 2 * (r / Real.sqrt n) := by
    have hnn : (0:ℝ) ≤ ((n : ℝ) + 1) / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hlog1 hnn
    calc (-((n : ℝ) + 1) / 2) * Real.log (1 - t)
        = ((n : ℝ) + 1) / 2 * (-Real.log (1 - t)) := by ring
      _ ≤ ((n : ℝ) + 1) / 2 * (r / Real.sqrt n) := this
  have hsimp : ((n : ℝ) + 1) / 2 * (r / Real.sqrt n) ≤ r * Real.sqrt n / 2 + r / 2 := by
    have key : ((n : ℝ) + 1) * r ≤ (r * Real.sqrt n + r) * Real.sqrt n := by
      nlinarith [hsnsq, hsn, hr]
    have hlhs : ((n : ℝ) + 1) / 2 * (r / Real.sqrt n)
        = (((n : ℝ) + 1) * r) / (2 * Real.sqrt n) := by
      field_simp
    have hrhs : r * Real.sqrt n / 2 + r / 2
        = ((r * Real.sqrt n + r) * Real.sqrt n) / (2 * Real.sqrt n) := by
      field_simp
    rw [hlhs, hrhs]
    gcongr
  rw [hterm2]
  linarith

end SparseFock
