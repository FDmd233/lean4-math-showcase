import RequestProject.Support
import RequestProject.Curvature

/-!
# The crossing radii `ρ_j`

This file formalises the algebraic part of Lemma 2.4 (radial grid) of the paper
*Zeros of high derivatives of sparse Fock series*: the exact formula (2.11) for
`log ρ_j`, the squeeze (2.14) and the strict monotonicity of the crossing radii.

Throughout, `n` is the order of the derivative, `m_j = ν_j - n` is the exponent of the
`j`-th active term, `A_j = √(ν_j!)/m_j!` its coefficient and
`ρ_j = (A_j / A_{j+1})^{1/q_j}` the crossing radius of the terms `j` and `j+1`.
-/

namespace SparseFock

open scoped BigOperators Nat

/-- The exponent `m_j = ν_j - n` of the `j`-th term of the `n`-th derivative. -/
noncomputable def mOf (p : ℝ) (n j : ℕ) : ℕ := nu p j - n

/-- The coefficient `A_j = √(ν_j!) / m_j!`. -/
noncomputable def Acoef (p : ℝ) (n j : ℕ) : ℝ := Real.sqrt ((nu p j)! ) / (mOf p n j)!

/-- The crossing radius `ρ_j = (A_j / A_{j+1})^{1/q_j}`. -/
noncomputable def rho (p : ℝ) (n j : ℕ) : ℝ :=
  (Acoef p n j / Acoef p n (j + 1)) ^ (1 / (qgap p j : ℝ))

/-- The logarithmic weight increment `f_n(t) = log (t+1) - ½ log (n+t+1)` whose averages over
blocks of consecutive integers give the crossing radii. -/
noncomputable def fterm (n : ℕ) (t : ℕ) : ℝ :=
  Real.log ((t : ℝ) + 1) - (1 / 2) * Real.log ((n : ℝ) + t + 1)

variable {p : ℝ} {n j : ℕ}

theorem fterm_eq_neg_dstep (n t : ℕ) : fterm n t = -dstep n 1 t := by
  rw [dstep_eq, fterm, Real.log_one]
  ring

theorem fterm_lt_fterm_succ (n t : ℕ) : fterm n t < fterm n (t + 1) := by
  have h := dstep_sub_dstep_succ_pos n 1 t
  rw [fterm_eq_neg_dstep, fterm_eq_neg_dstep]
  linarith

theorem fterm_mono (n : ℕ) : Monotone (fterm n) :=
  monotone_nat_of_le_succ (fun t => (fterm_lt_fterm_succ n t).le)

theorem exp_fterm (n t : ℕ) :
    Real.exp (fterm n t) = ((t : ℝ) + 1) / Real.sqrt ((n : ℝ) + t + 1) := by
  have h1 : (0:ℝ) < (t : ℝ) + 1 := by positivity
  have h2 : (0:ℝ) < (n : ℝ) + t + 1 := by positivity
  rw [fterm, Real.exp_sub, Real.exp_log h1]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2]
  ring_nf

/-- Factorials telescope: `log ((a+b)!) = log (a!) + ∑_{s=1}^{b} log (a+s)`. -/
theorem log_factorial_add (a b : ℕ) :
    Real.log (((a + b)! : ℕ) : ℝ)
      = Real.log ((a ! : ℕ) : ℝ) + ∑ s ∈ Finset.Icc 1 b, Real.log ((a : ℝ) + s) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 : a + (b + 1) = (a + b) + 1 := by omega
    have hpos : (0:ℝ) < (((a + b)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [h1, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (ne_of_gt hpos)]
    push_cast at ih
    rw [ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ b + 1)]
    push_cast
    ring_nf

theorem Acoef_pos (p : ℝ) (n j : ℕ) : 0 < Acoef p n j := by
  have h1 : (0:ℝ) < Real.sqrt (((nu p j)! : ℕ) : ℝ) := by
    have : (0:ℝ) < (((nu p j)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    exact Real.sqrt_pos.2 this
  have h2 : (0:ℝ) < (((mOf p n j)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Acoef]
  positivity

theorem mOf_succ (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j) :
    mOf p n (j + 1) = mOf p n j + qgap p j := by
  have h := nu_add_qgap hp hj
  simp only [mOf]
  omega

theorem nu_eq_add_mOf (hn : n ≤ nu p j) : nu p j = n + mOf p n j := by
  simp only [mOf]
  omega

theorem log_Acoef (p : ℝ) (n j : ℕ) :
    Real.log (Acoef p n j)
      = (1 / 2) * Real.log (((nu p j)! : ℕ) : ℝ) - Real.log (((mOf p n j)! : ℕ) : ℝ) := by
  have h1 : (0:ℝ) < (((nu p j)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : (0:ℝ) < (((mOf p n j)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Acoef, Real.log_div (ne_of_gt (Real.sqrt_pos.2 h1)) (ne_of_gt h2), Real.log_sqrt (le_of_lt h1)]
  ring

/-- Formula (2.11): the exact expression for `log ρ_j` as an average over a block of
`q_j` consecutive integers. -/
theorem log_rho_eq (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j) :
    Real.log (rho p n j)
      = (1 / (qgap p j : ℝ)) * ∑ s ∈ Finset.Icc 1 (qgap p j),
          (Real.log ((mOf p n j : ℝ) + s) - (1 / 2) * Real.log ((n : ℝ) + mOf p n j + s)) := by
  set m := mOf p n j with hm
  set q := qgap p j with hq
  have hnuj : nu p j = n + m := nu_eq_add_mOf hn
  have hnuj1 : nu p (j + 1) = n + m + q := by
    have := nu_add_qgap hp hj
    omega
  have hmsucc : mOf p n (j + 1) = m + q := mOf_succ hp hj hn
  have hlog : Real.log (Acoef p n j / Acoef p n (j + 1))
      = ∑ s ∈ Finset.Icc 1 q,
        (Real.log ((m : ℝ) + s) - (1 / 2) * Real.log ((n : ℝ) + m + s)) := by
    rw [Real.log_div (ne_of_gt (Acoef_pos p n j)) (ne_of_gt (Acoef_pos p n (j + 1))),
      log_Acoef, log_Acoef, hnuj, hnuj1, hmsucc]
    have e1 : Real.log (((n + m + q)! : ℕ) : ℝ)
        = Real.log (((n + m)! : ℕ) : ℝ) + ∑ s ∈ Finset.Icc 1 q, Real.log (((n + m : ℕ) : ℝ) + s) :=
      log_factorial_add (n + m) q
    have e2 : Real.log (((m + q)! : ℕ) : ℝ)
        = Real.log (((m)! : ℕ) : ℝ) + ∑ s ∈ Finset.Icc 1 q, Real.log ((m : ℝ) + s) :=
      log_factorial_add m q
    rw [e1, e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
    push_cast
    ring
  rw [rho, Real.log_rpow (div_pos (Acoef_pos p n j) (Acoef_pos p n (j + 1))), hlog]

/-- The same formula, written as an average of the increments `f_n(m_j + i)`. -/
theorem log_rho_eq_range (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j) :
    Real.log (rho p n j)
      = (1 / (qgap p j : ℝ)) * ∑ i ∈ Finset.range (qgap p j), fterm n (mOf p n j + i) := by
  rw [log_rho_eq hp hj hn]
  congr 1
  have hreindex : ∀ f : ℕ → ℝ, ∑ s ∈ Finset.Icc 1 (qgap p j), f s
      = ∑ i ∈ Finset.range (qgap p j), f (i + 1) := by
    intro f
    induction qgap p j with
    | zero => simp
    | succ q ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1), ih, Finset.sum_range_succ]
  rw [hreindex]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fterm]
  push_cast
  ring_nf

theorem rho_pos (p : ℝ) (n j : ℕ) : 0 < rho p n j :=
  Real.rpow_pos_of_pos (div_pos (Acoef_pos p n j) (Acoef_pos p n (j + 1))) _

/-- The squeeze (2.14): `f_n(m_j) ≤ log ρ_j ≤ f_n(m_j + q_j - 1)`. -/
theorem log_rho_squeeze (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j) :
    fterm n (mOf p n j) ≤ Real.log (rho p n j) ∧
      Real.log (rho p n j) ≤ fterm n (mOf p n j + (qgap p j - 1)) := by
  have hq1 : 1 ≤ qgap p j := one_le_qgap hp hj
  have hqpos : (0:ℝ) < (qgap p j : ℝ) := by exact_mod_cast hq1
  have hlow : (qgap p j : ℝ) * fterm n (mOf p n j)
      ≤ ∑ i ∈ Finset.range (qgap p j), fterm n (mOf p n j + i) := by
    have := Finset.card_nsmul_le_sum (Finset.range (qgap p j))
      (fun i => fterm n (mOf p n j + i)) (fterm n (mOf p n j))
      (fun i _ => fterm_mono n (by omega))
    simpa [nsmul_eq_mul] using this
  have hhigh : ∑ i ∈ Finset.range (qgap p j), fterm n (mOf p n j + i)
      ≤ (qgap p j : ℝ) * fterm n (mOf p n j + (qgap p j - 1)) := by
    have := Finset.sum_le_card_nsmul (Finset.range (qgap p j))
      (fun i => fterm n (mOf p n j + i)) (fterm n (mOf p n j + (qgap p j - 1)))
      (fun i hi => by
        refine fterm_mono n ?_
        have : i < qgap p j := Finset.mem_range.1 hi
        omega)
    simpa [nsmul_eq_mul] using this
  rw [log_rho_eq_range hp hj hn,
    show (1 / (qgap p j : ℝ)) * (∑ i ∈ Finset.range (qgap p j), fterm n (mOf p n j + i))
      = (∑ i ∈ Finset.range (qgap p j), fterm n (mOf p n j + i)) / (qgap p j : ℝ) by ring]
  constructor
  · rw [le_div_iff₀ hqpos]
    linarith
  · rw [div_le_iff₀ hqpos]
    linarith

/-- The squeeze (2.14) in multiplicative form:
`(m_j+1)/√(n+m_j+1) ≤ ρ_j ≤ (m_j+q_j)/√(n+m_j+q_j)`. -/
theorem rho_squeeze (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j) :
    ((mOf p n j : ℝ) + 1) / Real.sqrt ((n : ℝ) + mOf p n j + 1) ≤ rho p n j ∧
      rho p n j ≤ ((mOf p n j : ℝ) + qgap p j) /
        Real.sqrt ((n : ℝ) + mOf p n j + qgap p j) := by
  have hq1 : 1 ≤ qgap p j := one_le_qgap hp hj
  obtain ⟨h1, h2⟩ := log_rho_squeeze hp hj hn
  have hrho : Real.exp (Real.log (rho p n j)) = rho p n j := Real.exp_log (rho_pos p n j)
  constructor
  · have := Real.exp_le_exp.2 h1
    rw [hrho, exp_fterm] at this
    simpa using this
  · have := Real.exp_le_exp.2 h2
    rw [hrho, exp_fterm] at this
    have hcast : ((mOf p n j + (qgap p j - 1) : ℕ) : ℝ) + 1 = (mOf p n j : ℝ) + qgap p j := by
      have : mOf p n j + (qgap p j - 1) + 1 = mOf p n j + qgap p j := by omega
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) this
    have hcast2 : (n : ℝ) + ((mOf p n j + (qgap p j - 1) : ℕ) : ℝ) + 1
        = (n : ℝ) + mOf p n j + qgap p j := by
      push_cast [Nat.cast_sub hq1]
      ring
    rw [hcast, hcast2] at this
    exact this

/-- The crossing radii strictly increase in `j`. -/
theorem rho_lt_rho_succ (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j) :
    rho p n j < rho p n (j + 1) := by
  have hq1 : 1 ≤ qgap p j := one_le_qgap hp hj
  have hj1 : 1 ≤ j + 1 := by omega
  have hn1 : n ≤ nu p (j + 1) := le_trans hn (nu_lt_nu_succ hp hj).le
  have hmsucc : mOf p n (j + 1) = mOf p n j + qgap p j := mOf_succ hp hj hn
  obtain ⟨_, hupper⟩ := log_rho_squeeze hp hj hn
  obtain ⟨hlower, _⟩ := log_rho_squeeze hp hj1 hn1
  have hstep : fterm n (mOf p n j + (qgap p j - 1)) < fterm n (mOf p n (j + 1)) := by
    rw [hmsucc]
    have : mOf p n j + (qgap p j - 1) + 1 = mOf p n j + qgap p j := by omega
    calc fterm n (mOf p n j + (qgap p j - 1))
        < fterm n (mOf p n j + (qgap p j - 1) + 1) := fterm_lt_fterm_succ _ _
      _ = fterm n (mOf p n j + qgap p j) := by rw [this]
  have hlog : Real.log (rho p n j) < Real.log (rho p n (j + 1)) := by
    linarith
  have := Real.exp_lt_exp.2 hlog
  rwa [Real.exp_log (rho_pos p n j), Real.exp_log (rho_pos p n (j + 1))] at this

/-- A bounded crossing radius forces `m_j = O(√n)`: if `ρ_j ≤ b` then
`(m_j + 1)^2 ≤ b^2 (n + m_j + 1)`. -/
theorem sq_le_of_rho_le (hp : 1 ≤ p) (hj : 1 ≤ j) (hn : n ≤ nu p j) {b : ℝ}
    (hb : rho p n j ≤ b) :
    ((mOf p n j : ℝ) + 1) ^ 2 ≤ b ^ 2 * ((n : ℝ) + mOf p n j + 1) := by
  obtain ⟨h1, -⟩ := rho_squeeze hp hj hn
  have hbpos : 0 < b := lt_of_lt_of_le (rho_pos p n j) hb
  have hsq : (0:ℝ) < Real.sqrt ((n : ℝ) + mOf p n j + 1) := by
    apply Real.sqrt_pos.2
    positivity
  have hle : ((mOf p n j : ℝ) + 1) / Real.sqrt ((n : ℝ) + mOf p n j + 1) ≤ b := le_trans h1 hb
  rw [div_le_iff₀ hsq] at hle
  have hsqsq : Real.sqrt ((n : ℝ) + mOf p n j + 1) * Real.sqrt ((n : ℝ) + mOf p n j + 1)
      = (n : ℝ) + mOf p n j + 1 := Real.mul_self_sqrt (by positivity)
  nlinarith [hle, hsqsq, hsq, hbpos, Real.sqrt_nonneg ((n : ℝ) + mOf p n j + 1)]

end SparseFock
