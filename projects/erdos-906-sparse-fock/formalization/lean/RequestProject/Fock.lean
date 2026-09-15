import RequestProject.EntirePowerSeries
import RequestProject.Support
import RequestProject.Growth

/-!
# The sparse Fock series `F_p`

For `p ≥ 1` we define the entire function
`F_p(z) = ∑_{j ≥ 1} z^{ν_j} / √(ν_j!)`, `ν_j = ⌊j^p⌋`,
of the paper *Zeros of high derivatives of sparse Fock series*, and we prove:

* `F_p` is entire (Lemma 2.2);
* the growth bound `‖F_p(z)‖ ≤ √(1+|z|²) exp((1+|z|²)/2)`, i.e. the upper half of (1.3);
* the termwise formula (2.5) for `F_p^{(n)}`;
* strict positivity of every derivative on the positive real axis, hence transcendence;
* the exact multiplicity (4.2) of the zero of `F_p^{(n)}` at the origin.
-/

namespace SparseFock

open scoped Nat BigOperators
open Classical

/-- The support of the sparse series: the exponents `ν_j`, `j ≥ 1`. -/
def IsSupp (p : ℝ) (k : ℕ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ nu p j = k

/-- The Taylor coefficients of `F_p`. -/
noncomputable def fcoeff (p : ℝ) (k : ℕ) : ℝ := if IsSupp p k then 1 / Real.sqrt (k !) else 0

/-- The sparse Fock series `F_p(z) = ∑_{j≥1} z^{ν_j}/√(ν_j!)`. -/
noncomputable def F (p : ℝ) (z : ℂ) : ℂ := sumSeries (fun k => (fcoeff p k : ℂ)) z

variable {p : ℝ} {n k : ℕ}

/-- The descending factorial as a quotient of factorials. -/
theorem descFactorial_mul_factorial (n m : ℕ) : (m + n).descFactorial n * m ! = (m + n)! := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    have h1 : m + (n + 1) = (m + 1) + n := by omega
    have h2 : ((m + 1) + n).descFactorial (n + 1) = (m + 1) * (((m + 1) + n).descFactorial n) := by
      rw [Nat.descFactorial_succ]
      congr 1
      omega
    rw [h1, h2]
    calc (m + 1) * ((m + 1 + n).descFactorial n) * m !
        = (m + 1 + n).descFactorial n * ((m + 1) * m !) := by ring
      _ = (m + 1 + n).descFactorial n * (m + 1)! := by rw [Nat.factorial_succ]
      _ = (m + 1 + n)! := ih (m + 1)

theorem fcoeff_nonneg (p : ℝ) (k : ℕ) : 0 ≤ fcoeff p k := by
  unfold fcoeff
  split
  · positivity
  · exact le_rfl

theorem fcoeff_le (p : ℝ) (k : ℕ) : fcoeff p k ≤ 1 / Real.sqrt (k !) := by
  unfold fcoeff
  split
  · exact le_rfl
  · positivity

theorem fcoeff_pos_of_isSupp (h : IsSupp p k) : 0 < fcoeff p k := by
  have hfac : (0:ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [fcoeff, if_pos h]
  positivity

theorem entireCoeff_fcoeff (p : ℝ) : EntireCoeff (fun k => (fcoeff p k : ℂ)) := by
  intro r hr
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_pow_div_sqrt_factorial (le_of_lt hr))
  have h1 : ‖((fcoeff p k : ℝ) : ℂ)‖ = fcoeff p k := by
    rw [Complex.norm_real, Real.norm_of_nonneg (fcoeff_nonneg p k)]
  rw [h1]
  calc fcoeff p k * r ^ k ≤ (1 / Real.sqrt (k !)) * r ^ k :=
        mul_le_mul_of_nonneg_right (fcoeff_le p k) (by positivity)
    _ = r ^ k / Real.sqrt (k !) := by ring

/-- Lemma 2.2: `F_p` is entire. -/
theorem F_differentiable (p : ℝ) : Differentiable ℂ (F p) :=
  (entireCoeff_fcoeff p).differentiable

/-- The upper half of the growth statement (1.3):
`|F_p(z)| ≤ √(1+|z|²) exp((1+|z|²)/2)`, so `log M_{F_p}(r) ≤ ½ r² + O(log r)`. -/
theorem F_norm_le (p : ℝ) (z : ℂ) :
    ‖F p z‖ ≤ Real.sqrt (1 + ‖z‖ ^ 2) * Real.exp ((1 + ‖z‖ ^ 2) / 2) := by
  have hmaj := tsum_pow_div_sqrt_factorial_le' (r := ‖z‖) (norm_nonneg z)
  refine le_trans (norm_tsum_le_tsum_norm ((entireCoeff_fcoeff p).summable_norm_at z)) ?_
  refine le_trans ?_ hmaj
  refine Summable.tsum_le_tsum (fun k => ?_) ((entireCoeff_fcoeff p).summable_norm_at z)
    (summable_pow_div_sqrt_factorial (norm_nonneg z))
  have h1 : ‖((fcoeff p k : ℝ) : ℂ) * z ^ k‖ = fcoeff p k * ‖z‖ ^ k := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (fcoeff_nonneg p k)]
  rw [h1]
  calc fcoeff p k * ‖z‖ ^ k ≤ (1 / Real.sqrt (k !)) * ‖z‖ ^ k :=
        mul_le_mul_of_nonneg_right (fcoeff_le p k) (by positivity)
    _ = ‖z‖ ^ k / Real.sqrt (k !) := by ring

/-- The growth bound in the form giving order at most two and type at most `1/2`:
for every `ε > 0` there is `C > 0` with `|F_p(z)| ≤ C exp((1/2 + ε)|z|²)`. -/
theorem F_norm_le_exp (p : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ C > 0, ∀ z : ℂ, ‖F p z‖ ≤ C * Real.exp ((1 / 2 + eps) * ‖z‖ ^ 2) := by
  refine ⟨Real.exp (1 / 2) * (1 + 1 / eps), by positivity, fun z => ?_⟩
  set r : ℝ := ‖z‖ with hr_def
  have hr : 0 ≤ r := norm_nonneg z
  have h1 : Real.sqrt (1 + r ^ 2) ≤ 1 + r ^ 2 := by
    have h : (1:ℝ) ≤ 1 + r ^ 2 := by nlinarith
    calc Real.sqrt (1 + r ^ 2) ≤ Real.sqrt ((1 + r ^ 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + r ^ 2 := Real.sqrt_sq (by nlinarith)
  have hexp1 : (1:ℝ) ≤ Real.exp (eps * r ^ 2) := Real.one_le_exp (by positivity)
  have hexp2 : eps * r ^ 2 ≤ Real.exp (eps * r ^ 2) := (Real.add_one_le_exp _).trans' (by linarith)
  have h2 : 1 + r ^ 2 ≤ (1 + 1 / eps) * Real.exp (eps * r ^ 2) := by
    have hr2 : r ^ 2 ≤ Real.exp (eps * r ^ 2) / eps := by
      rw [le_div_iff₀ heps]
      linarith [hexp2]
    have : (1 + 1 / eps) * Real.exp (eps * r ^ 2)
        = Real.exp (eps * r ^ 2) + Real.exp (eps * r ^ 2) / eps := by
      field_simp
    rw [this]
    linarith
  have hmain := F_norm_le p z
  have hsplit : Real.exp ((1 + r ^ 2) / 2) = Real.exp (1 / 2) * Real.exp (r ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgoal : Real.exp (1 / 2) * (1 + 1 / eps) * Real.exp ((1 / 2 + eps) * r ^ 2)
      = ((1 + 1 / eps) * Real.exp (eps * r ^ 2)) * (Real.exp (1 / 2) * Real.exp (r ^ 2 / 2)) := by
    have hsum : (1 / 2 + eps) * r ^ 2 = eps * r ^ 2 + r ^ 2 / 2 := by ring
    rw [hsum, Real.exp_add]
    ring
  rw [hgoal]
  rw [hsplit] at hmain
  refine hmain.trans (mul_le_mul (h1.trans h2) le_rfl (by positivity) (by positivity))

theorem summable_fcoeff_mul_pow (p : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun k : ℕ => fcoeff p k * x ^ k := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (fcoeff_nonneg p k) (pow_nonneg hx k))
    (fun k => ?_) (summable_pow_div_sqrt_factorial hx)
  calc fcoeff p k * x ^ k ≤ (1 / Real.sqrt (k !)) * x ^ k :=
        mul_le_mul_of_nonneg_right (fcoeff_le p k) (by positivity)
    _ = x ^ k / Real.sqrt (k !) := by ring

/-- On the real axis `F_p` takes real values. -/
theorem F_eq_ofReal (p : ℝ) (x : ℝ) : F p (x : ℂ) = ((∑' k : ℕ, fcoeff p k * x ^ k : ℝ) : ℂ) := by
  rw [F, sumSeries, Complex.ofReal_tsum]
  exact tsum_congr (fun k => by push_cast; ring)

/-- The lower bound for the maximum modulus used for the type: every support term is a lower
bound for `F_p` on the positive real axis. -/
theorem le_F_re_of_isSupp (hk : IsSupp p k) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k / Real.sqrt (k !) ≤ (F p (x : ℂ)).re := by
  rw [F_eq_ofReal, Complex.ofReal_re]
  have hterm : x ^ k / Real.sqrt (k !) = fcoeff p k * x ^ k := by
    rw [fcoeff, if_pos hk]
    ring
  rw [hterm]
  exact (summable_fcoeff_mul_pow p hx).le_tsum k
    (fun i _ => mul_nonneg (fcoeff_nonneg p i) (pow_nonneg hx i))

/-- Formula (2.5): the `n`-th derivative of `F_p` is `∑_{ν_j ≥ n} A_j z^{m_j}` with
`A_j = √(ν_j!)/m_j!`; here the summation index is `m = ν_j - n`. -/
theorem iteratedDeriv_F (p : ℝ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (F p) z =
      ∑' m : ℕ, ((if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0 : ℝ) : ℂ)
        * z ^ m := by
  have h := (entireCoeff_fcoeff p).iteratedDeriv_eq n
  have hF : iteratedDeriv n (F p) = iteratedDeriv n (sumSeries fun k => (fcoeff p k : ℂ)) := rfl
  rw [hF, h, sumSeries]
  refine tsum_congr (fun m => ?_)
  congr 1
  -- identify the shifted coefficient
  have hfac : (0:ℝ) < ((m + n)! : ℝ) := by exact_mod_cast Nat.factorial_pos (m + n)
  have hmfac : (0:ℝ) < ((m)! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hdesc : (((m + n).descFactorial n : ℕ) : ℝ) * ((m)! : ℝ) = ((m + n)! : ℝ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) (descFactorial_mul_factorial n m)
  rw [shiftCoeff, fcoeff]
  by_cases hsupp : IsSupp p (m + n)
  · rw [if_pos hsupp, if_pos hsupp]
    have hs : Real.sqrt ((m + n)! : ℝ) * Real.sqrt ((m + n)! : ℝ) = ((m + n)! : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hfac)
    have hsne : Real.sqrt ((m + n)! : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hfac)
    have hreal : (((m + n).descFactorial n : ℕ) : ℝ) * (1 / Real.sqrt ((m + n)!))
        = Real.sqrt ((m + n)!) / (m !) := by
      rw [mul_one_div, div_eq_div_iff hsne (ne_of_gt hmfac), hs]
      exact hdesc
    rw [← hreal]
    push_cast
    ring
  · rw [if_neg hsupp, if_neg hsupp]
    simp

/-- Every derivative of `F_p` is a positive real number on the positive real axis. -/
theorem iteratedDeriv_F_eq_ofReal (p : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (F p) (x : ℂ) =
      ((∑' m : ℕ, (if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0) * x ^ m : ℝ)
        : ℂ) := by
  rw [iteratedDeriv_F, Complex.ofReal_tsum]
  refine tsum_congr (fun m => ?_)
  push_cast
  ring

theorem summable_iteratedDeriv_coeff (p : ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun m : ℕ =>
      (if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0) * x ^ m := by
  have hc := ((entireCoeff_fcoeff p).shift n) (x + 1) (by positivity)
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hc
  · have : (0:ℝ) ≤ (if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0) := by
      split <;> positivity
    positivity
  · have hnorm : ‖shiftCoeff (fun k => (fcoeff p k : ℂ)) n m‖
        = (if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0) := by
      rw [shiftCoeff, fcoeff]
      by_cases hsupp : IsSupp p (m + n)
      · rw [if_pos hsupp, if_pos hsupp]
        have hfac : (0:ℝ) < ((m + n)! : ℝ) := by exact_mod_cast Nat.factorial_pos (m + n)
        have hmfac : (0:ℝ) < ((m)! : ℝ) := by exact_mod_cast Nat.factorial_pos m
        have hdesc : (((m + n).descFactorial n : ℕ) : ℝ) * ((m)! : ℝ) = ((m + n)! : ℝ) := by
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) (descFactorial_mul_factorial n m)
        have hs : Real.sqrt ((m + n)! : ℝ) * Real.sqrt ((m + n)! : ℝ) = ((m + n)! : ℝ) :=
          Real.mul_self_sqrt (le_of_lt hfac)
        have hsne : Real.sqrt ((m + n)! : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hfac)
        have hval : (((m + n).descFactorial n : ℕ) : ℝ) * (1 / Real.sqrt ((m + n)!))
            = Real.sqrt ((m + n)!) / (m !) := by
          rw [mul_one_div, div_eq_div_iff hsne (ne_of_gt hmfac), hs]
          exact hdesc
        rw [show ((((m + n).descFactorial n : ℕ) : ℂ) * ((1 / Real.sqrt ((m + n)! ) : ℝ) : ℂ))
            = (((((m + n).descFactorial n : ℕ) : ℝ) * (1 / Real.sqrt ((m + n)!)) : ℝ) : ℂ) by
          push_cast; ring]
        rw [Complex.norm_real, hval, Real.norm_of_nonneg (by positivity)]
      · rw [if_neg hsupp, if_neg hsupp]
        simp
    rw [hnorm]
    have hnn : (0:ℝ) ≤ (if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0) := by
      split <;> positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx (by linarith) m) hnn

/-- The exponent of the first active term of `F_p^{(n)}`, i.e. `m_{j_0} = min_{ν_j ≥ n}(ν_j - n)`. -/
noncomputable def mZero (p : ℝ) (n : ℕ) : ℕ := sInf {m : ℕ | IsSupp p (m + n)}

theorem nonempty_supp (hp : 1 ≤ p) (n : ℕ) : {m : ℕ | IsSupp p (m + n)}.Nonempty := by
  refine ⟨nu p (max n 1) - n, ?_⟩
  have hj : 1 ≤ max n 1 := le_max_right _ _
  have hge : n ≤ nu p (max n 1) := le_trans (le_max_left n 1) (le_nu hp _)
  exact ⟨max n 1, hj, by omega⟩

theorem isSupp_mZero (hp : 1 ≤ p) (n : ℕ) : IsSupp p (mZero p n + n) :=
  Nat.sInf_mem (nonempty_supp hp n)

theorem not_isSupp_of_lt_mZero {n m : ℕ} (hm : m < mZero p n) : ¬ IsSupp p (m + n) :=
  Nat.notMem_of_lt_sInf hm

/-- Every derivative of `F_p` is strictly positive on the positive real axis. -/
theorem iteratedDeriv_F_pos (hp : 1 ≤ p) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (iteratedDeriv n (F p) (x : ℂ)).re := by
  rw [iteratedDeriv_F_eq_ofReal, Complex.ofReal_re]
  have hsum := summable_iteratedDeriv_coeff p n (le_of_lt hx)
  have hnn : ∀ m : ℕ,
      0 ≤ (if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0) * x ^ m := by
    intro m
    have : (0:ℝ) ≤ (if IsSupp p (m + n) then Real.sqrt ((m + n)! ) / (m !) else 0) := by
      split <;> positivity
    positivity
  have hpos : 0 < (if IsSupp p (mZero p n + n) then
      Real.sqrt ((mZero p n + n)! ) / ((mZero p n)!) else 0) * x ^ mZero p n := by
    rw [if_pos (isSupp_mZero hp n)]
    have h1 : (0:ℝ) < Real.sqrt ((mZero p n + n)! : ℝ) := by
      have : (0:ℝ) < ((mZero p n + n)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      exact Real.sqrt_pos.2 this
    have h2 : (0:ℝ) < ((mZero p n)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  exact lt_of_lt_of_le hpos (hsum.le_tsum _ (fun m _ => hnn m))

theorem iteratedDeriv_F_ne_zero (hp : 1 ≤ p) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (F p) (x : ℂ) ≠ 0 := by
  intro h
  have := iteratedDeriv_F_pos hp n hx
  rw [h] at this
  simp at this

/-- The iterated derivative of a polynomial function. -/
theorem iteratedDeriv_polynomial (P : Polynomial ℂ) (N : ℕ) :
    iteratedDeriv N (fun z : ℂ => P.eval z) = fun z => ((Polynomial.derivative^[N]) P).eval z := by
  induction N generalizing P with
  | zero => simp
  | succ N ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (fun z : ℂ => P.eval z) = fun z => (Polynomial.derivative P).eval z := by
      funext z
      exact Polynomial.deriv P
    rw [hderiv, ih (Polynomial.derivative P), Function.iterate_succ_apply]

/-- `F_p` is transcendental: it is not a polynomial. -/
theorem F_not_polynomial (hp : 1 ≤ p) (P : Polynomial ℂ) :
    (fun z : ℂ => P.eval z) ≠ F p := by
  intro h
  set N := P.natDegree + 1 with hN
  have h1 : iteratedDeriv N (fun z : ℂ => P.eval z) = iteratedDeriv N (F p) := by rw [h]
  rw [iteratedDeriv_polynomial P N,
    Polynomial.iterate_derivative_eq_zero (by omega : P.natDegree < N)] at h1
  have h2 := congrFun h1 (1 : ℂ)
  simp only [Polynomial.eval_zero] at h2
  refine iteratedDeriv_F_ne_zero hp N (x := 1) one_pos ?_
  rw [show (((1:ℝ)) : ℂ) = (1:ℂ) by norm_num, ← h2]

/-- The value at the origin of an iterated derivative of `F_p`. -/
theorem iteratedDeriv_F_at_zero (p : ℝ) (N : ℕ) :
    iteratedDeriv N (F p) 0 = ((N ! : ℝ) : ℂ) * (fcoeff p N : ℂ) := by
  have h := (entireCoeff_fcoeff p).iteratedDeriv_eq N
  have hF : iteratedDeriv N (F p) = iteratedDeriv N (sumSeries fun k => (fcoeff p k : ℂ)) := rfl
  rw [hF, h, sumSeries_zero, shiftCoeff]
  simp [Nat.descFactorial_self]

/-- Formula (4.2): the multiplicity of the zero of `F_p^{(n)}` at the origin equals
`m_{j_0} = min_{ν_j ≥ n} (ν_j - n)`. -/
theorem origin_multiplicity (hp : 1 ≤ p) (n : ℕ) :
    (∀ i < mZero p n, iteratedDeriv (n + i) (F p) 0 = 0) ∧
      iteratedDeriv (n + mZero p n) (F p) 0 ≠ 0 := by
  constructor
  · intro i hi
    rw [iteratedDeriv_F_at_zero]
    have : fcoeff p (n + i) = 0 := by
      rw [fcoeff, if_neg]
      rw [show n + i = i + n by omega]
      exact not_isSupp_of_lt_mZero hi
    rw [this]
    simp
  · rw [iteratedDeriv_F_at_zero]
    have hsupp : IsSupp p (n + mZero p n) := by
      rw [show n + mZero p n = mZero p n + n by omega]
      exact isSupp_mZero hp n
    have hpos : 0 < fcoeff p (n + mZero p n) := fcoeff_pos_of_isSupp hsupp
    have hfacpos : (0:ℝ) < ((n + mZero p n)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, not_or]
    exact ⟨ne_of_gt hfacpos, ne_of_gt hpos⟩

end SparseFock
