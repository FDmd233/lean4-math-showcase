import RequestProject.Tail
import RequestProject.MinModulus

/-!
# The two-term model and the transfer of its zeros

At a crossing radius `ρ` the two adjacent principal terms of `F_p^{(n)}` have equal
modulus, and the two-term model

`H(z) = A_j z^{m₀} + A_{j+1} z^{m₀+q}`

has the `q` nonzero zeros `z = ρ e^{iθ}` with `(e^{iθ})^q = -1`.

This file shows that, under the global tail domination of `Tail.lean`, the *true*
derivative `F_p^{(n)}` has a zero within distance `2 ρ c₀ / q` of each such model zero.
The complex-analytic input is the minimum-modulus principle of `MinModulus.lean`,
applied in the logarithmic variable `w`, i.e. to `w ↦ F_p^{(n)}(ρ e^{iθ} e^{w})`.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-! ### An abstract Rouché-type localisation statement -/

/-- **Localisation of a model zero.**  Let `f` be entire, let `z₀` have modulus `ρ`, and
suppose that on the disc `‖w‖ ≤ ζ` the function `w ↦ f (z₀ e^w)` is approximated by the
two-term model `P e^{m₀ w} (1 - e^{q w})` with error at most `S e^{m₀ Re w} K`, where
`‖P‖ = S` and `q ζ = c₀ ≤ 1/2`.  If `e^{m₀ ζ} K < c₀ / 4`, then `f` has a zero within
distance `2 ρ ζ` of `z₀`. -/
theorem exists_zero_of_dominant_two_term
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ P : ℂ} {ρ S K c₀ ζ : ℝ} {m₀ q : ℕ}
    (hz₀ : ‖z₀‖ = ρ) (hρ : 0 < ρ) (hP : ‖P‖ = S) (hSpos : 0 < S) (hKnn : 0 ≤ K)
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1 / 2) (hζpos : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hqζ : (q : ℝ) * ζ = c₀)
    (hdom : ∀ w : ℂ, ‖w‖ ≤ ζ →
      ‖f (z₀ * Complex.exp w) - P * Complex.exp ((m₀ : ℂ) * w)
        * (1 - Complex.exp ((q : ℂ) * w))‖ ≤ S * Real.exp ((m₀ : ℝ) * w.re) * K)
    (hsmall : Real.exp ((m₀ : ℝ) * ζ) * K < c₀ / 4) :
    ∃ z : ℂ, f z = 0 ∧ ‖z - z₀‖ ≤ 2 * ρ * ζ := by
  have hm₀ : (0:ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg _
  have hKlt : K < c₀ / 4 := by
    have h1 : (1:ℝ) ≤ Real.exp ((m₀ : ℝ) * ζ) := Real.one_le_exp (by positivity)
    nlinarith
  have hΨdiff : Differentiable ℂ (fun w : ℂ => f (z₀ * Complex.exp w)) :=
    hf.comp ((differentiable_id.cexp).const_mul _)
  -- modulus of the model term
  have hmod : ∀ w : ℂ, ‖P * Complex.exp ((m₀ : ℂ) * w) * (1 - Complex.exp ((q : ℂ) * w))‖
      = S * Real.exp ((m₀ : ℝ) * w.re) * ‖1 - Complex.exp ((q : ℂ) * w)‖ := by
    intro w
    rw [norm_mul, norm_mul, hP, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  -- value at the centre
  have hcentre : ‖f (z₀ * Complex.exp 0)‖ ≤ S * K := by
    have h := hdom 0 (by simpa using hζpos.le)
    simpa using h
  -- lower bound on the boundary circle
  have hbdry : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) ζ →
      S * Real.exp (-((m₀ : ℝ) * ζ)) * (c₀ / 2 - K) ≤ ‖f (z₀ * Complex.exp w)‖ := by
    intro w hw
    have hwn : ‖w‖ = ζ := by simpa [Metric.mem_sphere] using hw
    have hσ : |w.re| ≤ ζ := le_trans (Complex.abs_re_le_norm w) (le_of_eq hwn)
    have hqw : ‖(q : ℂ) * w‖ = c₀ := by
      rw [norm_mul, Complex.norm_natCast, hwn, hqζ]
    have hqw1 : ‖(q : ℂ) * w‖ ≤ 1 := by rw [hqw]; linarith
    have hexp := Complex.norm_exp_sub_one_sub_id_le hqw1
    have hlow : c₀ / 2 ≤ ‖1 - Complex.exp ((q : ℂ) * w)‖ := by
      have h3 : ‖(q : ℂ) * w‖ ≤ ‖Complex.exp ((q : ℂ) * w) - 1‖
          + ‖Complex.exp ((q : ℂ) * w) - 1 - (q : ℂ) * w‖ := by
        calc ‖(q : ℂ) * w‖
            = ‖(Complex.exp ((q : ℂ) * w) - 1)
                - (Complex.exp ((q : ℂ) * w) - 1 - (q : ℂ) * w)‖ := by
              congr 1
              ring
          _ ≤ _ := norm_sub_le _ _
      rw [hqw] at h3 hexp
      rw [show (1 : ℂ) - Complex.exp ((q : ℂ) * w) = -(Complex.exp ((q : ℂ) * w) - 1) by ring,
        norm_neg]
      nlinarith
    have h1 := hdom w (le_of_eq hwn)
    have h3 : ‖P * Complex.exp ((m₀ : ℂ) * w) * (1 - Complex.exp ((q : ℂ) * w))‖
        - ‖f (z₀ * Complex.exp w)‖ ≤ S * Real.exp ((m₀ : ℝ) * w.re) * K := by
      refine le_trans ?_ h1
      have h4 := norm_sub_norm_le
        (P * Complex.exp ((m₀ : ℂ) * w) * (1 - Complex.exp ((q : ℂ) * w)))
        (f (z₀ * Complex.exp w))
      rw [show (P * Complex.exp ((m₀ : ℂ) * w) * (1 - Complex.exp ((q : ℂ) * w)))
          - f (z₀ * Complex.exp w)
          = -(f (z₀ * Complex.exp w) - P * Complex.exp ((m₀ : ℂ) * w)
            * (1 - Complex.exp ((q : ℂ) * w))) by ring, norm_neg] at h4
      exact h4
    rw [hmod w] at h3
    have hE : 0 < Real.exp ((m₀ : ℝ) * w.re) := Real.exp_pos _
    have hSE : 0 < S * Real.exp ((m₀ : ℝ) * w.re) := mul_pos hSpos hE
    have h5 : S * Real.exp ((m₀ : ℝ) * w.re) * (c₀ / 2)
        ≤ S * Real.exp ((m₀ : ℝ) * w.re) * ‖1 - Complex.exp ((q : ℂ) * w)‖ :=
      mul_le_mul_of_nonneg_left hlow hSE.le
    have hexpand : S * Real.exp ((m₀ : ℝ) * w.re) * (c₀ / 2 - K)
        = S * Real.exp ((m₀ : ℝ) * w.re) * (c₀ / 2)
          - S * Real.exp ((m₀ : ℝ) * w.re) * K := by ring
    have hstep : S * Real.exp ((m₀ : ℝ) * w.re) * (c₀ / 2 - K)
        ≤ ‖f (z₀ * Complex.exp w)‖ := by
      rw [hexpand]
      linarith
    refine le_trans ?_ hstep
    have hmono : Real.exp (-((m₀ : ℝ) * ζ)) ≤ Real.exp ((m₀ : ℝ) * w.re) := by
      refine Real.exp_le_exp.2 ?_
      have hneg : -ζ ≤ w.re := neg_le_of_abs_le hσ
      nlinarith
    have hck : 0 ≤ c₀ / 2 - K := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hSpos.le) hck
  -- minimum modulus
  have hMlt : ‖f (z₀ * Complex.exp 0)‖ < S * Real.exp (-((m₀ : ℝ) * ζ)) * (c₀ / 2 - K) := by
    refine lt_of_le_of_lt hcentre ?_
    have hEpos : 0 < Real.exp (-((m₀ : ℝ) * ζ)) := Real.exp_pos _
    have hexpo : Real.exp (-((m₀ : ℝ) * ζ)) * Real.exp ((m₀ : ℝ) * ζ) = 1 := by
      rw [← Real.exp_add]
      simp
    have h2 : K < Real.exp (-((m₀ : ℝ) * ζ)) * (c₀ / 4) := by
      have h := mul_lt_mul_of_pos_left hsmall hEpos
      rw [← mul_assoc, hexpo, one_mul] at h
      exact h
    have h3 : c₀ / 4 ≤ c₀ / 2 - K := by linarith
    have hkey : K < Real.exp (-((m₀ : ℝ) * ζ)) * (c₀ / 2 - K) :=
      lt_of_lt_of_le h2 (mul_le_mul_of_nonneg_left h3 hEpos.le)
    have hmul := mul_lt_mul_of_pos_left hkey hSpos
    have heq : S * (Real.exp (-((m₀ : ℝ) * ζ)) * (c₀ / 2 - K))
        = S * Real.exp (-((m₀ : ℝ) * ζ)) * (c₀ / 2 - K) := by ring
    linarith [hmul, heq.le, heq.ge]
  obtain ⟨w, hwmem, hwzero⟩ :=
    exists_zero_of_norm_lt_on_sphere hΨdiff hζpos hbdry hMlt
  refine ⟨z₀ * Complex.exp w, hwzero, ?_⟩
  have hwn : ‖w‖ ≤ ζ := by simpa [Metric.mem_closedBall] using hwmem
  rw [show z₀ * Complex.exp w - z₀ = z₀ * (Complex.exp w - 1) by ring, norm_mul, hz₀]
  have h1 : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ :=
    Complex.norm_exp_sub_one_le (le_trans hwn hζ1)
  calc ρ * ‖Complex.exp w - 1‖ ≤ ρ * (2 * ζ) := by
        refine mul_le_mul_of_nonneg_left (le_trans h1 (by linarith)) hρ.le
    _ = 2 * ρ * ζ := by ring

/-! ### Specialisation to the sparse Fock series -/

variable {p : ℝ} {n m₀ q Q : ℕ}

/-- Every iterated derivative of `F_p` is entire. -/
theorem iteratedDeriv_F_differentiable (p : ℝ) (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n (F p)) := by
  have h := (entireCoeff_fcoeff p).iteratedDeriv_eq n
  have hF : iteratedDeriv n (F p) = iteratedDeriv n (sumSeries fun k => (fcoeff p k : ℂ)) := rfl
  rw [hF, h]
  exact ((entireCoeff_fcoeff p).shift n).differentiable

/-- On the support, the modulus of the `m`-th term equals `exp (Phi n r m)`. -/
theorem dcoeff_mul_pow_eq_exp_Phi (p : ℝ) (n m : ℕ) {r : ℝ} (hr : 0 < r)
    (hm : IsSupp p (m + n)) :
    dcoeff p n m * r ^ m = Real.exp (Phi n r m) := by
  have hfac : (0:ℝ) < ((n + m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmfac : (0:ℝ) < ((m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hval : Real.exp (Phi n r m) = Real.sqrt ((n + m)! ) / (m !) * r ^ m := by
    rw [Phi, Real.exp_add, Real.exp_sub]
    have h1 : Real.exp ((1 / 2) * Real.log ((n + m)! : ℝ)) = Real.sqrt ((n + m)! : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hfac]
      ring_nf
    have h2 : Real.exp (Real.log ((m)! : ℝ)) = ((m)! : ℝ) := Real.exp_log hmfac
    have h3 : Real.exp ((m : ℝ) * Real.log r) = r ^ m := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hr, Real.rpow_natCast]
    rw [h1, h2, h3]
  rw [hval, dcoeff, if_pos hm, show (m + n)! = (n + m)! by rw [Nat.add_comm]]

theorem dcoeff_pos_of_isSupp (p : ℝ) (n m : ℕ) (hm : IsSupp p (m + n)) : 0 < dcoeff p n m := by
  rw [dcoeff, if_pos hm]
  have h1 : (0:ℝ) < Real.sqrt ((m + n)! : ℝ) := by
    have : (0:ℝ) < ((m + n)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    exact Real.sqrt_pos.2 this
  have h2 : (0:ℝ) < ((m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  positivity

/-- The derivative differs from its two principal terms by at most the tail sum. -/
theorem norm_sub_two_terms_le (p : ℝ) (n m₀ q : ℕ) (hq : 1 ≤ q) (z : ℂ) :
    ‖iteratedDeriv n (F p) z
        - (((dcoeff p n m₀ : ℝ) : ℂ) * z ^ m₀
            + ((dcoeff p n (m₀ + q) : ℝ) : ℂ) * z ^ (m₀ + q))‖
      ≤ ∑' m : ℕ, (if m = m₀ ∨ m = m₀ + q then 0 else dcoeff p n m * ‖z‖ ^ m) := by
  classical
  set a : ℕ → ℂ := fun m => ((dcoeff p n m : ℝ) : ℂ) * z ^ m with ha
  have hsum : Summable a := summable_dcoeff_mul_pow_complex p n z
  have hne : m₀ ≠ m₀ + q := by omega
  have hs1 : Summable fun m : ℕ => (if m = m₀ then a m₀ else 0) :=
    summable_of_ne_finset_zero (s := {m₀}) (fun m hm => if_neg (by simpa using hm))
  have hs2 : Summable fun m : ℕ => (if m = m₀ + q then a (m₀ + q) else 0) :=
    summable_of_ne_finset_zero (s := {m₀ + q}) (fun m hm => if_neg (by simpa using hm))
  have hnormb : ∀ m : ℕ,
      ‖(if m = m₀ ∨ m = m₀ + q then 0 else a m)‖
        = (if m = m₀ ∨ m = m₀ + q then 0 else dcoeff p n m * ‖z‖ ^ m) := by
    intro m
    by_cases hm : m = m₀ ∨ m = m₀ + q
    · rw [if_pos hm, if_pos hm, norm_zero]
    · rw [if_neg hm, if_neg hm, ha]
      dsimp only
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (dcoeff_nonneg p n m)]
  have htarget : Summable fun m : ℕ =>
      (if m = m₀ ∨ m = m₀ + q then 0 else dcoeff p n m * ‖z‖ ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      (summable_dcoeff_mul_pow p n (norm_nonneg z))
    · split
      · exact le_rfl
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
    · split
      · exact mul_nonneg (dcoeff_nonneg p n m) (by positivity)
      · exact le_rfl
  have hnsum : Summable fun m : ℕ => ‖(if m = m₀ ∨ m = m₀ + q then 0 else a m)‖ :=
    htarget.congr (fun m => (hnormb m).symm)
  have hbsum : Summable fun m : ℕ => (if m = m₀ ∨ m = m₀ + q then 0 else a m) :=
    Summable.of_norm hnsum
  have hbeq : ∀ m : ℕ, (if m = m₀ ∨ m = m₀ + q then 0 else a m)
      = a m - (if m = m₀ then a m₀ else 0) - (if m = m₀ + q then a (m₀ + q) else 0) := by
    intro m
    by_cases h1 : m = m₀
    · subst h1
      rw [if_pos (Or.inl rfl), if_pos rfl, if_neg hne]
      ring
    · by_cases h2 : m = m₀ + q
      · subst h2
        rw [if_pos (Or.inr rfl), if_neg h1, if_pos rfl]
        ring
      · rw [if_neg (by tauto), if_neg h1, if_neg h2]
        ring
  have htsum : ∑' m, (if m = m₀ ∨ m = m₀ + q then 0 else a m)
      = (∑' m, a m) - a m₀ - a (m₀ + q) := by
    have he1 : ∑' m : ℕ, (if m = m₀ then a m₀ else 0) = a m₀ := by
      rw [tsum_eq_single m₀ (fun b hb => if_neg hb), if_pos rfl]
    have he2 : ∑' m : ℕ, (if m = m₀ + q then a (m₀ + q) else 0) = a (m₀ + q) := by
      rw [tsum_eq_single (m₀ + q) (fun b hb => if_neg hb), if_pos rfl]
    rw [tsum_congr hbeq, (hsum.sub hs1).tsum_sub hs2, hsum.tsum_sub hs1, he1, he2]
  have hval : iteratedDeriv n (F p) z - (a m₀ + a (m₀ + q))
      = ∑' m, (if m = m₀ ∨ m = m₀ + q then 0 else a m) := by
    rw [htsum, iteratedDeriv_F_eq_dcoeff]
    ring
  rw [hval]
  exact le_trans (norm_tsum_le_tsum_norm hnsum) (le_of_eq (tsum_congr hnormb))

/-- **Transfer of a model zero.**  Under the global tail domination, the true derivative
`F_p^{(n)}` vanishes somewhere within distance `2 ρ c₀ / q` of the model zero
`ρ e^{iθ}`, where `(e^{iθ})^q = -1`. -/
theorem exists_zero_near_model
    {ρ c c₀ θ : ℝ}
    (hρ : 0 < ρ) (hq : 1 ≤ q)
    (hphase : (Complex.exp ((θ : ℝ) * Complex.I)) ^ q = -1)
    (hsupp₀ : IsSupp p (m₀ + n))
    (hcrossA : dcoeff p n m₀ * ρ ^ m₀ = dcoeff p n (m₀ + q) * ρ ^ (m₀ + q))
    (hcross : Phi n ρ (m₀ + q) = Phi n ρ m₀)
    (hcl : c ≤ dstep n ρ m₀) (hcr : dstep n ρ (m₀ + q - 1) ≤ -c)
    (hsupp : ∀ m : ℕ, dcoeff p n m ≠ 0 → m ≠ m₀ → m ≠ m₀ + q →
      (m + Q ≤ m₀ ∨ m₀ + q + Q ≤ m))
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1 / 2)
    (hζc : c₀ / q < c)
    (hsmall : Real.exp ((m₀ : ℝ) * (c₀ / q)) *
        (Real.exp (-(c - c₀ / q) * Q) *
          (((m₀ : ℝ) + 1) + Real.exp ((q : ℝ) * (c₀ / q))
            / (1 - Real.exp (-(c - c₀ / q))))) < c₀ / 4) :
    ∃ z : ℂ, iteratedDeriv n (F p) z = 0 ∧
      ‖z - (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ ≤ 2 * ρ * (c₀ / q) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hζpos : 0 < c₀ / q := by positivity
  have hqζ : (q : ℝ) * (c₀ / q) = c₀ := by field_simp
  have hζ1 : c₀ / q ≤ 1 := by
    rw [div_le_one hqR]
    linarith
  have hA₀pos : 0 < dcoeff p n m₀ := dcoeff_pos_of_isSupp p n m₀ hsupp₀
  have hA₁ρ : dcoeff p n (m₀ + q) * ρ ^ q = dcoeff p n m₀ := by
    have hρm : (0:ℝ) < ρ ^ m₀ := by positivity
    have h : dcoeff p n m₀ * ρ ^ m₀ = dcoeff p n (m₀ + q) * ρ ^ q * ρ ^ m₀ := by
      rw [hcrossA, pow_add]
      ring
    exact (mul_right_cancel₀ (ne_of_gt hρm) h).symm
  have hSexp : dcoeff p n m₀ * ρ ^ m₀ = Real.exp (Phi n ρ m₀) :=
    dcoeff_mul_pow_eq_exp_Phi p n m₀ hρ hsupp₀
  have hz₀norm : ‖(ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ = ρ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]
  have hPnorm : ‖((dcoeff p n m₀ : ℝ) : ℂ) * ((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) ^ m₀‖
      = dcoeff p n m₀ * ρ ^ m₀ := by
    rw [norm_mul, norm_pow, hz₀norm, Complex.norm_real, Real.norm_of_nonneg hA₀pos.le]
  -- identify the principal part
  have hprin : ∀ w : ℂ,
      ((dcoeff p n m₀ : ℝ) : ℂ)
          * (((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) * Complex.exp w) ^ m₀
        + ((dcoeff p n (m₀ + q) : ℝ) : ℂ)
          * (((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) * Complex.exp w) ^ (m₀ + q)
      = (((dcoeff p n m₀ : ℝ) : ℂ) * ((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) ^ m₀)
          * Complex.exp ((m₀ : ℂ) * w) * (1 - Complex.exp ((q : ℂ) * w)) := by
    intro w
    have he1 : Complex.exp ((m₀ : ℂ) * w) = (Complex.exp w) ^ m₀ := by
      rw [← Complex.exp_nat_mul]
    have he2 : Complex.exp ((q : ℂ) * w) = (Complex.exp w) ^ q := by
      rw [← Complex.exp_nat_mul]
    have hz₀q : ((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) ^ q = -((ρ : ℂ) ^ q) := by
      rw [mul_pow, hphase]
      ring
    have hA : ((dcoeff p n (m₀ + q) : ℝ) : ℂ) * ((ρ : ℂ) ^ q)
        = ((dcoeff p n m₀ : ℝ) : ℂ) := by
      have h := congrArg (fun t : ℝ => (t : ℂ)) hA₁ρ
      push_cast at h ⊢
      exact h
    set Z : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) with hZ
    have key0 : (Z * Complex.exp w) ^ m₀ = Z ^ m₀ * (Complex.exp w) ^ m₀ := mul_pow _ _ _
    have key1 : (Z * Complex.exp w) ^ (m₀ + q)
        = (Z ^ m₀ * (Complex.exp w) ^ m₀) * (Z ^ q * (Complex.exp w) ^ q) := by
      rw [mul_pow, pow_add, pow_add]
      ring
    rw [he1, he2, key0, key1, hz₀q]
    linear_combination (-(Z ^ m₀ * (Complex.exp w) ^ m₀ * (Complex.exp w) ^ q)) * hA
  -- the domination hypothesis
  have hdom : ∀ w : ℂ, ‖w‖ ≤ c₀ / q →
      ‖iteratedDeriv n (F p) (((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) * Complex.exp w)
        - (((dcoeff p n m₀ : ℝ) : ℂ) * ((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) ^ m₀)
            * Complex.exp ((m₀ : ℂ) * w) * (1 - Complex.exp ((q : ℂ) * w))‖
        ≤ (dcoeff p n m₀ * ρ ^ m₀) * Real.exp ((m₀ : ℝ) * w.re) *
            (Real.exp (-(c - c₀ / q) * Q) *
              (((m₀ : ℝ) + 1) + Real.exp ((q : ℝ) * (c₀ / q))
                / (1 - Real.exp (-(c - c₀ / q))))) := by
    intro w hw
    have hσ : |w.re| ≤ c₀ / q := le_trans (Complex.abs_re_le_norm w) hw
    have hznorm : ‖((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) * Complex.exp w‖
        = ρ * Real.exp w.re := by
      rw [norm_mul, hz₀norm, Complex.norm_exp]
    have h1 := norm_sub_two_terms_le p n m₀ q hq
      (((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) * Complex.exp w)
    rw [hprin w] at h1
    refine le_trans h1 ?_
    rw [hznorm]
    have h2 := tail_sum_bound (p := p) (n := n) (m₀ := m₀) (q := q) (Q := Q)
      (ρ := ρ) (σ := w.re) (c := c) (γ := c₀ / q) hρ hq hσ hζc hcross hcl hcr hsupp
    refine le_trans h2 (le_of_eq ?_)
    rw [Real.exp_add, ← hSexp]
    ring
  have hmain := exists_zero_of_dominant_two_term
    (f := iteratedDeriv n (F p)) (iteratedDeriv_F_differentiable p n)
    (z₀ := (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I))
    (P := ((dcoeff p n m₀ : ℝ) : ℂ) * ((ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) ^ m₀)
    (ρ := ρ) (S := dcoeff p n m₀ * ρ ^ m₀)
    (K := Real.exp (-(c - c₀ / q) * Q) *
      (((m₀ : ℝ) + 1) + Real.exp ((q : ℝ) * (c₀ / q)) / (1 - Real.exp (-(c - c₀ / q)))))
    (c₀ := c₀) (ζ := c₀ / q) (m₀ := m₀) (q := q)
    hz₀norm hρ hPnorm (by positivity) ?_ hc₀ hc₀1 hζpos hζ1 hqζ hdom hsmall
  · exact hmain
  · have hden : 0 < 1 - Real.exp (-(c - c₀ / q)) := by
      have : Real.exp (-(c - c₀ / q)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      linarith
    positivity

end SparseFock
