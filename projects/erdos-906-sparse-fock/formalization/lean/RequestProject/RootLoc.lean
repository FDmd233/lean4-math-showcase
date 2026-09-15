import Mathlib

/-!
# Quantitative localisation of the roots of `1 + w^q`

This is the elementary complex-analytic step (§6A of the round specification, the display
`|1-\ee^{v_0}|\geq\frac1{4}|v_0|` in the proof of Proposition 3.3 of the manuscript).

If `|1 + w^q| ≤ K` is small and `w` is a priori close to the unit circle in the sense
`|q log ‖w‖| ≤ 2`, then `w` is within `16 K / q` of one of the `q` model roots
`exp((2ℓ+1)π i / q)`, `0 ≤ ℓ < q`.

Both the modulus part and the phase part are proved with explicit constants; no numerical
tactic is used to hide either step.
-/

namespace SparseFock

open Complex

/-! ### The phase step -/

/-- If `‖exp (i δ) - 1‖ ≤ ε ≤ 1/2` and `|δ| ≤ π`, then `|δ| ≤ (π/2) ε`. -/
theorem abs_le_of_norm_exp_sub_one_le {δ ε : ℝ} (hδ : |δ| ≤ Real.pi)
    (hε : ε ≤ 1/2) (h : ‖Complex.exp ((δ : ℝ) * Complex.I) - 1‖ ≤ ε) :
    |δ| ≤ (Real.pi / 2) * ε := by
  have hexp : Complex.exp ((δ : ℝ) * Complex.I) - 1
      = ((Real.cos δ - 1 : ℝ) : ℂ) + ((Real.sin δ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hre : |Real.cos δ - 1| ≤ ε := by
    refine le_trans ?_ h
    rw [hexp]
    simpa using Complex.abs_re_le_norm
      (((Real.cos δ - 1 : ℝ) : ℂ) + ((Real.sin δ : ℝ) : ℂ) * Complex.I)
  have him : |Real.sin δ| ≤ ε := by
    refine le_trans ?_ h
    rw [hexp]
    simpa using Complex.abs_im_le_norm
      (((Real.cos δ - 1 : ℝ) : ℂ) + ((Real.sin δ : ℝ) : ℂ) * Complex.I)
  have hcos : (1:ℝ)/2 ≤ Real.cos δ := by
    have := abs_le.1 hre
    linarith [this.1]
  -- hence `|δ| ≤ π/2`
  have hhalf : |δ| ≤ Real.pi / 2 := by
    by_contra hcon
    push_neg at hcon
    have hcosneg : Real.cos δ ≤ 0 := by
      rcases le_or_gt 0 δ with hd | hd
      · have h1 : Real.pi / 2 ≤ δ := by
          rw [abs_of_nonneg hd] at hcon; linarith
        have h2 : δ ≤ Real.pi + Real.pi / 2 := by
          have := abs_le.1 hδ
          linarith [this.2, Real.pi_pos]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
      · have h1 : Real.pi / 2 ≤ -δ := by
          rw [abs_of_neg hd] at hcon; linarith
        have h2 : -δ ≤ Real.pi + Real.pi / 2 := by
          have := abs_le.1 hδ
          linarith [this.1, Real.pi_pos]
        have := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
        rwa [Real.cos_neg] at this
    linarith
  -- `2/π |δ| ≤ sin |δ| = |sin δ| ≤ ε`
  have hsin : 2 / Real.pi * |δ| ≤ Real.sin |δ| :=
    Real.mul_le_sin (abs_nonneg _) hhalf
  have hsineq : Real.sin |δ| ≤ |Real.sin δ| := by
    rcases le_or_gt 0 δ with hd | hd
    · rw [abs_of_nonneg hd]
      exact le_abs_self _
    · rw [abs_of_neg hd, Real.sin_neg, ← abs_neg (Real.sin δ)]
      exact le_abs_self _
  have hsin' : 2 / Real.pi * |δ| ≤ |Real.sin δ| := le_trans hsin hsineq
  have hπ : 0 < Real.pi := Real.pi_pos
  have : 2 / Real.pi * |δ| ≤ ε := le_trans hsin' him
  rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at this
  nlinarith

/-! ### The modulus step -/

/-- If `|x^q - 1| ≤ K` and `|q log x| ≤ 2` then `|x - 1| ≤ 8 K / q`. -/
theorem abs_sub_one_le_of_pow_close {x K : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x)
    (hK : 0 ≤ K) (hlog : |(q : ℝ) * Real.log x| ≤ 2) (hpow : |x ^ q - 1| ≤ K) :
    |x - 1| ≤ 8 * K / (q : ℝ) := by
  have hqR : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  rcases le_or_gt 1 x with h1 | h1
  · -- `x ≥ 1`: Bernoulli
    have hb : 1 + (q : ℝ) * (x - 1) ≤ x ^ q := by
      have := one_add_mul_le_pow (a := x - 1) (by linarith) q
      simpa using this
    have h2 : x ^ q - 1 ≤ K := by
      have := abs_le.1 hpow
      linarith [this.2]
    have h3 : (q : ℝ) * (x - 1) ≤ K := by linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - 1), le_div_iff₀ hqpos]
    nlinarith
  · -- `x < 1`
    have hlogneg : Real.log x < 0 := Real.log_neg hx h1
    set y : ℝ := -((q : ℝ) * Real.log x) with hy
    have hypos : 0 < y := by
      rw [hy]; nlinarith
    have hy2 : y ≤ 2 := by
      have := abs_le.1 hlog
      rw [hy]; linarith [this.1]
    have hxq : x ^ q = Real.exp (-y) := by
      rw [hy, neg_neg, ← Real.log_pow, Real.exp_log (by positivity)]
    have h2 : 1 - x ^ q ≤ K := by
      have := abs_le.1 hpow
      linarith [this.1]
    -- `1 - exp (-y) ≥ y exp (-2)`
    have hey : Real.exp (-2 : ℝ) ≤ Real.exp (-y) := Real.exp_le_exp.2 (by linarith)
    have hkey : y * Real.exp (-y) ≤ 1 - Real.exp (-y) := by
      have h3 : 1 + y ≤ Real.exp y := by
        have := Real.add_one_le_exp y; linarith
      have h4 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-y), Real.exp_pos y]
    have he2 : (1:ℝ)/8 ≤ Real.exp (-2 : ℝ) := by
      have h5 : Real.exp (2:ℝ) ≤ 8 := by
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have h0 : (0:ℝ) < Real.exp 1 := Real.exp_pos _
        have hsq : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        rw [hsq]
        nlinarith
      have h6 : Real.exp (-2:ℝ) * Real.exp (2:ℝ) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-2:ℝ), Real.exp_pos (2:ℝ)]
    have hyK : y ≤ 8 * K := by
      rw [hxq] at h2
      nlinarith [Real.exp_pos (-y)]
    -- `1 - x ≤ -log x = y / q`
    have hlogle : 1 - x ≤ -Real.log x := by
      have := Real.add_one_le_exp (Real.log x)
      rw [Real.exp_log hx] at this
      linarith
    have hneglog : -Real.log x = y / (q : ℝ) := by
      rw [hy]; field_simp
    rw [abs_of_nonpos (by linarith : x - 1 ≤ 0)]
    rw [hneglog] at hlogle
    have hfin : y / (q : ℝ) ≤ 8 * K / (q : ℝ) := (div_le_div_iff_of_pos_right hqpos).2 hyK
    linarith

/-! ### The localisation lemma -/

/-- **Root localisation.**  If `‖1 + w^q‖ ≤ K ≤ 1/4` and `|q log ‖w‖| ≤ 2`, then `w` is
within `16 K / q` of one of the `q` model roots `exp((2ℓ+1)π i / q)`. -/
theorem exists_model_root_near {w : ℂ} {q : ℕ} {K : ℝ} (hq : 1 ≤ q) (hw : w ≠ 0)
    (hK : 0 ≤ K) (hK4 : K ≤ 1/4)
    (hmod : |(q : ℝ) * Real.log ‖w‖| ≤ 2)
    (hclose : ‖1 + w ^ q‖ ≤ K) :
    ∃ l : ℕ, l < q ∧
      ‖w - Complex.exp (((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ) : ℝ) * Complex.I)‖
        ≤ 16 * K / (q : ℝ) := by
  have hqR : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q : ℝ) := by linarith
  have hqnat : 0 < q := hq
  set x : ℝ := ‖w‖ with hxdef
  have hxpos : 0 < x := norm_pos_iff.2 hw
  set φ : ℝ := Complex.arg w with hφdef
  have hwrep : ((x : ℝ) : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) = w :=
    Complex.norm_mul_exp_arg_mul_I w
  -- modulus
  have hpowx : ‖w ^ q‖ = x ^ q := by rw [norm_pow]
  have hxq : |x ^ q - 1| ≤ K := by
    have h := abs_norm_sub_norm_le (w ^ q) (-1 : ℂ)
    have h2 : ‖w ^ q - (-1 : ℂ)‖ = ‖1 + w ^ q‖ := by
      rw [show w ^ q - (-1 : ℂ) = 1 + w ^ q by ring]
    rw [h2, hpowx] at h
    simp only [norm_neg, norm_one] at h
    linarith
  have hxclose : |x - 1| ≤ 8 * K / (q : ℝ) :=
    abs_sub_one_le_of_pow_close hq hxpos hK hmod hxq
  -- phase
  have hwq : w ^ q = ((x ^ q : ℝ) : ℂ) * Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I) := by
    have h1 : ((((q : ℝ) * φ : ℝ)) : ℂ) * Complex.I = (q : ℂ) * (((φ : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h1, Complex.exp_nat_mul]
    conv_lhs => rw [← hwrep]
    rw [mul_pow]
    push_cast
    ring
  have hunit : ‖1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I)‖ ≤ 2 * K := by
    have h1 : ‖(1 + w ^ q) - (1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I))‖
        = |x ^ q - 1| := by
      rw [show (1 + w ^ q) - (1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I))
          = w ^ q - Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I) by ring, hwq,
        show ((x ^ q : ℝ) : ℂ) * Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I)
            - Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I)
          = ((x ^ q - 1 : ℝ) : ℂ) * Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I) by
          push_cast; ring,
        norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    have h2 := norm_sub_norm_le (1 + w ^ q)
      (1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I))
    have h3 : ‖1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I)‖ - ‖1 + w ^ q‖
        ≤ |x ^ q - 1| := by
      have h4 := norm_sub_norm_le (1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I))
        (1 + w ^ q)
      have h5 : ‖(1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I)) - (1 + w ^ q)‖
          = |x ^ q - 1| := by
        rw [← h1, norm_sub_rev]
      linarith [h4, h5.le, h5.ge]
    linarith
  -- reduce the phase modulo `2π`
  set δ₀ : ℝ := (q : ℝ) * φ - Real.pi with hδ₀
  obtain ⟨k, hk⟩ : ∃ k : ℤ, |δ₀ / (2 * Real.pi) - (k : ℝ)| ≤ 1/2 :=
    ⟨round (δ₀ / (2 * Real.pi)), abs_sub_round _⟩
  set δ : ℝ := δ₀ - 2 * Real.pi * (k : ℝ) with hδ
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδπ : |δ| ≤ Real.pi := by
    have hrw : δ = 2 * Real.pi * (δ₀ / (2 * Real.pi) - (k : ℝ)) := by
      rw [hδ]; field_simp
    rw [hrw, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    nlinarith [hk, abs_nonneg (δ₀ / (2 * Real.pi) - (k : ℝ))]
  have hexpδ : Complex.exp ((δ : ℝ) * Complex.I)
      = -Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I) := by
    have hsplit : ((δ : ℝ) : ℂ) * Complex.I
        = (((q : ℝ) * φ : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I * (-1)
          + (k : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [hδ, hδ₀]
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_add]
    have h1 : Complex.exp ((Real.pi : ℂ) * Complex.I * (-1)) = -1 := by
      rw [show (Real.pi : ℂ) * Complex.I * (-1) = -((Real.pi : ℂ) * Complex.I) by ring,
        Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have h2 : Complex.exp ((k : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
      rw [show (k : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I))
          = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h1, h2]
    ring
  have hδsmall : ‖Complex.exp ((δ : ℝ) * Complex.I) - 1‖ ≤ 2 * K := by
    rw [hexpδ]
    rw [show -Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I) - 1
        = -(1 + Complex.exp (((q : ℝ) * φ : ℝ) * Complex.I)) by ring, norm_neg]
    exact hunit
  have hδbound : |δ| ≤ (Real.pi / 2) * (2 * K) :=
    abs_le_of_norm_exp_sub_one_le hδπ (by linarith) hδsmall
  -- the model index
  refine ⟨(k % (q : ℤ)).toNat, ?_, ?_⟩
  · have hqz : ((q : ℤ)) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have h1 : (0:ℤ) ≤ k % (q : ℤ) := Int.emod_nonneg k hqz
    have h2 : k % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos k (by exact_mod_cast hqnat)
    omega
  · -- the model phase equals `exp (i ((2k+1)π/q))`
    set l : ℕ := (k % (q : ℤ)).toNat with hl
    have hlk : ∃ t : ℤ, (k : ℝ) = (l : ℝ) + (q : ℝ) * (t : ℝ) := by
      refine ⟨k / (q : ℤ), ?_⟩
      have hqz : ((q : ℤ)) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      have h1 : (0:ℤ) ≤ k % (q : ℤ) := Int.emod_nonneg k hqz
      have h2 : ((l : ℤ) : ℝ) = ((k % (q : ℤ) : ℤ) : ℝ) := by
        rw [hl]
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h1)
      have h3 : k = k % (q : ℤ) + (q : ℤ) * (k / (q : ℤ)) := by
        have hdm : k % (q : ℤ) + (q : ℤ) * (k / (q : ℤ)) = k := Int.emod_add_mul_ediv k (q : ℤ)
        linarith
      have h4 : (k : ℝ) = ((k % (q : ℤ) : ℤ) : ℝ) + (q : ℝ) * ((k / (q : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h3
      rw [h4, ← h2]
      push_cast
      ring
    obtain ⟨t, ht⟩ := hlk
    have hphase_eq : Complex.exp (((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ) : ℝ) * Complex.I)
        = Complex.exp ((((2 * (k : ℝ) + 1) * Real.pi / (q : ℝ)) : ℝ) * Complex.I) := by
      have hsplit : (((2 * (k : ℝ) + 1) * Real.pi / (q : ℝ) : ℝ) : ℂ) * Complex.I
          = (((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ) : ℝ) : ℂ) * Complex.I
            + (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        have hqC : ((q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [ht]
        push_cast
        field_simp
        ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hphase_eq]
    -- assemble
    set θk : ℝ := (2 * (k : ℝ) + 1) * Real.pi / (q : ℝ) with hθk
    have hφθ : |φ - θk| = |δ| / (q : ℝ) := by
      have hrw : φ - θk = δ / (q : ℝ) := by
        rw [hθk, hδ, hδ₀]
        field_simp
        ring
      rw [hrw, abs_div, abs_of_pos hqpos]
    have hsplitnorm : w - Complex.exp ((θk : ℝ) * Complex.I)
        = ((x - 1 : ℝ) : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)
          + (Complex.exp ((φ : ℝ) * Complex.I) - Complex.exp ((θk : ℝ) * Complex.I)) := by
      rw [← hwrep]
      push_cast
      ring
    have hterm1 : ‖((x - 1 : ℝ) : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖ = |x - 1| := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    have hterm2 : ‖Complex.exp ((φ : ℝ) * Complex.I) - Complex.exp ((θk : ℝ) * Complex.I)‖
        ≤ 2 * |φ - θk| := by
      have hfac : Complex.exp ((φ : ℝ) * Complex.I) - Complex.exp ((θk : ℝ) * Complex.I)
          = Complex.exp ((θk : ℝ) * Complex.I)
            * (Complex.exp (((φ - θk : ℝ) : ℝ) * Complex.I) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      have hz : ‖((φ - θk : ℝ) : ℂ) * Complex.I‖ = |φ - θk| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hle1 : ‖((φ - θk : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
        rw [hz, hφθ, div_le_one hqpos]
        nlinarith [hδbound, Real.pi_le_four, hK4, hK, hqR]
      have hb := Complex.norm_exp_sub_one_le hle1
      rw [hz] at hb
      rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact hb
    have hfinal : |x - 1| + 2 * |φ - θk| ≤ 16 * K / (q : ℝ) := by
      rw [hφθ]
      have h2 : 2 * |δ| ≤ 8 * K := by nlinarith [hδbound, Real.pi_le_four, hK]
      have h4 : (2 * |δ|) / (q : ℝ) ≤ (8 * K) / (q : ℝ) :=
        (div_le_div_iff_of_pos_right hqpos).2 h2
      have h5 : 2 * (|δ| / (q : ℝ)) = (2 * |δ|) / (q : ℝ) := by ring
      have h6 : 8 * K / (q : ℝ) + 8 * K / (q : ℝ) = 16 * K / (q : ℝ) := by ring
      linarith [hxclose]
    calc ‖w - Complex.exp ((θk : ℝ) * Complex.I)‖
        ≤ ‖((x - 1 : ℝ) : ℂ) * Complex.exp ((φ : ℝ) * Complex.I)‖
          + ‖Complex.exp ((φ : ℝ) * Complex.I) - Complex.exp ((θk : ℝ) * Complex.I)‖ := by
          rw [hsplitnorm]; exact norm_add_le _ _
      _ ≤ |x - 1| + 2 * |φ - θk| := by rw [hterm1]; linarith [hterm2]
      _ ≤ 16 * K / (q : ℝ) := hfinal

end SparseFock
