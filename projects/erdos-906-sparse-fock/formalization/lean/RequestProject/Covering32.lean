import RequestProject.Crossing
import RequestProject.Numeric
import RequestProject.Phase
import RequestProject.IndexSelect

/-!
# The annular covering theorem for `p = 3/2`

The covering proof combines the tail domination (`Tail.lean`) with the two-term localisation
(`TwoTerm.lean`) and the arithmetic of the support `ν_j = ⌊j^{3/2}⌋` into the
quantitative annular covering statement: on every compact annulus
`{a ≤ |z| ≤ b}` with `0 < a ≤ b`, the zero set of `F_{3/2}^{(n)}` becomes
`η`-dense for all sufficiently large `n`.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- The real sixth root of a sixth power. -/
theorem rpow_one_sixth_pow_six {x : ℝ} (hx : 0 ≤ x) : (x ^ 6) ^ ((1:ℝ)/6) = x := by
  rw [← Real.rpow_natCast x 6, ← Real.rpow_mul hx]
  norm_num

/-- Turning `x ≤ v^6` into a bound for the sixth root: `1/v ≤ 1/x^{1/6}`. -/
theorem inv_le_inv_sixthRoot_of_le_pow_six {x v : ℝ} (hx : 0 < x) (hv : 0 < v) (h : x ≤ v^6) :
    1 / v ≤ 1 / (x ^ ((1:ℝ)/6)) := by
  have h1 : x ^ ((1:ℝ)/6) ≤ v := by
    have := Real.rpow_le_rpow hx.le h (by norm_num : (0:ℝ) ≤ 1/6)
    rwa [rpow_one_sixth_pow_six hv.le] at this
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx _) h1

/-- Combining the three geometric error bounds into the explicit rate `C · n^{-1/6}`
with `C = b(2 + 2π + 12/a)`. -/
theorem covering_rate_final {a b c₀ q v X : ℝ} {n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc₀ : 0 < c₀) (hc₀half : c₀ ≤ 1/2) (hv3 : 3 ≤ v) (hq : v^2 ≤ q) (hn : 0 < (n:ℝ))
    (hnv : (n:ℝ) ≤ v^6)
    (hX : X ≤ 2*b*(c₀/q) + 2*Real.pi*b/v^2 + 12*b/(a*v)) :
    X ≤ (b * (2 + 2*Real.pi + 12/a)) / ((n:ℝ) ^ ((1:ℝ)/6)) := by
  have hvpos : (0:ℝ) < v := by linarith
  have hvv2 : v ≤ v ^ 2 := by nlinarith
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le (by positivity) hq
  have hfrac : c₀ / q ≤ 1 / (2*v) := by
    rw [div_le_div_iff₀ hqpos (by positivity)]
    nlinarith
  have h1 : 2 * b * (c₀ / q) ≤ b / v := by
    have hmul := mul_le_mul_of_nonneg_left hfrac (by positivity : (0:ℝ) ≤ 2*b)
    have heq : 2 * b * (1 / (2*v)) = b / v := by field_simp
    linarith
  have h2 : 2 * Real.pi * b / v ^ 2 ≤ 2 * Real.pi * b / v :=
    div_le_div_of_nonneg_left (by positivity) hvpos hvv2
  have h3 : 12 * b / (a * v) = (12 * b / a) / v := by field_simp
  have hsum : X ≤ (b * (2 + 2*Real.pi + 12/a)) / v := by
    have e2 : (b * (2 + 2*Real.pi + 12/a)) / v
        = b/v + (2*Real.pi*b/v + (12*b/a)/v) + b/v := by
      field_simp; ring
    have e3 : (0:ℝ) < b / v := by positivity
    linarith
  have hinv : 1 / v ≤ 1 / ((n : ℝ) ^ ((1:ℝ)/6)) :=
    inv_le_inv_sixthRoot_of_le_pow_six hn hvpos hnv
  have hCpos : (0:ℝ) ≤ b * (2 + 2*Real.pi + 12/a) := by
    have h12 : (0:ℝ) < 12/a := div_pos (by norm_num) ha
    have := Real.pi_pos
    nlinarith
  calc X ≤ (b * (2 + 2*Real.pi + 12/a)) / v := hsum
    _ = (b * (2 + 2*Real.pi + 12/a)) * (1 / v) := by ring
    _ ≤ (b * (2 + 2*Real.pi + 12/a)) * (1 / ((n : ℝ) ^ ((1:ℝ)/6))) :=
        mul_le_mul_of_nonneg_left hinv hCpos
    _ = (b * (2 + 2*Real.pi + 12/a)) / ((n : ℝ) ^ ((1:ℝ)/6)) := by ring

set_option maxHeartbeats 2000000 in
/-- **Quantitative annular covering with the explicit rate `n^{-1/6}`.**  For every
compact annulus `a ≤ |z| ≤ b` with `0 < a ≤ b` there is an explicit constant
`C = b(2 + 2π + 12/a)` such that for all large `n` every point of the annulus lies
within `C · n^{-1/6}` of a zero of `F_{3/2}^{(n)}`. -/
theorem annular_covering_rate_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w : ℂ, a ≤ ‖w‖ → ‖w‖ ≤ b →
        ∃ z : ℂ, iteratedDeriv n (F (3/2)) z = 0 ∧
          ‖z - w‖ ≤ C / ((n : ℝ) ^ ((1 : ℝ) / 6)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h12a : (0:ℝ) < 12 / a := div_pos (by norm_num) ha
  have hCpos : (0:ℝ) < b * (2 + 2*Real.pi + 12/a) := by
    have := Real.pi_pos
    nlinarith
  refine ⟨b * (2 + 2*Real.pi + 12/a), hCpos, ?_⟩
  obtain ⟨c₀, hc₀pos, hc₀half, hc₀b⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1/2 ∧ c₀ ≤ 1/(256*b^2) :=
    ⟨min (1/2) (1/(256*b^2)), lt_min (by norm_num) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨V, hV3, hVspec⟩ := numeric_core ha hab (η := 1) one_pos hc₀pos hc₀half hc₀b
  obtain ⟨N₁, hN₁⟩ := exists_small_crossing ha
  obtain ⟨N₂, hN₂⟩ := exists_threshold_pow_six (V + (4*b+8) + b + 12/a)
  refine ⟨max (max N₁ N₂) 1, fun n hn w hwa hwb => ?_⟩
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnone : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hrpos : 0 < ‖w‖ := lt_of_lt_of_le ha hwa
  obtain ⟨j', hj'1, hj'n, hj'r⟩ := hN₁ n hnN₁
  obtain ⟨j, hj1, hjn, hjr, hjr'⟩ :=
    exists_crossing_index hrpos ⟨j', hj'1, hj'n, le_trans hj'r hwa⟩
  obtain ⟨v, hv0, hv2, hv4⟩ := exists_quartic_root j
  -- `n ≤ v^6`
  have hnv6 : (n : ℝ) ≤ v ^ 6 := by
    have h1 : ((nu (3/2) j : ℕ) : ℝ) ≤ (j : ℝ) * Real.sqrt j := nu32_le j
    have h2 : (n : ℝ) ≤ ((nu (3/2) j : ℕ) : ℝ) := by exact_mod_cast hjn
    have h3 : (j : ℝ) * Real.sqrt j = v ^ 6 := by
      rw [← hv2, ← hv4]
      ring
    linarith
  have hVv := hN₂ n hnN₂ v hv0 hnv6
  have hbpos : (0:ℝ) < 4*b + 8 := by positivity
  have hapos : (0:ℝ) < 12/a := by positivity
  have hvV : V ≤ v := by linarith
  have hv4b8 : 4*b + 8 ≤ v := by linarith
  have hvb : b ≤ v := by linarith
  have hva : 12/a ≤ v := by linarith
  have hv3 : (3:ℝ) ≤ v := le_trans hV3 hvV
  have hvpos : (0:ℝ) < v := by linarith
  have hv29 : (9:ℝ) ≤ v ^ 2 := by nlinarith [hv3, hvpos]
  have hvv3 : v ≤ v ^ 3 := by nlinarith [hv3, hvpos]
  -- `j ≥ 2`
  have hjR : (j : ℝ) = v ^ 4 := hv4.symm
  have hj2 : 2 ≤ j := by
    have h81 : (81:ℝ) ≤ (j : ℝ) := by
      rw [hjR]
      nlinarith [hv29]
    have : (2:ℝ) ≤ (j : ℝ) := by linarith
    exact_mod_cast this
  -- notation
  have hρpos : 0 < rho (3/2) n j := rho_pos _ _ _
  have hρb : rho (3/2) n j ≤ b := le_trans hjr hwb
  -- upper bound for `m`
  have hsqn : Real.sqrt n ≤ v ^ 3 := by
    have h1 : (n : ℝ) ≤ (v ^ 3) ^ 2 := by nlinarith [hnv6]
    calc Real.sqrt n ≤ Real.sqrt ((v ^ 3) ^ 2) := Real.sqrt_le_sqrt h1
      _ = v ^ 3 := Real.sqrt_sq (by positivity)
  have hm2 : ((mOf (3/2) n j : ℕ) : ℝ) ≤ 2*b*v^3 := by
    have h1 := mOf_add_one_le_of_rho_le hj1 hjn hb hρb
    have h2 : b * Real.sqrt n ≤ b * v ^ 3 := mul_le_mul_of_nonneg_left hsqn hb.le
    have h3 : b ^ 2 ≤ b * v ^ 3 := by nlinarith [hvb, hvv3, hb.le]
    linarith
  -- lower bound for `n`
  have hnlow : v ^ 6 / 2 ≤ (n : ℝ) := by
    have h1 : (j : ℝ) * Real.sqrt j - 1 ≤ ((nu (3/2) j : ℕ) : ℝ) := le_nu32 j
    have h3 : (j : ℝ) * Real.sqrt j = v ^ 6 := by
      rw [← hv2, ← hv4]
      ring
    have h4 : ((nu (3/2) j : ℕ) : ℝ) = (n : ℝ) + ((mOf (3/2) n j : ℕ) : ℝ) := by
      have := nu_eq_add_mOf hjn
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) this
    have h5 : v ^ 3 * (4*b + 8) ≤ v ^ 3 * v ^ 3 :=
      mul_le_mul_of_nonneg_left (le_trans hv4b8 hvv3) (by positivity)
    have h6 : (1:ℝ) ≤ v ^ 3 := by nlinarith [hv3, hvpos]
    rw [h3, h4] at h1
    nlinarith [h1, hm2, h5, h6]
  have hsqnlow : v ^ 3 / (3/2) ≤ Real.sqrt n := by
    refine Real.le_sqrt_of_sq_le ?_
    have h0 : (0:ℝ) ≤ v ^ 6 := by positivity
    nlinarith [hnlow, h0]
  -- the gaps
  have hjm1 : (1:ℕ) ≤ j - 1 := by omega
  have hj1' : (1:ℕ) ≤ j + 1 := by omega
  have hsqrtj : Real.sqrt j = v ^ 2 := hv2.symm
  have hsqrtjp : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ v ^ 2 + 1 := by
    have h : ((j + 1 : ℕ) : ℝ) ≤ (v ^ 2 + 1) ^ 2 := by
      push_cast
      rw [hjR]
      nlinarith [sq_nonneg v]
    calc Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ Real.sqrt ((v ^ 2 + 1) ^ 2) := Real.sqrt_le_sqrt h
      _ = v ^ 2 + 1 := Real.sqrt_sq (by positivity)
  have hsqrtjp' : v ^ 2 ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) := by
    rw [← hsqrtj]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    linarith
  have hsqrtjm : v ^ 2 - 1 ≤ Real.sqrt ((j - 1 : ℕ) : ℝ) := by
    have hc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      have h1 : (1:ℕ) ≤ j := hj1
      push_cast [Nat.cast_sub h1]
      ring
    refine Real.le_sqrt_of_sq_le ?_
    rw [hc, hjR]
    nlinarith [hvpos, hv3]
  have hq_low : v ^ 2 ≤ ((qgap (3/2) j : ℕ) : ℝ) := by
    have h := le_qgap32 hj1
    rw [hsqrtj] at h
    nlinarith [hv3, hvpos]
  have hq_up : ((qgap (3/2) j : ℕ) : ℝ) ≤ 2 * v ^ 2 := by
    have h := qgap32_le hj1
    rw [hsqrtj] at h
    nlinarith [hv3, hvpos]
  have hqp_up : ((qgap (3/2) (j + 1) : ℕ) : ℝ) ≤ 2 * v ^ 2 := by
    have h := qgap32_le hj1'
    nlinarith [hsqrtjp, hv3, hvpos]
  have hQ : v ^ 2 ≤ ((min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) : ℕ) : ℝ) := by
    have hA : v ^ 2 ≤ ((qgap (3/2) (j - 1) : ℕ) : ℝ) := by
      have h := le_qgap32 hjm1
      nlinarith [hsqrtjm, hv3, hvpos]
    have hB : v ^ 2 ≤ ((qgap (3/2) (j + 1) : ℕ) : ℝ) := by
      have h := le_qgap32 hj1'
      nlinarith [hsqrtjp', hv3, hvpos]
    rw [Nat.cast_min]
    exact le_min hA hB
  -- lower bound for `m`
  have hmsucc : mOf (3/2) n (j + 1) = mOf (3/2) n j + qgap (3/2) j :=
    mOf_succ (by norm_num) hj1 hjn
  have hva' : 12 ≤ a * v := by
    have h := (div_le_iff₀ ha).1 hva
    linarith [mul_comm a v]
  have hm1 : (a/3) * v^3 ≤ ((mOf (3/2) n j : ℕ) : ℝ) := by
    have h := le_mOf_add_qgap hj1 hjn ha (le_of_lt (lt_of_le_of_lt hwa hjr'))
    rw [hmsucc] at h
    push_cast at h
    have hav : a * (v ^ 3 / (3/2)) ≤ a * Real.sqrt n :=
      mul_le_mul_of_nonneg_left hsqnlow ha.le
    nlinarith [hq_up, hqp_up, hvpos,
      mul_nonneg (sq_nonneg v) (by linarith : (0:ℝ) ≤ a * v - 12)]
  -- the numerical core
  obtain ⟨hnum1, hnum2, hnum3, hnum4, -⟩ :=
    hVspec v hvV ((mOf (3/2) n j : ℕ) : ℝ) ((qgap (3/2) j : ℕ) : ℝ)
      ((min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) : ℕ) : ℝ) hm1 hm2 hq_low hq_up hQ
  have hsmallN : mOf (3/2) n j + qgap (3/2) j + 2 ≤ n := by
    have h : ((mOf (3/2) n j + qgap (3/2) j + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  obtain ⟨hL, hR⟩ := crossing_slopes32 hj1 hjn hsmallN
  have hcl : 1/(32*b*v) ≤ dstep n (rho (3/2) n j) (mOf (3/2) n j) := le_trans hnum3 hL
  have hcr : dstep n (rho (3/2) n j) (mOf (3/2) n j + qgap (3/2) j - 1) ≤ -(1/(32*b*v)) :=
    le_trans hR (by linarith)
  have hqNat : 1 ≤ qgap (3/2) j := one_le_qgap (by norm_num) hj1
  obtain ⟨θ, hphase, hθ⟩ := exists_phase (qgap (3/2) j) hqNat (Complex.arg w)
  obtain ⟨z, hz0, hzd⟩ := exists_zero_near_model (p := 3/2) (n := n)
    (m₀ := mOf (3/2) n j) (q := qgap (3/2) j)
    (Q := min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)))
    (ρ := rho (3/2) n j) (c := 1/(32*b*v)) (c₀ := c₀) (θ := θ)
    hρpos hqNat hphase (isSupp_mOf hj1 hjn) (crossing_dcoeff hj1 hjn) (crossing_Phi hj1 hjn)
    hcl hcr (fun m hm h1 h2 => supp_gap hj2 hjn hm h1 h2) hc₀pos hc₀half hnum1 hnum2
  refine ⟨z, hz0, ?_⟩
  -- the three pieces of the triangle inequality
  have hqR : (0:ℝ) < ((qgap (3/2) j : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hq_low
  have hterm1 : ‖z - (rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖
      ≤ 2 * b * (c₀ / ((qgap (3/2) j : ℕ) : ℝ)) := by
    refine le_trans hzd ?_
    have hnn : (0:ℝ) ≤ c₀ / ((qgap (3/2) j : ℕ) : ℝ) := by positivity
    have : 2 * rho (3/2) n j ≤ 2 * b := by linarith
    exact mul_le_mul_of_nonneg_right this hnn
  have hterm2 : ‖(rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)
      - (rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I)‖
      ≤ 2 * Real.pi * b / v ^ 2 := by
    have hexp : Complex.exp ((Complex.arg w : ℝ) * Complex.I)
        * Complex.exp (((θ - Complex.arg w : ℝ) : ℝ) * Complex.I)
        = Complex.exp ((θ : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hdiff : (rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)
        - (rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I)
        = ((rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I))
          * (Complex.exp (((θ - Complex.arg w : ℝ) : ℝ) * Complex.I) - 1) := by
      rw [mul_sub, mul_one, mul_assoc, hexp]
    have hz1 : ‖((θ - Complex.arg w : ℝ) : ℂ) * Complex.I‖ = |θ - Complex.arg w| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hpiq : Real.pi / ((qgap (3/2) j : ℕ) : ℝ) ≤ Real.pi / v ^ 2 :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hq_low
    have hle1 : ‖((θ - Complex.arg w : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
      rw [hz1]
      have h9 : Real.pi / v ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [Real.pi_le_four, hv3, hvpos]
      linarith [hθ, hpiq]
    have hbound := Complex.norm_exp_sub_one_le hle1
    rw [hz1] at hbound
    rw [hdiff, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    have hstep : rho (3/2) n j * ‖Complex.exp (((θ - Complex.arg w : ℝ) : ℝ) * Complex.I) - 1‖
        ≤ b * (2 * (Real.pi / v ^ 2)) := by
      refine mul_le_mul hρb ?_ (norm_nonneg _) hb.le
      refine le_trans hbound ?_
      have : |θ - Complex.arg w| ≤ Real.pi / v ^ 2 := le_trans hθ hpiq
      linarith
    calc rho (3/2) n j * ‖Complex.exp (((θ - Complex.arg w : ℝ) : ℝ) * Complex.I) - 1‖
        ≤ b * (2 * (Real.pi / v ^ 2)) := hstep
      _ = 2 * Real.pi * b / v ^ 2 := by field_simp
  have hterm3 : ‖(rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I) - w‖
      ≤ 12 * b / (a * v) := by
    have hrepr : (rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I) - w
        = ((rho (3/2) n j - ‖w‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I) := by
      rw [Complex.ofReal_sub, sub_mul, Complex.norm_mul_exp_arg_mul_I]
    rw [hrepr, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith : rho (3/2) n j - ‖w‖ ≤ 0)]
    -- `‖w‖ - ρ_j ≤ ρ_{j+1} - ρ_j`
    have hden : (0:ℝ) < ((mOf (3/2) n j : ℕ) : ℝ) + 1 := by positivity
    have hnum' : ((qgap (3/2) j : ℕ) : ℝ) + ((qgap (3/2) (j + 1) : ℕ) : ℝ) ≤ 4 * v ^ 2 := by
      linarith
    have hfrac : (((qgap (3/2) j : ℕ) : ℝ) + ((qgap (3/2) (j + 1) : ℕ) : ℝ))
        / (((mOf (3/2) n j : ℕ) : ℝ) + 1) ≤ 12 / (a * v) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hnum' (by positivity : (0:ℝ) ≤ a * v), hm1, hvpos]
    have hfrac0 : (0:ℝ) ≤ (((qgap (3/2) j : ℕ) : ℝ) + ((qgap (3/2) (j + 1) : ℕ) : ℝ))
        / (((mOf (3/2) n j : ℕ) : ℝ) + 1) := by positivity
    have hrd := rho_succ_sub_rho_le hj1 hjn
    have hmul : rho (3/2) n j * ((((qgap (3/2) j : ℕ) : ℝ) + ((qgap (3/2) (j + 1) : ℕ) : ℝ))
        / (((mOf (3/2) n j : ℕ) : ℝ) + 1)) ≤ b * (12 / (a * v)) :=
      mul_le_mul hρb hfrac hfrac0 hb.le
    have hfin : b * (12 / (a * v)) = 12 * b / (a * v) := by ring
    linarith [hjr'.le, hrd, hmul, hfin.le, hfin.ge]
  -- assemble
  have htri : ‖z - w‖
      ≤ ‖z - (rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖
        + (‖(rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)
            - (rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I)‖
          + ‖(rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I) - w‖) := by
    calc ‖z - w‖
        = ‖(z - (rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I))
            + (((rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)
                - (rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I))
              + ((rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I)
                - w))‖ := by
          congr 1
          ring
      _ ≤ ‖z - (rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖
            + ‖((rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)
                - (rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I))
              + ((rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I)
                - w)‖ := norm_add_le _ _
      _ ≤ _ := by
          have := norm_add_le
            ((rho (3/2) n j : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)
              - (rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I))
            ((rho (3/2) n j : ℂ) * Complex.exp ((Complex.arg w : ℝ) * Complex.I) - w)
          linarith
  -- the explicit rate
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnone
  exact covering_rate_final ha hb hc₀pos hc₀half hv3 hq_low hnR hnv6
    (by linarith [htri, hterm1, hterm2, hterm3])

/-- **Qualitative annular covering** (derived from the explicit rate).  For every compact
annulus `a ≤ |z| ≤ b` with `0 < a ≤ b` and every `η > 0` there is `N` such that for all
`n ≥ N` the zero set of `F_{3/2}^{(n)}` is `η`-dense in the annulus. -/
theorem annular_covering {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w : ℂ, a ≤ ‖w‖ → ‖w‖ ≤ b →
      ∃ z : ℂ, iteratedDeriv n (F (3/2)) z = 0 ∧ ‖z - w‖ ≤ η := by
  obtain ⟨C, hC, N, hN⟩ := annular_covering_rate_p32 ha hab
  have hCη : (0:ℝ) < C / η := div_pos hC hη
  refine ⟨max N (⌈(C/η)^6⌉₊ + 1), fun n hn w hwa hwb => ?_⟩
  obtain ⟨z, hz0, hzd⟩ := hN n (le_trans (le_max_left _ _) hn) w hwa hwb
  refine ⟨z, hz0, le_trans hzd ?_⟩
  have hceil : ⌈(C/η)^6⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnone : 1 ≤ n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnone
  have hpow : (C/η)^6 ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    have : (⌈(C/η)^6⌉₊ : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hroot : C / η ≤ (n : ℝ) ^ ((1:ℝ)/6) := by
    have h := Real.rpow_le_rpow (by positivity) hpow (by norm_num : (0:ℝ) ≤ 1/6)
    rwa [rpow_one_sixth_pow_six hCη.le] at h
  have hposroot : (0:ℝ) < (n : ℝ) ^ ((1:ℝ)/6) := Real.rpow_pos_of_pos hnR _
  rw [div_le_iff₀ hposroot]
  have := (div_le_iff₀ hη).1 hroot
  linarith [this, mul_comm η ((n : ℝ) ^ ((1:ℝ)/6))]

end SparseFock
