import RequestProject.Simplicity

/-!
# Pairwise disjointness of the model disks (`p = 3/2`)

Section 4 of the round's specification.  For a fixed annulus `a ≤ |z| ≤ b` the model
disks attached to admissible crossing indices are eventually pairwise disjoint:

* **same crossing circle**: the `q_j` model centers are equally spaced with angular gap
  `2π/q_j`, so consecutive centers are at distance `≥ 4 ρ_j / q_j`, while the disks have
  radius `c ρ_j / q_j` with `c ≤ 1`;
* **different crossing circles**: the crossing radii are separated by
  `log ρ_{j+1} - log ρ_j ≥ 1/(2(2B+6) v)` (`Spacing.rho_log_spacing32`), a scale
  `v ≈ n^{1/6}` larger than the disk radius `O(ρ/v²)`.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-! ### Two elementary trigonometric facts -/

/-- `‖e^{ix} - e^{iy}‖ = 2 |sin((x-y)/2)|`. -/
theorem norm_exp_I_sub_exp_I (x y : ℝ) :
    ‖Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I)‖
      = 2 * |Real.sin ((x - y) / 2)| := by
  have h1 : Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I)
      = ((Real.cos x - Real.cos y : ℝ) : ℂ)
        + ((Real.sin x - Real.sin y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [h1, Complex.norm_add_mul_I]
  have habs : (2 * |Real.sin ((x - y) / 2)|) ^ 2 = 4 * Real.sin ((x - y) / 2) ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  have h2 : Real.cos (x - y) = 1 - 2 * Real.sin ((x - y) / 2) ^ 2 := by
    have hd : x - y = 2 * ((x - y) / 2) := by ring
    rw [hd, Real.cos_two_mul]
    have hpy := Real.sin_sq_add_cos_sq ((x - y) / 2)
    have hd2 : 2 * ((x - y) / 2) / 2 = (x - y) / 2 := by ring
    rw [hd2]
    nlinarith [hpy]
  have hexp : Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y :=
    Real.cos_sub x y
  have hs1 := Real.sin_sq_add_cos_sq x
  have hs2 := Real.sin_sq_add_cos_sq y
  have hcos : (Real.cos x - Real.cos y) ^ 2 + (Real.sin x - Real.sin y) ^ 2
      = (2 * |Real.sin ((x - y) / 2)|) ^ 2 := by rw [habs]; nlinarith
  rw [hcos, Real.sqrt_sq (by positivity)]

/-- On `[w, π - w]` the sine is at least `(2/π) w`. -/
theorem sin_lower_of_between {u w : ℝ} (hw : 0 < w) (hwu : w ≤ u)
    (huw : u ≤ Real.pi - w) :
    2 / Real.pi * w ≤ Real.sin u := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases le_or_gt u (Real.pi / 2) with h | h
  · have h1 := Real.mul_le_sin (x := u) (by linarith) h
    have h2 : 2 / Real.pi * w ≤ 2 / Real.pi * u :=
      mul_le_mul_of_nonneg_left hwu (by positivity)
    linarith
  · have hsin : Real.sin u = Real.sin (Real.pi - u) := (Real.sin_pi_sub u).symm
    have h1 := Real.mul_le_sin (x := Real.pi - u) (by linarith) (by linarith)
    have h2 : 2 / Real.pi * w ≤ 2 / Real.pi * (Real.pi - u) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-! ### Geometry of the model centers -/

theorem norm_modelCenter (n j l : ℕ) : ‖modelCenter n j l‖ = rho (3/2) n j := by
  rw [modelCenter, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (rho_pos _ _ _), Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Two distinct model centers on the same crossing circle are at distance at least
`4 ρ_j / q_j`. -/
theorem modelCenter_dist_ge {n j : ℕ} (hq2 : 2 ≤ qgap (3/2) j) {l l' : ℕ}
    (hl : l < qgap (3/2) j) (hl' : l' < qgap (3/2) j) (hne : l ≠ l') :
    4 * rho (3/2) n j / ((qgap (3/2) j : ℕ) : ℝ)
      ≤ dist (modelCenter n j l) (modelCenter n j l') := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hρpos : 0 < rho (3/2) n j := rho_pos _ _ _
  have hqR : (2:ℝ) ≤ ((qgap (3/2) j : ℕ) : ℝ) := by exact_mod_cast hq2
  have hqpos : (0:ℝ) < ((qgap (3/2) j : ℕ) : ℝ) := by linarith
  have key : ∀ u u' : ℕ, u' < u → u < qgap (3/2) j →
      4 * rho (3/2) n j / ((qgap (3/2) j : ℕ) : ℝ)
        ≤ dist (modelCenter n j u) (modelCenter n j u') := by
    intro u u' hlt hu
    have hdiff : modelCenter n j u - modelCenter n j u'
        = (rho (3/2) n j : ℂ) *
          (Complex.exp ((((2 * (u:ℝ) + 1) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ)) : ℝ)
              * Complex.I)
            - Complex.exp ((((2 * (u':ℝ) + 1) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ)) : ℝ)
              * Complex.I)) := by
      rw [modelCenter, modelCenter]; ring
    rw [dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρpos, norm_exp_I_sub_exp_I]
    -- the half angle
    have harg : (((2 * (u:ℝ) + 1) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ))
        - ((2 * (u':ℝ) + 1) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ))) / 2
        = ((u:ℝ) - (u':ℝ)) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ) := by
      field_simp
      ring
    rw [harg]
    -- the sine lower bound
    have hd1 : (1:ℝ) ≤ (u:ℝ) - (u':ℝ) := by
      have : (u' : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast hlt
      linarith
    have hd2 : (u:ℝ) - (u':ℝ) ≤ ((qgap (3/2) j : ℕ) : ℝ) - 1 := by
      have h1 : (u : ℝ) + 1 ≤ ((qgap (3/2) j : ℕ) : ℝ) := by exact_mod_cast hu
      have h2 : (0:ℝ) ≤ (u' : ℝ) := Nat.cast_nonneg _
      linarith
    have hpine : Real.pi ≠ 0 := ne_of_gt hpi
    have hqne : ((qgap (3/2) j : ℕ) : ℝ) ≠ 0 := ne_of_gt hqpos
    have hsin : 2 / ((qgap (3/2) j : ℕ) : ℝ)
        ≤ Real.sin (((u:ℝ) - (u':ℝ)) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ)) := by
      have hbase := sin_lower_of_between
        (u := ((u:ℝ) - (u':ℝ)) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ))
        (w := Real.pi / ((qgap (3/2) j : ℕ) : ℝ))
        (by positivity)
        (by
          refine (div_le_div_iff_of_pos_right hqpos).2 ?_
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (u:ℝ) - (u':ℝ) - 1) hpi.le])
        (by
          have heq3 : Real.pi - Real.pi / ((qgap (3/2) j : ℕ) : ℝ)
              = (((qgap (3/2) j : ℕ) : ℝ) - 1) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ) := by
            field_simp
          rw [heq3]
          refine (div_le_div_iff_of_pos_right hqpos).2 ?_
          nlinarith [mul_nonneg
            (by linarith : (0:ℝ) ≤ (((qgap (3/2) j : ℕ) : ℝ) - 1) - ((u:ℝ) - (u':ℝ)))
            hpi.le])
      have heq : 2 / Real.pi * (Real.pi / ((qgap (3/2) j : ℕ) : ℝ))
          = 2 / ((qgap (3/2) j : ℕ) : ℝ) := by
        field_simp
      rw [heq] at hbase
      exact hbase
    have habs : 2 / ((qgap (3/2) j : ℕ) : ℝ)
        ≤ |Real.sin (((u:ℝ) - (u':ℝ)) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ))| :=
      le_trans hsin (le_abs_self _)
    have hmul : rho (3/2) n j * (2 * (2 / ((qgap (3/2) j : ℕ) : ℝ)))
        ≤ rho (3/2) n j * (2 * |Real.sin (((u:ℝ) - (u':ℝ)) * Real.pi
            / ((qgap (3/2) j : ℕ) : ℝ))|) := by
      have := mul_le_mul_of_nonneg_left habs (by norm_num : (0:ℝ) ≤ 2)
      exact mul_le_mul_of_nonneg_left this hρpos.le
    have heq2 : rho (3/2) n j * (2 * (2 / ((qgap (3/2) j : ℕ) : ℝ)))
        = 4 * rho (3/2) n j / ((qgap (3/2) j : ℕ) : ℝ) := by ring
    rw [heq2] at hmul
    exact hmul
  rcases lt_trichotomy l l' with h | h | h
  · rw [dist_comm]; exact key l' l h hl'
  · exact absurd h hne
  · exact key l l' h hl

/-! ### Monotonicity of the crossing radii -/

theorem rho_mono32 {n j k : ℕ} (hj : 1 ≤ j) (hjn : n ≤ nu (3/2) j) (hjk : j ≤ k) :
    rho (3/2) n j ≤ rho (3/2) n k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
      have hk1 : 1 ≤ k := le_trans hj hk
      have hkn : n ≤ nu (3/2) k := le_trans hjn (nu32_mono hj hk)
      exact le_trans ih (rho_lt_rho_succ (by norm_num) hk1 hkn).le

/-- A point of a model disk has modulus within `modelRadius` of the crossing radius. -/
theorem abs_norm_sub_rho_le {c : ℝ} {n j l : ℕ} {z : ℂ} (hz : z ∈ modelDisk c n j l) :
    |‖z‖ - rho (3/2) n j| ≤ modelRadius c n j := by
  have h : ‖z - modelCenter n j l‖ ≤ modelRadius c n j := by
    rw [← dist_eq_norm]; exact hz
  calc |‖z‖ - rho (3/2) n j| = |‖z‖ - ‖modelCenter n j l‖| := by rw [norm_modelCenter]
    _ ≤ ‖z - modelCenter n j l‖ := abs_norm_sub_norm_le _ _
    _ ≤ modelRadius c n j := h


/-! ### Pairwise disjointness -/

set_option maxHeartbeats 2000000 in
/-- **The relevant model disks are eventually pairwise disjoint** (`p = 3/2`).

For a fixed annulus `a ≤ |z| ≤ b` and a disk constant `0 < c ≤ 1`, all model disks
attached to crossing indices with `a ≤ ρ_j ≤ b` are pairwise disjoint once `n` is
large. -/
theorem model_disks_pairwise_disjoint_p32 {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j j' l l' : ℕ,
      1 ≤ j → n ≤ nu (3/2) j → a ≤ rho (3/2) n j → rho (3/2) n j ≤ b →
      1 ≤ j' → n ≤ nu (3/2) j' → a ≤ rho (3/2) n j' → rho (3/2) n j' ≤ b →
      l < qgap (3/2) j → l' < qgap (3/2) j' → (j ≠ j' ∨ l ≠ l') →
      Disjoint (modelDisk c n j l) (modelDisk c n j' l') := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set B : ℝ := max b 2 with hBdef
  have hB2 : (2:ℝ) ≤ B := le_max_right _ _
  have hbB : b ≤ B := le_max_left _ _
  have hBpos : (0:ℝ) < B := by linarith
  obtain ⟨N, hN⟩ := p32_local_bounds ha hab (10*c*b*(2*B+6)/a + 2*(2*B+6) + 1)
  refine ⟨N, fun n hn j j' l l' hj1 hjn hja hjb hj'1 hj'n hj'a hj'b hl hl' hne => ?_⟩
  -- the radial case, for `i < i'`
  have radial : ∀ i i' u u' : ℕ, 1 ≤ i → n ≤ nu (3/2) i → a ≤ rho (3/2) n i →
      rho (3/2) n i ≤ b → 1 ≤ i' → n ≤ nu (3/2) i' → a ≤ rho (3/2) n i' →
      rho (3/2) n i' ≤ b → i < i' →
      Disjoint (modelDisk c n i u) (modelDisk c n i' u') := by
    intro i i' u u' hi1 hin hia hib hi'1 hi'n hi'a hi'b hii
    obtain ⟨v, hW, hv3, hnv6, hnlow, -, -, hm2, hq_low, hq_up, hqp_up, hQ, -⟩ :=
      hN n i hn hi1 hin (le_trans hia (rho_lt_rho_succ (by norm_num) hi1 hin).le) hib
    obtain ⟨v', -, hv3', hnv6', hnlow', -, -, -, hq'_low, -, -, -, -⟩ :=
      hN n i' hn hi'1 hi'n
        (le_trans hi'a (rho_lt_rho_succ (by norm_num) hi'1 hi'n).le) hi'b
    have hvpos : (0:ℝ) < v := by linarith
    have hv'pos : (0:ℝ) < v' := by linarith
    have hv2 : (0:ℝ) < v ^ 2 := by positivity
    have hρi : 0 < rho (3/2) n i := rho_pos _ _ _
    have hρi' : 0 < rho (3/2) n i' := rho_pos _ _ _
    have hρi1 : 0 < rho (3/2) n (i + 1) := rho_pos _ _ _
    -- `v` and `v'` are comparable
    have hvv' : v / 2 ≤ v' := by
      have h0 : (0:ℝ) ≤ v ^ 6 := by positivity
      have h1 : (v/2) ^ 6 ≤ v' ^ 6 := by
        have he : (v/2) ^ 6 = v ^ 6 / 64 := by ring
        rw [he]; linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) hv'pos.le h1
    have hq'low4 : v ^ 2 / 4 ≤ ((qgap (3/2) i' : ℕ) : ℝ) := by nlinarith
    -- the block length
    have hqplow : v ^ 2 ≤ ((qgap (3/2) (i + 1) : ℕ) : ℝ) := by
      have h := min_le_right (qgap (3/2) (i - 1)) (qgap (3/2) (i + 1))
      have hcast : (((min (qgap (3/2) (i - 1)) (qgap (3/2) (i + 1)) : ℕ)) : ℝ)
          ≤ ((qgap (3/2) (i + 1) : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hTle : ((mOf (3/2) n i : ℕ) : ℝ) + ((qgap (3/2) i : ℕ) : ℝ)
        + ((qgap (3/2) (i + 1) : ℕ) : ℝ) + 2 ≤ (2*B + 6) * v ^ 3 := by
      refine block_length_le (B := B) hv3 ?_ hq_up hqp_up
      nlinarith
    have hTpos : (0:ℝ) < ((mOf (3/2) n i : ℕ) : ℝ) + ((qgap (3/2) i : ℕ) : ℝ)
        + ((qgap (3/2) (i + 1) : ℕ) : ℝ) + 2 := by positivity
    have hone : (1:ℝ) ≤ v := by linarith
    have hvcube : 2 * (2*B + 6) ≤ v := by
      have : (0:ℝ) < 10*c*b*(2*B+6)/a := by positivity
      linarith
    have hv6half : (2*B + 6) * v ^ 3 ≤ v ^ 6 / 2 := by
      have h1 : v ^ 3 * (2*B + 6) ≤ v ^ 3 * (v/2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h3 : v ^ 4 ≤ v ^ 6 := pow_le_pow_right₀ hone (by norm_num)
      nlinarith
    have hsmallN3 : mOf (3/2) n i + qgap (3/2) i + qgap (3/2) (i + 1) + 2 ≤ n := by
      have h : ((mOf (3/2) n i + qgap (3/2) i + qgap (3/2) (i + 1) + 2 : ℕ) : ℝ)
          ≤ (n : ℝ) := by push_cast; linarith
      exact_mod_cast h
    -- the radial spacing
    have hδ : 1/(2*(2*B + 6)*v)
        ≤ Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i) :=
      le_trans (numeric_block_spacing hB2 hv3 hq_low hqplow hTpos hTle)
        (rho_log_spacing32 hi1 hin hsmallN3)
    have hδnn : (0:ℝ) ≤ Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i) := by
      have : (0:ℝ) < 1/(2*(2*B + 6)*v) := by positivity
      linarith
    have hratio : rho (3/2) n (i + 1)
        = rho (3/2) n i
          * Real.exp (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)) := by
      rw [Real.exp_sub, Real.exp_log hρi1, Real.exp_log hρi]
      field_simp
    have hgap : a * (1/(2*(2*B + 6)*v)) ≤ rho (3/2) n (i + 1) - rho (3/2) n i := by
      have hexp : 1 + (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i))
          ≤ Real.exp (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)) := by
        linarith [Real.add_one_le_exp
          (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i))]
      have hmul : rho (3/2) n i
          * (1 + (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)))
          ≤ rho (3/2) n (i + 1) :=
        calc rho (3/2) n i
              * (1 + (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)))
            ≤ rho (3/2) n i
              * Real.exp (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)) :=
              mul_le_mul_of_nonneg_left hexp hρi.le
          _ = rho (3/2) n (i + 1) := hratio.symm
      have hexpand : rho (3/2) n i
          * (1 + (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)))
          = rho (3/2) n i + rho (3/2) n i
            * (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)) := by ring
      have h1 : a * (1/(2*(2*B + 6)*v))
          ≤ a * (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)) :=
        mul_le_mul_of_nonneg_left hδ ha.le
      have h2 : a * (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i))
          ≤ rho (3/2) n i
            * (Real.log (rho (3/2) n (i + 1)) - Real.log (rho (3/2) n i)) :=
        mul_le_mul_of_nonneg_right hia hδnn
      linarith
    -- the two disk radii
    have hri : modelRadius c n i ≤ c*b/v ^ 2 := by
      rw [modelRadius]
      have hq0 : (0:ℝ) < ((qgap (3/2) i : ℕ) : ℝ) := lt_of_lt_of_le hv2 hq_low
      rw [div_le_div_iff₀ hq0 hv2]
      nlinarith [mul_nonneg (mul_nonneg hc.le (sub_nonneg.2 hib)) (sq_nonneg v),
        mul_nonneg (mul_nonneg hc.le hb.le) (sub_nonneg.2 hq_low)]
    have hri' : modelRadius c n i' ≤ 4*c*b/v ^ 2 := by
      rw [modelRadius]
      have hq0 : (0:ℝ) < ((qgap (3/2) i' : ℕ) : ℝ) := by
        have : (0:ℝ) < v ^ 2 / 4 := by positivity
        linarith
      rw [div_le_div_iff₀ hq0 hv2]
      nlinarith [mul_nonneg (mul_nonneg hc.le (sub_nonneg.2 hi'b)) (sq_nonneg v),
        mul_nonneg (mul_nonneg hc.le hb.le) (sub_nonneg.2 hq'low4)]
    -- the comparison
    have hav : 10*c*b*(2*B + 6) < a * v := by
      have h1 : 10*c*b*(2*B+6)/a + 1 ≤ v := by
        have h0 : (0:ℝ) < 2*(2*B+6) := by positivity
        linarith
      have h2 : 10*c*b*(2*B+6)/a * a = 10*c*b*(2*B+6) := by field_simp
      nlinarith
    have hkey : 5*c*b/v ^ 2 < a * (1/(2*(2*B + 6)*v)) := by
      rw [div_lt_iff₀ hv2]
      have heq : a * (1/(2*(2*B + 6)*v)) * v ^ 2 = a*v/(2*(2*B + 6)) := by
        field_simp
      rw [heq, lt_div_iff₀ (by positivity)]
      nlinarith
    -- conclusion
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 := abs_le.1 (abs_norm_sub_rho_le hz)
    have h2 := abs_le.1 (abs_norm_sub_rho_le hz')
    have hmono : rho (3/2) n (i + 1) ≤ rho (3/2) n i' :=
      rho_mono32 (by omega) (le_trans hin (nu32_mono hi1 (by omega))) (by omega)
    have hsum : c*b/v ^ 2 + 4*c*b/v ^ 2 = 5*c*b/v ^ 2 := by ring
    linarith [h1.2, h2.1, hri, hri', hgap, hkey, hmono]
  rcases Nat.lt_trichotomy j j' with h | h | h
  · exact radial j j' l l' hj1 hjn hja hjb hj'1 hj'n hj'a hj'b h
  · subst h
    have hll : l ≠ l' := by
      rcases hne with h1 | h1
      · exact absurd rfl h1
      · exact h1
    obtain ⟨v, -, hv3, -, -, -, -, -, hq_low, -, -, -, -⟩ :=
      hN n j hn hj1 hjn (le_trans hja (rho_lt_rho_succ (by norm_num) hj1 hjn).le) hjb
    have hq2 : 2 ≤ qgap (3/2) j := by
      have h9 : (9:ℝ) ≤ v ^ 2 := by nlinarith
      have : (2:ℝ) ≤ ((qgap (3/2) j : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hqR : (2:ℝ) ≤ ((qgap (3/2) j : ℕ) : ℝ) := by exact_mod_cast hq2
    have hqpos : (0:ℝ) < ((qgap (3/2) j : ℕ) : ℝ) := by linarith
    have hρpos : 0 < rho (3/2) n j := rho_pos _ _ _
    have hdist := modelCenter_dist_ge (n := n) hq2 hl hl' hll
    refine Metric.closedBall_disjoint_closedBall ?_
    refine lt_of_lt_of_le ?_ hdist
    rw [modelRadius]
    rw [← add_div, div_lt_div_iff₀ hqpos hqpos]
    nlinarith [mul_nonneg (mul_nonneg hρpos.le (sub_nonneg.2 hc1)) hqpos.le]
  · exact (radial j' j l' l hj'1 hj'n hj'a hj'b hj1 hjn hja hjb h).symm

end SparseFock
