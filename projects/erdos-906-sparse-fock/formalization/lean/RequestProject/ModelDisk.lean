import RequestProject.Crossing
import RequestProject.Numeric
import RequestProject.IndexSelect
import RequestProject.ZeroCount32

/-!
# Model disks and the exact local zero count for `p = 3/2`

This file introduces the model data of the manuscript,

`z_{j,ℓ} = ρ_j exp((2ℓ+1)π i / q_j)`,  `D(z_{j,ℓ}, c ρ_j / q_j)`,

and proves the `p = 3/2` case of Proposition 3.2 ("Rouché transfer") in the sharp form:
for every fixed annulus there are a constant `c > 0` and a threshold `N` such that for
all `n ≥ N` and every admissible crossing index `j` (i.e. `a ≤ ρ_j ≤ b`) each model disk
`D(z_{j,ℓ}, c ρ_j / q_j)` contains **exactly one** zero of `F_{3/2}^{(n)}`, and that zero
is **simple**.  In particular the total multiplicity of the zeros of `F_{3/2}^{(n)}` in
the disk is exactly one.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-! ### The model data -/

/-- The model center `z_{j,ℓ} = ρ_j exp((2ℓ+1)π i / q_j)` (equation (2.10) of the paper). -/
noncomputable def modelCenter (n j l : ℕ) : ℂ :=
  (rho (3/2) n j : ℂ) *
    Complex.exp (((2 * (l : ℝ) + 1) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ) : ℝ) * Complex.I)

/-- The model disk radius `c ρ_j / q_j`. -/
noncomputable def modelRadius (c : ℝ) (n j : ℕ) : ℝ :=
  c * rho (3/2) n j / ((qgap (3/2) j : ℕ) : ℝ)

/-- The model disk `D(z_{j,ℓ}, c ρ_j / q_j)`, taken closed. -/
noncomputable def modelDisk (c : ℝ) (n j l : ℕ) : Set ℂ :=
  Metric.closedBall (modelCenter n j l) (modelRadius c n j)

/-- The model phases are the odd `q`-th roots of `-1`. -/
theorem modelPhase_pow {q : ℕ} (hq : 1 ≤ q) (l : ℕ) :
    (Complex.exp ((((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ) : ℝ)) * Complex.I)) ^ q = -1 := by
  have hq0 : ((q : ℝ)) ≠ 0 := by
    have : 0 < q := hq
    positivity
  have hqC : ((q : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).2 (by omega : q ≠ 0)
  rw [← Complex.exp_nat_mul]
  have hstep : (q : ℂ) * ((((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ) : ℝ)) * Complex.I)
      = ((2 * l + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [hstep, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  exact Odd.neg_one_pow ⟨l, by ring⟩

theorem modelRadius_pos {c : ℝ} (hc : 0 < c) {n j : ℕ} (hj : 1 ≤ j) :
    0 < modelRadius c n j := by
  have hq : 1 ≤ qgap (3/2) j := one_le_qgap (by norm_num) hj
  have hqR : (0:ℝ) < ((qgap (3/2) j : ℕ) : ℝ) := by exact_mod_cast hq
  have := rho_pos (3/2) n j
  unfold modelRadius
  positivity

/-! ### The local numerical data at an admissible crossing index -/

set_option maxHeartbeats 1000000 in
/-- All size relations needed at an admissible crossing index `j` (that is, one with
`a ≤ ρ_j ≤ b`), packaged in terms of the auxiliary variable `v = ⁴√j`.  This is the part
of the proof of `annular_covering_rate_p32` that depends only on `j`, extracted so that it
can be reused for the zero-counting statements. -/
theorem p32_local_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (W : ℝ) :
    ∃ N : ℕ, ∀ n j : ℕ, N ≤ n → 1 ≤ j → n ≤ nu (3/2) j →
      a ≤ rho (3/2) n (j + 1) → rho (3/2) n j ≤ b →
      ∃ v : ℝ, W ≤ v ∧ 3 ≤ v ∧ (n : ℝ) ≤ v ^ 6 ∧ v ^ 6 / 2 ≤ (n : ℝ) ∧ 2 ≤ j ∧
        (a/3) * v ^ 3 ≤ ((mOf (3/2) n j : ℕ) : ℝ) ∧
        ((mOf (3/2) n j : ℕ) : ℝ) ≤ 2 * b * v ^ 3 ∧
        v ^ 2 ≤ ((qgap (3/2) j : ℕ) : ℝ) ∧
        ((qgap (3/2) j : ℕ) : ℝ) ≤ 2 * v ^ 2 ∧
        ((qgap (3/2) (j + 1) : ℕ) : ℝ) ≤ 2 * v ^ 2 ∧
        v ^ 2 ≤ ((min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) : ℕ) : ℝ) ∧
        v ^ 2 ≤ ((qgap (3/2) (j + 2) : ℕ) : ℝ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨N₂, hN₂⟩ := exists_threshold_pow_six (max W 0 + 3 + (4*b+8) + b + 12/a)
  refine ⟨N₂, fun n j hn hj1 hjn hja hjb => ?_⟩
  obtain ⟨v, hv0, hv2, hv4⟩ := exists_quartic_root j
  have hnv6 : (n : ℝ) ≤ v ^ 6 := by
    have h1 : ((nu (3/2) j : ℕ) : ℝ) ≤ (j : ℝ) * Real.sqrt j := nu32_le j
    have h2 : (n : ℝ) ≤ ((nu (3/2) j : ℕ) : ℝ) := by exact_mod_cast hjn
    have h3 : (j : ℝ) * Real.sqrt j = v ^ 6 := by
      rw [← hv2, ← hv4]; ring
    linarith
  have hVv := hN₂ n hn v hv0 hnv6
  have hbpos : (0:ℝ) < 4*b + 8 := by positivity
  have hapos : (0:ℝ) < 12/a := by positivity
  have hW0 : (0:ℝ) ≤ max W 0 := le_max_right _ _
  have hWle : W ≤ max W 0 := le_max_left _ _
  have hW : W ≤ v := by linarith
  have hv3 : (3:ℝ) ≤ v := by linarith
  have hv4b8 : 4*b + 8 ≤ v := by linarith
  have hvb : b ≤ v := by linarith
  have hva : 12/a ≤ v := by linarith
  have hvpos : (0:ℝ) < v := by linarith
  have hv29 : (9:ℝ) ≤ v ^ 2 := by nlinarith
  have hvv3 : v ≤ v ^ 3 := by nlinarith
  have hjR : (j : ℝ) = v ^ 4 := hv4.symm
  have hj2 : 2 ≤ j := by
    have h81 : (81:ℝ) ≤ (j : ℝ) := by rw [hjR]; nlinarith
    have : (2:ℝ) ≤ (j : ℝ) := by linarith
    exact_mod_cast this
  have hsqn : Real.sqrt n ≤ v ^ 3 := by
    have h1 : (n : ℝ) ≤ (v ^ 3) ^ 2 := by nlinarith
    calc Real.sqrt n ≤ Real.sqrt ((v ^ 3) ^ 2) := Real.sqrt_le_sqrt h1
      _ = v ^ 3 := Real.sqrt_sq (by positivity)
  have hm2 : ((mOf (3/2) n j : ℕ) : ℝ) ≤ 2*b*v^3 := by
    have h1 := mOf_add_one_le_of_rho_le hj1 hjn hb hjb
    have h2 : b * Real.sqrt n ≤ b * v ^ 3 := mul_le_mul_of_nonneg_left hsqn hb.le
    have h3 : b ^ 2 ≤ b * v ^ 3 := by nlinarith
    linarith
  have hnlow : v ^ 6 / 2 ≤ (n : ℝ) := by
    have h1 : (j : ℝ) * Real.sqrt j - 1 ≤ ((nu (3/2) j : ℕ) : ℝ) := le_nu32 j
    have h3 : (j : ℝ) * Real.sqrt j = v ^ 6 := by rw [← hv2, ← hv4]; ring
    have h4 : ((nu (3/2) j : ℕ) : ℝ) = (n : ℝ) + ((mOf (3/2) n j : ℕ) : ℝ) := by
      have := nu_eq_add_mOf hjn
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) this
    have h5 : v ^ 3 * (4*b + 8) ≤ v ^ 3 * v ^ 3 :=
      mul_le_mul_of_nonneg_left (le_trans hv4b8 hvv3) (by positivity)
    have h6 : (1:ℝ) ≤ v ^ 3 := by nlinarith
    rw [h3, h4] at h1
    nlinarith
  have hsqnlow : v ^ 3 / (3/2) ≤ Real.sqrt n := by
    refine Real.le_sqrt_of_sq_le ?_
    have h0 : (0:ℝ) ≤ v ^ 6 := by positivity
    nlinarith
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
    nlinarith
  have hq_low : v ^ 2 ≤ ((qgap (3/2) j : ℕ) : ℝ) := by
    have h := le_qgap32 hj1
    rw [hsqrtj] at h
    nlinarith
  have hq_up : ((qgap (3/2) j : ℕ) : ℝ) ≤ 2 * v ^ 2 := by
    have h := qgap32_le hj1
    rw [hsqrtj] at h
    nlinarith
  have hqp_up : ((qgap (3/2) (j + 1) : ℕ) : ℝ) ≤ 2 * v ^ 2 := by
    have h := qgap32_le hj1'
    nlinarith
  have hQ : v ^ 2 ≤ ((min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) : ℕ) : ℝ) := by
    have hA : v ^ 2 ≤ ((qgap (3/2) (j - 1) : ℕ) : ℝ) := by
      have h := le_qgap32 hjm1
      nlinarith
    have hB : v ^ 2 ≤ ((qgap (3/2) (j + 1) : ℕ) : ℝ) := by
      have h := le_qgap32 hj1'
      nlinarith
    rw [Nat.cast_min]
    exact le_min hA hB
  have hva' : 12 ≤ a * v := by
    have h := (div_le_iff₀ ha).1 hva
    linarith [mul_comm a v]
  have hmsucc : mOf (3/2) n (j + 1) = mOf (3/2) n j + qgap (3/2) j :=
    mOf_succ (by norm_num) hj1 hjn
  have hja' : a ≤ rho (3/2) n (j + 1) := hja
  have hsqrtjp2 : v ^ 2 ≤ Real.sqrt ((j + 2 : ℕ) : ℝ) := by
    rw [← hsqrtj]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    linarith
  have hQ2 : v ^ 2 ≤ ((qgap (3/2) (j + 2) : ℕ) : ℝ) := by
    have h := le_qgap32 (show 1 ≤ j + 2 by omega)
    nlinarith
  have hm1 : (a/3) * v^3 ≤ ((mOf (3/2) n j : ℕ) : ℝ) := by
    have h := le_mOf_add_qgap hj1 hjn ha hja'
    rw [hmsucc] at h
    push_cast at h
    have hav : a * (v ^ 3 / (3/2)) ≤ a * Real.sqrt n :=
      mul_le_mul_of_nonneg_left hsqnlow ha.le
    nlinarith [hq_up, hqp_up, hvpos,
      mul_nonneg (sq_nonneg v) (by linarith : (0:ℝ) ≤ a * v - 12)]
  exact ⟨v, hW, hv3, hnv6, hnlow, hj2, hm1, hm2, hq_low, hq_up, hqp_up, hQ, hQ2⟩

/-! ### Exactly one zero in each model disk -/

set_option maxHeartbeats 1000000 in
/-- **Exactly one zero, counted with multiplicity, in each model disk** (`p = 3/2`).
For every compact annulus `a ≤ |z| ≤ b` with `0 < a ≤ b` there are a constant `c > 0` and
a threshold `N` such that for all `n ≥ N`, every crossing index `j` with `a ≤ ρ_j ≤ b`
and every `ℓ`, the closed model disk `D(z_{j,ℓ}, c ρ_j / q_j)` contains exactly one zero
of `F_{3/2}^{(n)}`, and that zero is simple.  Hence the total multiplicity of the zeros of
`F_{3/2}^{(n)}` in the disk equals one. -/
theorem model_disk_zero_count_one_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
      1 ≤ j → n ≤ nu (3/2) j → a ≤ rho (3/2) n j → rho (3/2) n j ≤ b → ∀ l : ℕ,
        (∃! z : ℂ, z ∈ modelDisk c n j l ∧ iteratedDeriv n (F (3/2)) z = 0) ∧
        (∀ z ∈ modelDisk c n j l, iteratedDeriv n (F (3/2)) z = 0 →
          deriv (iteratedDeriv n (F (3/2))) z ≠ 0) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨c₀, hc₀pos, hc₀half, hc₀b⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1/2 ∧ c₀ ≤ 1/(256*b^2) :=
    ⟨min (1/2) (1/(256*b^2)), lt_min (by norm_num) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  refine ⟨c₀ / 4, by positivity, by linarith, ?_⟩
  obtain ⟨V₁, hV₁3, hV₁⟩ := numeric_core ha hab (η := 1) one_pos hc₀pos hc₀half hc₀b
  obtain ⟨V₂, hV₂3, hV₂⟩ := numeric_core ha hab (η := 1) one_pos
    (c₀ := c₀ / 8) (by positivity) (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := p32_local_bounds ha hab (max V₁ V₂ + 6 / (a * c₀))
  refine ⟨N, fun n hn j hj1 hjn hja hjb l => ?_⟩
  obtain ⟨v, hW, hv3, hnv6, hnlow, hj2, hm1, hm2, hq_low, hq_up, hqp_up, hQ, hQ2⟩ :=
    hN n j hn hj1 hjn (le_trans hja (rho_lt_rho_succ (by norm_num) hj1 hjn).le) hjb
  have hvpos : (0:ℝ) < v := by linarith
  have hV₁v : V₁ ≤ v := le_trans (le_trans (le_max_left _ _) (by
    have : (0:ℝ) < 6 / (a * c₀) := by positivity
    linarith)) hW
  have hV₂v : V₂ ≤ v := le_trans (le_trans (le_max_right _ _) (by
    have : (0:ℝ) < 6 / (a * c₀) := by positivity
    linarith)) hW
  have hvbig : 6 / (a * c₀) ≤ v := by
    have h1 : (0:ℝ) ≤ max V₁ V₂ := le_trans (by linarith) (le_max_left V₁ V₂)
    linarith
  -- abbreviations
  set m : ℕ := mOf (3/2) n j with hmdef
  set q : ℕ := qgap (3/2) j with hqdef
  set Q : ℕ := min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) with hQdef
  set ρ : ℝ := rho (3/2) n j with hρdef
  have hρpos : 0 < ρ := rho_pos _ _ _
  have hqNat : 1 ≤ q := one_le_qgap (by norm_num) hj1
  have hqR : (0:ℝ) < (q : ℝ) := by exact_mod_cast hqNat
  have hq1R : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNat
  -- the numerical core, twice
  obtain ⟨hnum1, hnum2, hnum3, hnum4, -⟩ :=
    hV₁ v hV₁v ((m : ℕ) : ℝ) ((q : ℕ) : ℝ) ((Q : ℕ) : ℝ) hm1 hm2 hq_low hq_up hQ
  obtain ⟨hnum1', hnum2', -, -, -⟩ :=
    hV₂ v hV₂v ((m : ℕ) : ℝ) ((q : ℕ) : ℝ) ((Q : ℕ) : ℝ) hm1 hm2 hq_low hq_up hQ
  -- the slopes
  have hsmallN : m + q + 2 ≤ n := by
    have h : ((m + q + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast h
  obtain ⟨hL, hR⟩ := crossing_slopes32 hj1 hjn hsmallN
  have hcl : 1/(32*b*v) ≤ dstep n ρ m := le_trans hnum3 hL
  have hcr : dstep n ρ (m + q - 1) ≤ -(1/(32*b*v)) := le_trans hR (by linarith)
  -- the model phase
  set θ : ℝ := (2 * (l : ℝ) + 1) * Real.pi / ((q : ℕ) : ℝ) with hθdef
  have hphase : (Complex.exp ((θ : ℝ) * Complex.I)) ^ q = -1 := modelPhase_pow hqNat l
  have hcenter : modelCenter n j l = (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) := rfl
  -- the disk radius
  set s : ℝ := c₀ / (4 * (q : ℝ)) with hsdef
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hradius : modelRadius (c₀/4) n j = ρ * s := by
    have hqne : ((q : ℕ) : ℝ) ≠ 0 := ne_of_gt hqR
    rw [modelRadius, hsdef, ← hρdef, ← hqdef]
    field_simp
  have hqs : (q : ℝ) * s ≤ 1/8 := by
    rw [hsdef]
    rw [show (q:ℝ) * (c₀ / (4 * (q:ℝ))) = c₀ / 4 by field_simp]
    linarith
  have h4s : 4 * s = c₀ / (q : ℝ) := by
    rw [hsdef]; field_simp
  -- existence
  have hex : ∃ z : ℂ, iteratedDeriv n (F (3/2)) z = 0 ∧
      ‖z - (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ ≤ 2 * ρ * ((c₀/8) / (q:ℝ)) :=
    exists_zero_near_model (p := 3/2) (n := n) (m₀ := m) (q := q) (Q := Q)
      (ρ := ρ) (c := 1/(32*b*v)) (c₀ := c₀/8) (θ := θ)
      hρpos hqNat hphase (isSupp_mOf hj1 hjn) (crossing_dcoeff hj1 hjn) (crossing_Phi hj1 hjn)
      hcl hcr (fun mm hmm h1 h2 => supp_gap hj2 hjn hmm h1 h2) (by positivity) (by linarith)
      hnum1' hnum2'
  have hexrad : 2 * ρ * ((c₀/8) / (q:ℝ)) = ρ * s := by
    rw [hsdef]; field_simp; ring
  rw [hexrad] at hex
  -- uniqueness and simplicity
  set K : ℝ := Real.exp (-(1/(32*b*v) - c₀/(q:ℝ)) * (Q:ℝ)) *
      (((m : ℝ) + 1) + Real.exp ((q:ℝ) * (c₀/(q:ℝ)))
        / (1 - Real.exp (-(1/(32*b*v) - c₀/(q:ℝ))))) with hKdef
  have hden : 0 < 1 - Real.exp (-(1/(32*b*v) - c₀/(q:ℝ))) := by
    have : Real.exp (-(1/(32*b*v) - c₀/(q:ℝ))) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  -- the key smallness `K < q s / 2`
  have hmγ : 1 ≤ (m : ℝ) * (c₀ / (q:ℝ)) := by
    have h1 : (a/3) * v ^ 3 * (c₀ / (2 * v^2)) ≤ (m : ℝ) * (c₀ / (q:ℝ)) := by
      have hfrac : c₀ / (2 * v^2) ≤ c₀ / (q:ℝ) :=
        div_le_div_of_nonneg_left hc₀pos.le hqR (by linarith)
      have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
      have h2 : (a/3) * v ^ 3 * (c₀ / (2 * v^2)) ≤ (m:ℝ) * (c₀ / (2*v^2)) :=
        mul_le_mul_of_nonneg_right hm1 (by positivity)
      have h3 : (m:ℝ) * (c₀ / (2*v^2)) ≤ (m:ℝ) * (c₀/(q:ℝ)) :=
        mul_le_mul_of_nonneg_left hfrac hmnn
      linarith
    have h4 : (a/3) * v ^ 3 * (c₀ / (2 * v^2)) = a * c₀ * v / 6 := by
      field_simp; ring
    have h5 : 6 / (a * c₀) ≤ v := hvbig
    have h6 : (6:ℝ) ≤ a * c₀ * v := by
      rw [div_le_iff₀ (by positivity)] at h5
      linarith
    linarith [h1, h4.le, h4.ge]
  have hexp2 : (2:ℝ) ≤ Real.exp ((m : ℝ) * (c₀ / (q:ℝ))) := by
    have h1 : Real.exp 1 ≤ Real.exp ((m : ℝ) * (c₀ / (q:ℝ))) := Real.exp_le_exp.2 hmγ
    have h2 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    linarith
  have hKs : K < (q:ℝ) * s / 2 := by
    have h1 : Real.exp ((m : ℝ) * (c₀/(q:ℝ))) * K < c₀ / 4 := hnum2
    have h2 : 2 * K ≤ Real.exp ((m : ℝ) * (c₀/(q:ℝ))) * K :=
      mul_le_mul_of_nonneg_right hexp2 hKnn
    have h3 : (q:ℝ) * s / 2 = c₀ / 8 := by
      rw [hsdef]; field_simp; ring
    rw [h3]
    linarith
  have htail : ∀ σ : ℝ, |σ| ≤ 4 * s →
      ∑' mm : ℕ, (if mm = m ∨ mm = m + q then 0
        else dcoeff (3/2) n mm * (ρ * Real.exp σ) ^ mm)
        ≤ Real.exp (Phi n ρ m + (m : ℝ) * σ) * K := by
    intro σ hσ
    rw [h4s] at hσ
    have h := tail_sum_bound (p := 3/2) (n := n) (m₀ := m) (q := q) (Q := Q)
      (ρ := ρ) (σ := σ) (c := 1/(32*b*v)) (γ := c₀/(q:ℝ)) hρpos hqNat hσ hnum1
      (crossing_Phi hj1 hjn) hcl hcr (fun mm hmm h1 h2 => supp_gap hj2 hjn hmm h1 h2)
    refine le_trans h (le_of_eq ?_)
    rw [hKdef]
    ring
  obtain ⟨huniq, hsimple⟩ := unique_zero_near_model (p := 3/2) (n := n) (m₀ := m) (q := q)
    (ρ := ρ) (θ := θ) (s := s) (K := K)
    hρpos hqNat hphase (isSupp_mOf hj1 hjn) (crossing_dcoeff hj1 hjn)
    hspos hqs hKnn htail hKs
  -- assemble
  obtain ⟨z, hz0, hzd⟩ := hex
  constructor
  · refine ⟨z, ⟨?_, hz0⟩, ?_⟩
    · rw [modelDisk, Metric.mem_closedBall, dist_eq_norm, hcenter, hradius]
      exact hzd
    · rintro y ⟨hy1, hy2⟩
      have hy1' : ‖y - (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ ≤ ρ * s := by
        rw [modelDisk, Metric.mem_closedBall, dist_eq_norm, hcenter, hradius] at hy1
        exact hy1
      exact huniq y z hy1' hzd hy2 hz0
  · intro y hy hy0
    have hy1' : ‖y - (ρ : ℂ) * Complex.exp ((θ : ℝ) * Complex.I)‖ ≤ ρ * s := by
      rw [modelDisk, Metric.mem_closedBall, dist_eq_norm, hcenter, hradius] at hy
      exact hy
    exact hsimple y hy1' hy0

end SparseFock
