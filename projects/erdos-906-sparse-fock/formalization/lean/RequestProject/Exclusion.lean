import RequestProject.Dominant
import RequestProject.ExclusionNum

/-!
# Exclusion of additional zeros on a fixed annulus (`p = 3/2`)

Proposition 3.3 of the manuscript.  Every zero of `F_{3/2}^{(n)}` in a fixed annulus
`a ≤ |z| ≤ b` lies, for all large `n`, in one of the model disks
`D(z_{j,ℓ}, c ρ_j / q_j)` with `a/2 ≤ ρ_j ≤ 2b`.

I follow the manuscript's dichotomy:

* choose the crossing index `j` with `ρ_j ≤ |z| < ρ_{j+1}`;
* if `|z|` is within `c₀ / q_j` (logarithmically) of `ρ_j`, or within `c₀ / q_{j+1}` of
  `ρ_{j+1}`, the two-term model applies and `Transition.zero_in_model_disk_of_transition`
  puts `z` in a model disk;
* otherwise the middle term `T_{j+1}` dominates all the others — the two neighbours by
  the factors `e^{-d_A}`, `e^{-d_B}` and the rest by the block tail bound — and
  `Dominant.no_zero_of_dominant` shows there is no zero at all.

The quantitative input which makes the third case work is the radial spacing lower bound
`Spacing.rho_log_spacing32`.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

set_option maxHeartbeats 1000000 in
/-- **A zero in a transition region lies in a model disk** (`p = 3/2`). -/
theorem transition_zero_p32 {A B c₀ cdisk : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hc₀pos : 0 < c₀) (hc₀half : c₀ ≤ 1/2) (hc₀B : c₀ ≤ 1/(256*B^2)) (hcd : 0 < cdisk) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ J : ℕ, 1 ≤ J → n ≤ nu (3/2) J →
      A ≤ rho (3/2) n (J + 1) → rho (3/2) n J ≤ B →
      ∀ z : ℂ, 0 < ‖z‖ →
        |Real.log (‖z‖ / rho (3/2) n J)| ≤ c₀ / ((qgap (3/2) J : ℕ) : ℝ) →
        iteratedDeriv n (F (3/2)) z = 0 →
        ∃ l : ℕ, l < qgap (3/2) J ∧ z ∈ modelDisk cdisk n J l := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  obtain ⟨V, hV3, hV⟩ := numeric_core hA hAB (η := 1) one_pos hc₀pos hc₀half hc₀B
  obtain ⟨N, hN⟩ := p32_local_bounds hA hAB (max V 0 + 6 / (A * c₀) + 24 / (A * cdisk))
  refine ⟨N, fun n hn J hJ1 hJn hJA hJB z hzpos hσbound hz0 => ?_⟩
  obtain ⟨v, hW, hv3, hnv6, hnlow, hJ2, hm1, hm2, hq_low, hq_up, hqp_up, hQ, hQ2⟩ :=
    hN n J hn hJ1 hJn hJA hJB
  have hvpos : (0:ℝ) < v := by linarith
  have hp1 : (0:ℝ) < 6 / (A * c₀) := by positivity
  have hp2 : (0:ℝ) < 24 / (A * cdisk) := by positivity
  have hmax0 : (0:ℝ) ≤ max V 0 := le_max_right _ _
  have hVv : V ≤ v := le_trans (le_max_left V 0) (by linarith)
  have hv6 : 6 / (A * c₀) ≤ v := by linarith
  have hv24 : 24 / (A * cdisk) ≤ v := by linarith
  set m : ℕ := mOf (3/2) n J with hmdef
  set q : ℕ := qgap (3/2) J with hqdef
  set Q : ℕ := min (qgap (3/2) (J - 1)) (qgap (3/2) (J + 1)) with hQdef
  set ρ : ℝ := rho (3/2) n J with hρdef
  have hρpos : 0 < ρ := rho_pos _ _ _
  have hqNat : 1 ≤ q := one_le_qgap (by norm_num) hJ1
  have hqR : (0:ℝ) < (q : ℝ) := by exact_mod_cast hqNat
  obtain ⟨hnum1, hnum2, hnum3, hnum4, -⟩ :=
    hV v hVv ((m : ℕ) : ℝ) ((q : ℕ) : ℝ) ((Q : ℕ) : ℝ) hm1 hm2 hq_low hq_up hQ
  have hsmallN : m + q + 2 ≤ n := by
    have h : ((m + q + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast h
  obtain ⟨hL, hR⟩ := crossing_slopes32 hJ1 hJn hsmallN
  have hcl : 1/(32*B*v) ≤ dstep n ρ m := le_trans hnum3 hL
  have hcr : dstep n ρ (m + q - 1) ≤ -(1/(32*B*v)) := le_trans hR (by linarith)
  -- the radius
  set σ : ℝ := Real.log (‖z‖ / ρ) with hσdef
  have hznorm : ‖z‖ = ρ * Real.exp σ := by
    rw [hσdef, Real.exp_log (by positivity)]
    field_simp
  have hσ : |σ| ≤ c₀ / (q : ℝ) := hσbound
  -- the tail constant
  set K : ℝ := Real.exp (-(1/(32*B*v) - c₀/(q:ℝ)) * (Q:ℝ)) *
      (((m : ℝ) + 1) + Real.exp ((q:ℝ) * (c₀/(q:ℝ)))
        / (1 - Real.exp (-(1/(32*B*v) - c₀/(q:ℝ))))) with hKdef
  have hden : 0 < 1 - Real.exp (-(1/(32*B*v) - c₀/(q:ℝ))) := by
    have : Real.exp (-(1/(32*B*v) - c₀/(q:ℝ))) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have htail : ∑' mm : ℕ, (if mm = m ∨ mm = m + q then 0
      else dcoeff (3/2) n mm * (ρ * Real.exp σ) ^ mm)
      ≤ Real.exp (Phi n ρ m + (m : ℝ) * σ) * K := by
    have h := tail_sum_bound (p := 3/2) (n := n) (m₀ := m) (q := q) (Q := Q)
      (ρ := ρ) (σ := σ) (c := 1/(32*B*v)) (γ := c₀/(q:ℝ)) hρpos hqNat hσ hnum1
      (crossing_Phi hJ1 hJn) hcl hcr (fun mm hmm h1 h2 => supp_gap hJ2 hJn hmm h1 h2)
    refine le_trans h (le_of_eq ?_)
    rw [hKdef]; ring
  -- smallness of `K`
  have hmc : A * c₀ * v / 6 ≤ (m : ℝ) * (c₀ / (q : ℝ)) := by
    have hfrac : c₀ / (2 * v^2) ≤ c₀ / (q : ℝ) :=
      div_le_div_of_nonneg_left hc₀pos.le hqR (by linarith)
    have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h2 : (A/3) * v ^ 3 * (c₀ / (2 * v^2)) ≤ (m : ℝ) * (c₀ / (2*v^2)) :=
      mul_le_mul_of_nonneg_right hm1 (by positivity)
    have h3 : (m : ℝ) * (c₀ / (2*v^2)) ≤ (m : ℝ) * (c₀/(q:ℝ)) :=
      mul_le_mul_of_nonneg_left hfrac hmnn
    have h4 : (A/3) * v ^ 3 * (c₀ / (2 * v^2)) = A * c₀ * v / 6 := by field_simp; ring
    linarith
  have hEexp : A * c₀ * v / 6 ≤ Real.exp ((m : ℝ) * (c₀ / (q : ℝ))) := by
    have h1 : (m : ℝ) * (c₀ / (q : ℝ)) ≤ Real.exp ((m : ℝ) * (c₀ / (q : ℝ))) := by
      have := Real.add_one_le_exp ((m : ℝ) * (c₀ / (q : ℝ))); linarith
    linarith
  have hEbig : 4 * c₀ / cdisk ≤ Real.exp ((m : ℝ) * (c₀ / (q : ℝ))) := by
    have h2 : 4 * c₀ / cdisk = 24 / (A * cdisk) * (A * c₀ / 6) := by
      field_simp
      ring
    have h1 : 24 / (A * cdisk) * (A * c₀ / 6) ≤ v * (A * c₀ / 6) :=
      mul_le_mul_of_nonneg_right hv24 (by positivity)
    rw [h2]
    calc 24 / (A * cdisk) * (A * c₀ / 6) ≤ v * (A * c₀ / 6) := h1
      _ = A * c₀ * v / 6 := by ring
      _ ≤ Real.exp ((m : ℝ) * (c₀ / (q : ℝ))) := hEexp
  have hEpos : (0:ℝ) < Real.exp ((m : ℝ) * (c₀ / (q : ℝ))) := Real.exp_pos _
  have hKsmall : 16 * K ≤ cdisk := by
    have h1 : Real.exp ((m : ℝ) * (c₀/(q:ℝ))) * K < c₀ / 4 := hnum2
    have h2 : (4 * c₀ / cdisk) * K ≤ Real.exp ((m : ℝ) * (c₀/(q:ℝ))) * K :=
      mul_le_mul_of_nonneg_right hEbig hKnn
    have h3 : (4 * c₀ / cdisk) * K < c₀ / 4 := lt_of_le_of_lt h2 h1
    rw [div_mul_eq_mul_div, div_lt_iff₀ hcd] at h3
    nlinarith [hc₀pos]
  have hK4 : K ≤ 1/4 := by
    have h1 : Real.exp ((m : ℝ) * (c₀/(q:ℝ))) * K < c₀ / 4 := hnum2
    have h2 : (1:ℝ) ≤ Real.exp ((m : ℝ) * (c₀/(q:ℝ))) := Real.one_le_exp (by positivity)
    nlinarith
  -- apply the transition lemma
  have hσ2 : |(q : ℝ) * σ| ≤ 2 := by
    rw [abs_mul, abs_of_pos hqR]
    have : (q : ℝ) * |σ| ≤ (q : ℝ) * (c₀ / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hσ hqR.le
    have heq : (q : ℝ) * (c₀ / (q : ℝ)) = c₀ := by field_simp
    linarith [hc₀half]
  obtain ⟨l, hl, hdist⟩ := zero_in_model_disk_of_transition (p := 3/2) (n := n) (m₀ := m)
    (q := q) (ρ := ρ) (σ := σ) (K := K) hρpos hqNat (isSupp_mOf hJ1 hJn)
    (crossing_dcoeff hJ1 hJn) hσ2 hKnn hK4 htail hznorm hz0
  refine ⟨l, hl, ?_⟩
  rw [modelDisk, Metric.mem_closedBall, dist_eq_norm]
  refine le_trans hdist ?_
  rw [modelRadius, ← hρdef, ← hqdef]
  have hfin : 16 * K * ρ ≤ cdisk * ρ := mul_le_mul_of_nonneg_right hKsmall hρpos.le
  exact (div_le_div_iff_of_pos_right hqR).2 hfin

set_option maxHeartbeats 4000000 in
/-- **Outside the transition regions there is no zero** (`p = 3/2`). -/
theorem no_zero_dominant_p32 {A B c₀ : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hB2 : 2 ≤ B)
    (hc₀pos : 0 < c₀) (hc₀half : c₀ ≤ 1/2) (hc₀B : c₀ ≤ 1/(256*B^2)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → n ≤ nu (3/2) j →
      A ≤ rho (3/2) n (j + 1) → rho (3/2) n j ≤ B →
      ∀ z : ℂ, rho (3/2) n j ≤ ‖z‖ → ‖z‖ < rho (3/2) n (j + 1) →
        c₀ / ((qgap (3/2) j : ℕ) : ℝ) < Real.log (‖z‖ / rho (3/2) n j) →
        c₀ / ((qgap (3/2) (j + 1) : ℕ) : ℝ) < Real.log (rho (3/2) n (j + 1) / ‖z‖) →
        iteratedDeriv n (F (3/2)) z ≠ 0 := by
  have hB : 0 < B := by linarith
  obtain ⟨V, hV3, hV⟩ := numeric_core hA hAB (η := 1) one_pos hc₀pos hc₀half hc₀B
  obtain ⟨N, hN⟩ := p32_local_bounds hA hAB
    (max V 0 + 6 / (A * c₀) + 32 * (2 * B + 6) / c₀ + 2 * (2 * B + 6))
  refine ⟨N, fun n hn j hj1 hjn hjA hjB z hzl hzr hsbig htbig => ?_⟩
  obtain ⟨v, hW, hv3, hnv6, hnlow, hj2, hm1, hm2, hq_low, hq_up, hqp_up, hQ, hQ2⟩ :=
    hN n j hn hj1 hjn hjA hjB
  have hvpos : (0:ℝ) < v := by linarith
  have hmax0 : (0:ℝ) ≤ max V 0 := le_max_right _ _
  have hp1 : (0:ℝ) < 6 / (A * c₀) := by positivity
  have hp2 : (0:ℝ) < 32 * (2 * B + 6) / c₀ := by positivity
  have hp3 : (0:ℝ) < 2 * (2 * B + 6) := by positivity
  have hVv : V ≤ v := le_trans (le_max_left V 0) (by linarith)
  have hv6 : 6 / (A * c₀) ≤ v := by linarith
  have hvS : 32 * (2 * B + 6) / c₀ ≤ v := by linarith
  have hvcube : 2 * (2 * B + 6) ≤ v := by linarith
  set m : ℕ := mOf (3/2) n j with hmdef
  set q : ℕ := qgap (3/2) j with hqdef
  set q' : ℕ := qgap (3/2) (j + 1) with hq'def
  set ρ : ℝ := rho (3/2) n j with hrdef
  set ρ' : ℝ := rho (3/2) n (j + 1) with hr'def
  have hρpos : 0 < ρ := rho_pos _ _ _
  have hρ'pos : 0 < ρ' := rho_pos _ _ _
  have hqNat : 1 ≤ q := one_le_qgap (by norm_num) hj1
  have hq'Nat : 1 ≤ q' := one_le_qgap (by norm_num) (by omega)
  have hqR : (0:ℝ) < (q : ℝ) := by exact_mod_cast hqNat
  have hq'R : (0:ℝ) < (q' : ℝ) := by exact_mod_cast hq'Nat
  have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hq'low : v ^ 2 ≤ ((q' : ℕ) : ℝ) := by
    have h := min_le_right (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1))
    have hc2 : (((min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) : ℕ)) : ℝ)
        ≤ ((q' : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  -- the block length
  set T : ℝ := (m : ℝ) + (q : ℝ) + (q' : ℝ) + 2 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hTle : T ≤ (2*B + 6) * v ^ 3 :=
    block_length_le hv3 hm2 hq_up hqp_up
  -- the two logarithmic offsets
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hρpos hzl
  set s : ℝ := Real.log (‖z‖ / ρ) with hsdef
  set t : ℝ := Real.log (ρ' / ‖z‖) with htdef
  have hsnn : 0 ≤ s := by
    rw [hsdef]; exact Real.log_nonneg (by rw [le_div_iff₀ hρpos]; linarith)
  have htnn : 0 ≤ t := by
    rw [htdef]; exact Real.log_nonneg (by rw [le_div_iff₀ hzpos]; linarith)
  have hznorms : ‖z‖ = ρ * Real.exp s := by
    rw [hsdef, Real.exp_log (by positivity)]; field_simp
  have hznormt : ‖z‖ = ρ' * Real.exp (-t) := by
    rw [htdef, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hsum : s + t = Real.log ρ' - Real.log ρ := by
    rw [hsdef, htdef, Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    ring
  -- block bounds inside `n`
  have hone : (1:ℝ) ≤ v := by linarith
  have hv3le : (2*B+6) * v ^ 3 ≤ v ^ 6 / 2 := by
    have h1 : v ^ 3 * (2*B+6) ≤ v ^ 3 * (v/2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : v ^ 4 ≤ v ^ 6 := pow_le_pow_right₀ hone (by norm_num)
    nlinarith
  have hsmallN3 : m + q + q' + 2 ≤ n := by
    have h : ((m + q + q' + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      have h1 : (m : ℝ) + (q : ℝ) + (q' : ℝ) + 2 ≤ (2*B+6) * v ^ 3 := by
        rw [hTdef] at hTle; linarith
      linarith [hnlow, hv3le]
    exact_mod_cast h
  have hsmallN : m + q + 2 ≤ n := by omega
  have hms : mOf (3/2) n (j + 1) = m + q := mOf_succ (by norm_num) hj1 hjn
  have hsmallN' : mOf (3/2) n (j + 1) + q' + 2 ≤ n := by rw [hms]; omega
  -- the numerical core with the three-block support gap
  set Q3 : ℕ := min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 2)) with hQ3def
  have hQ3 : v ^ 2 ≤ ((Q3 : ℕ) : ℝ) := by
    have h1 : v ^ 2 ≤ ((qgap (3/2) (j - 1) : ℕ) : ℝ) := by
      have h := min_le_left (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1))
      have hc : (((min (qgap (3/2) (j - 1)) (qgap (3/2) (j + 1)) : ℕ)) : ℝ)
          ≤ ((qgap (3/2) (j - 1) : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    rw [hQ3def, Nat.cast_min]
    exact le_min h1 hQ2
  obtain ⟨hnum1, hnum2, hnum3, hnum4, -⟩ :=
    hV v hVv ((m : ℕ) : ℝ) ((q : ℕ) : ℝ) ((Q3 : ℕ) : ℝ) hm1 hm2 hq_low hq_up hQ3
  set c : ℝ := 1/(32*B*v) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  -- slopes at the two ends of the three-term block
  obtain ⟨hLj, hRj⟩ := crossing_slopes32 hj1 hjn hsmallN
  obtain ⟨hLj', hRj'⟩ := crossing_slopes32 (show 1 ≤ j + 1 by omega)
    (le_trans hjn (nu_lt_nu_succ (by norm_num) hj1).le) hsmallN'
  have hcl : c ≤ dstep n ‖z‖ m := by
    rw [hznorms, dstep_exp_shift n m hρpos]
    have h : c ≤ dstep n ρ m := le_trans hnum3 hLj
    linarith
  have hcr : dstep n ‖z‖ (m + (q + q') - 1) ≤ -c := by
    have hidx : m + (q + q') - 1 = mOf (3/2) n (j + 1) + q' - 1 := by rw [hms]; omega
    have hMcast : ((mOf (3/2) n (j + 1) : ℕ) : ℝ) + ((q' : ℕ) : ℝ) + 2 = T := by
      rw [hTdef, hms]; push_cast; ring
    have hslope : c ≤ (1 / (2 * (((mOf (3/2) n (j + 1) : ℕ) : ℝ) + ((q' : ℕ) : ℝ) + 2)))
        * (((q' : ℕ) : ℝ) - 1) / 2 := by
      rw [hMcast, hcdef]
      exact numeric_block_slope (q' := ((q' : ℕ) : ℝ)) hB2 hv3 hq'low hTpos hTle
    rw [hidx, hznormt, dstep_exp_shift n _ hρ'pos]
    linarith [hRj', htnn]
  -- the weight identities
  have hPA : Phi n ‖z‖ m ≤ Phi n ‖z‖ (m + q) - (q : ℝ) * s := by
    rw [hznorms, Phi_exp_shift n m hρpos, Phi_exp_shift n (m + q) hρpos,
      crossing_Phi hj1 hjn]
    push_cast
    nlinarith [hsnn]
  have hPB : Phi n ‖z‖ (m + (q + q')) ≤ Phi n ‖z‖ (m + q) - (q' : ℝ) * t := by
    have hidx : m + (q + q') = mOf (3/2) n (j + 1) + q' := by rw [hms]; ring
    have hidx2 : m + q = mOf (3/2) n (j + 1) := hms.symm
    rw [hidx, hidx2, hznormt, Phi_exp_shift n _ hρ'pos, Phi_exp_shift n _ hρ'pos,
      crossing_Phi (show 1 ≤ j + 1 by omega)
        (le_trans hjn (nu_lt_nu_succ (by norm_num) hj1).le)]
    push_cast
    nlinarith [htnn]
  -- the spacing lower bound
  have hspacing : (1 / (2 * ((m : ℝ) + (q : ℝ) + (q' : ℝ) + 2)))
      * (((q : ℝ)) + ((q' : ℝ))) / 2 ≤ Real.log ρ' - Real.log ρ :=
    rho_log_spacing32 hj1 hjn hsmallN3
  have hD : 1/(2*(2*B + 6)*v) ≤ s + t := by
    rw [hsum]
    refine le_trans ?_ hspacing
    have h := numeric_block_spacing (B := B) (v := v) (q := (q:ℝ)) (q' := (q':ℝ))
      (T := T) hB2 hv3 hq_low hq'low hTpos hTle
    rw [hTdef] at h
    linarith
  have hS : 16 / c₀ ≤ (q : ℝ) * s + (q' : ℝ) * t := by
    have h1 : v ^ 2 * (s + t) ≤ (q : ℝ) * s + (q' : ℝ) * t := by
      have hqs : v ^ 2 * s ≤ (q : ℝ) * s := mul_le_mul_of_nonneg_right hq_low hsnn
      have hq's : v ^ 2 * t ≤ (q' : ℝ) * t := mul_le_mul_of_nonneg_right hq'low htnn
      nlinarith
    have h2 : v ^ 2 * (1/(2*(2*B + 6)*v)) ≤ v ^ 2 * (s + t) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have h3 : v ^ 2 * (1/(2*(2*B + 6)*v)) = v / (2 * (2 * B + 6)) := by
      field_simp
    have h4 : 16 / c₀ ≤ v / (2 * (2 * B + 6)) := by
      rw [div_le_div_iff₀ hc₀pos (by positivity)]
      rw [div_le_iff₀ hc₀pos] at hvS
      nlinarith
    linarith
  -- the tail is small
  have hE2 : (2:ℝ) ≤ Real.exp ((m : ℝ) * (c₀/(q:ℝ))) :=
    exp_weight_ge_two hA hc₀pos hv3 hv6 (by linarith) hqR hq_up
  have htailsmall : Real.exp (-c * (Q3:ℝ)) * (((m : ℝ) + 1) + 1 / (1 - Real.exp (-c)))
      ≤ c₀ / 8 :=
    tail_small_of_numeric (γ := c₀/(q:ℝ)) (by positivity) hnum1 (Nat.cast_nonneg _)
      (by positivity) (by positivity) hE2 hnum2
  -- the two neighbour ratios
  have hdA : c₀ < (q : ℝ) * s := by
    rw [div_lt_iff₀ hqR] at hsbig
    rw [hsdef]
    linarith [hsbig, mul_comm ((q:ℝ)) (Real.log (‖z‖ / ρ))]
  have hdB : c₀ < (q' : ℝ) * t := by
    rw [div_lt_iff₀ hq'R] at htbig
    rw [htdef]
    linarith [htbig, mul_comm ((q':ℝ)) (Real.log (ρ' / ‖z‖))]
  have hsmallsum : Real.exp (-((q : ℝ) * s)) + Real.exp (-((q' : ℝ) * t))
      + Real.exp (-c * (Q3:ℝ)) * (((m : ℝ) + 1) + 1 / (1 - Real.exp (-c))) < 1 :=
    dominance_sum_lt_one hc₀pos hc₀half hdA hdB hS htailsmall
  refine no_zero_of_dominant (p := 3/2) (n := n) (m₀ := m) (q := q) (q' := q') (Q := Q3)
    (r := ‖z‖) (c := c) (dA := (q : ℝ) * s) (dB := (q' : ℝ) * t)
    hzpos (by omega) hcpos ?_ hcl hcr ?_ ?_ ?_ (by positivity) (by positivity) hPA hPB
    hsmallsum rfl
  · refine ⟨j + 1, by omega, ?_⟩
    have hnu := nu_eq_add_mOf (p := (3/2:ℝ)) (n := n) (j := j + 1)
      (le_trans hjn (nu_lt_nu_succ (by norm_num) hj1).le)
    rw [hms] at hnu
    omega
  · intro mm hmm h1 h2
    by_contra hcon
    push_neg at hcon
    obtain ⟨hn0, hn1, hn2⟩ := hcon
    exact hmm (dcoeff_zero_in_block3 hj1 hjn h1 (by omega) hn0 (by omega) (by omega))
  · intro mm hmm hlt
    exact (supp_gap3 hj2 hjn hmm).1 hlt
  · intro mm hmm hgt
    have h := (supp_gap3 hj2 hjn hmm).2 (by omega)
    omega

end SparseFock
