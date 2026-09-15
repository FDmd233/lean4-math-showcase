import RequestProject.Aux32

/-!
# The numerical core of the `p = 3/2` covering estimate

All the quantitative inequalities needed to apply the two-term localisation are
collected here as a statement about real parameters `v, m, q, Q` satisfying the
size relations `m ≍ v³`, `q ≍ v²`, `Q ≥ v²` that hold for the active sparse
support (with `v = ⁴√j`, so that `n ≍ v⁶`, `√n ≍ v³`, `q_j ≍ v²`).
-/

namespace SparseFock

open scoped BigOperators

set_option maxHeartbeats 2000000 in
/-- The numerical core.  For all sufficiently large `v`, the tail ratio is smaller than
`c₀/4`, the curvature bound dominates `1/(32 b v)`, the block fits well inside `n`, and
the total covering radius is at most `η`. -/
theorem numeric_core {a b c₀ η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η)
    (hc₀pos : 0 < c₀) (hc₀half : c₀ ≤ 1/2) (hc₀b : c₀ ≤ 1/(256*b^2)) :
    ∃ V : ℝ, 3 ≤ V ∧ ∀ v : ℝ, V ≤ v → ∀ m q Q : ℝ,
      (a/3) * v^3 ≤ m → m ≤ 2*b*v^3 → v^2 ≤ q → q ≤ 2*v^2 → v^2 ≤ Q →
      ( c₀/q < 1/(32*b*v)
        ∧ Real.exp (m * (c₀/q)) * (Real.exp (-(1/(32*b*v) - c₀/q) * Q)
            * ((m+1) + Real.exp (q * (c₀/q)) / (1 - Real.exp (-(1/(32*b*v) - c₀/q))))) < c₀/4
        ∧ 1/(32*b*v) ≤ (1/(2*(m+q+2)))*(q-1)/2
        ∧ m + q + 2 ≤ v^6/2
        ∧ 2*b*(c₀/q) + 2*Real.pi*b/v^2 + 12*b/(a*v) ≤ η ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have p1 : (0:ℝ) < 32*b := by positivity
  have p2 : (0:ℝ) < 1/(32*b) := by positivity
  have p3 : (0:ℝ) < 1/b := by positivity
  have p4 : (0:ℝ) < 4*b + 8 := by positivity
  have p5 : (0:ℝ) < 4*(256*259*128^4)*b^5/c₀ + 1 := by positivity
  have p6 : (0:ℝ) < 24*b/η := by positivity
  have p7 : (0:ℝ) < 24*b/(a*η) := by positivity
  refine ⟨3 + 32*b + 1/(32*b) + 1/b + (4*b+8) + (4*(256*259*128^4)*b^5/c₀ + 1)
    + 24*b/η + 24*b/(a*η), by linarith, ?_⟩
  intro v hV m q Q hm1 hm2 hq1 hq2 hQ
  -- extract the individual largeness conditions
  have hv3 : (3:ℝ) ≤ v := by linarith
  have hvpos : (0:ℝ) < v := by linarith
  have hv32b : 32*b ≤ v := by linarith
  have hvinv : 1/(32*b) ≤ v := by linarith
  have hvb : 1/b ≤ v := by linarith
  have hv4b8 : 4*b + 8 ≤ v := by linarith
  have hvK : 4*(256*259*128^4)*b^5/c₀ + 1 ≤ v := by linarith
  have hvη : 24*b/η ≤ v := by linarith
  have hvaη : 24*b/(a*η) ≤ v := by linarith
  have hbv : 1 ≤ b * v := by
    rw [div_le_iff₀ hb] at hvb
    linarith
  have hv2pos : (0:ℝ) < v^2 := by positivity
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le hv2pos hq1
  have hmpos : (0:ℝ) < m := lt_of_lt_of_le (by positivity) hm1
  set c : ℝ := 1/(32*b*v) with hc
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  set ζ : ℝ := c₀/q with hζ
  have hζpos : (0:ℝ) < ζ := by rw [hζ]; positivity
  have hζle : ζ ≤ c₀ / v^2 := by
    rw [hζ]
    exact div_le_div_of_nonneg_left hc₀pos.le hv2pos hq1
  -- `ζ ≤ c/2`
  have hhalf : ζ ≤ c/2 := by
    refine le_trans hζle ?_
    rw [hc, div_le_iff₀ hv2pos]
    have h1 : 1/(32*b*v)/2 * v^2 = v/(64*b) := by
      field_simp
      ring
    rw [h1, le_div_iff₀ (by positivity : (0:ℝ) < 64*b)]
    nlinarith [hv32b, hc₀half, hb]
  have hδpos : (0:ℝ) < c - ζ := by linarith
  have hδhalf : c/2 ≤ c - ζ := by linarith
  have hδle1 : c - ζ ≤ 1 := by
    have hcle : c ≤ 1 := by
      rw [hc, div_le_one (by positivity)]
      rw [div_le_iff₀ p1] at hvinv
      nlinarith
    linarith
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · -- the tail ratio
    have hceq : c/2 = 1/(64*b*v) := by
      rw [hc]
      field_simp
      ring
    have hclow : 1/(64*b*v) ≤ c - ζ := by linarith [hδhalf, hceq.le, hceq.ge]
    have hone := one_sub_exp_neg_ge hδpos.le hδle1
    have hdenom : 1/(128*b*v) ≤ 1 - Real.exp (-(c - ζ)) := by
      have heq : (1/(64*b*v))/2 = 1/(128*b*v) := by
        field_simp
        ring
      linarith [hone, hclow, heq.le, heq.ge]
    have hdenpos : (0:ℝ) < 1 - Real.exp (-(c - ζ)) := by
      have : (0:ℝ) < 1/(128*b*v) := by positivity
      linarith
    have hqζ : q * ζ = c₀ := by
      rw [hζ]
      field_simp
    have hnum : Real.exp (q * ζ) ≤ 2 := by
      rw [hqζ]
      have h1 : Real.exp c₀ ≤ Real.exp (1/2) := Real.exp_le_exp.2 hc₀half
      have h2 : Real.exp (1/2) ≤ 2 := by
        have hsq : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
        have h3 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
        nlinarith [Real.exp_pos (1/2), hsq, h3]
      linarith
    have hfrac : Real.exp (q * ζ) / (1 - Real.exp (-(c - ζ))) ≤ 256*b*v := by
      rw [div_le_iff₀ hdenpos]
      have h1 : 2 ≤ 256*b*v * (1 - Real.exp (-(c - ζ))) := by
        have h2 : 256*b*v * (1/(128*b*v)) = 2 := by field_simp; ring
        calc (2:ℝ) = 256*b*v * (1/(128*b*v)) := h2.symm
          _ ≤ 256*b*v * (1 - Real.exp (-(c - ζ))) := by
              exact mul_le_mul_of_nonneg_left hdenom (by positivity)
      linarith
    have hmp1 : m + 1 ≤ 3*b*v^3 := by nlinarith [hbv, hvpos, hv3]
    have hexpQ : Real.exp (-(c - ζ) * Q) ≤ Real.exp (-(v/(64*b))) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : v/(64*b) ≤ (c - ζ) * Q := by
        have h2 : (1/(64*b*v)) * v^2 = v/(64*b) := by field_simp
        calc v/(64*b) = (1/(64*b*v)) * v^2 := h2.symm
          _ ≤ (c - ζ) * Q := by
              refine mul_le_mul hclow hQ (by positivity) (le_trans (by positivity) hclow)
      linarith
    have hexpm : Real.exp (m * ζ) ≤ Real.exp (v/(128*b)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : m * ζ ≤ 2*b*v^3 * (c₀/v^2) := by
        refine mul_le_mul hm2 hζle hζpos.le (by positivity)
      have h2 : 2*b*v^3 * (c₀/v^2) = 2*b*c₀*v := by field_simp
      have h3 : 2*b*c₀ ≤ 1/(128*b) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 128*b)]
        have : c₀ * (256*b^2) ≤ 1 := by
          rw [← le_div_iff₀ (by positivity : (0:ℝ) < 256*b^2)]
          simpa [one_div] using hc₀b
        nlinarith
      have h4 : 2*b*c₀*v ≤ (1/(128*b))*v := mul_le_mul_of_nonneg_right h3 hvpos.le
      have h5 : (1/(128*b))*v = v/(128*b) := by field_simp
      linarith [h1, h2.le, h2.ge, h4, h5.le, h5.ge]
    -- combine
    have hnn1 : (0:ℝ) ≤ (m+1) + Real.exp (q * ζ) / (1 - Real.exp (-(c - ζ))) := by
      have : (0:ℝ) ≤ Real.exp (q * ζ) / (1 - Real.exp (-(c - ζ))) := by positivity
      linarith
    have hstep1 : (m+1) + Real.exp (q * ζ) / (1 - Real.exp (-(c - ζ)))
        ≤ 3*b*v^3 + 256*b*v := by linarith
    have hstep2 : Real.exp (-(c - ζ) * Q) * ((m+1) + Real.exp (q * ζ) / (1 - Real.exp (-(c - ζ))))
        ≤ Real.exp (-(v/(64*b))) * (3*b*v^3 + 256*b*v) :=
      mul_le_mul hexpQ hstep1 hnn1 (Real.exp_pos _).le
    have hstep3 : Real.exp (m * ζ) * (Real.exp (-(c - ζ) * Q)
          * ((m+1) + Real.exp (q * ζ) / (1 - Real.exp (-(c - ζ)))))
        ≤ Real.exp (v/(128*b)) * (Real.exp (-(v/(64*b))) * (3*b*v^3 + 256*b*v)) := by
      refine mul_le_mul hexpm hstep2 ?_ (Real.exp_pos _).le
      exact mul_nonneg (Real.exp_pos _).le hnn1
    have hprod : Real.exp (v/(128*b)) * Real.exp (-(v/(64*b))) = Real.exp (-(v/(128*b))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hassoc : Real.exp (v/(128*b)) * (Real.exp (-(v/(64*b))) * (3*b*v^3 + 256*b*v))
        = Real.exp (-(v/(128*b))) * (3*b*v^3 + 256*b*v) := by
      rw [← mul_assoc, hprod]
    rw [hassoc] at hstep3
    -- final bound
    have hx : (0:ℝ) < v/(128*b) := by positivity
    have hexpbd := exp_neg_le_inv_pow_four hx
    have hpow : (v/(128*b))^4 = v^4/(128*b)^4 := by field_simp
    rw [hpow] at hexpbd
    have hbd2 : Real.exp (-(v/(128*b))) ≤ 256*(128*b)^4/v^4 := by
      refine le_trans hexpbd (le_of_eq ?_)
      field_simp
    have hgrow : 3*b*v^3 + 256*b*v ≤ 259*b*v^3 := by nlinarith [hvpos, hv3, hb]
    have hfinal : Real.exp (-(v/(128*b))) * (3*b*v^3 + 256*b*v)
        ≤ (256*(128*b)^4/v^4) * (259*b*v^3) := by
      refine mul_le_mul hbd2 hgrow (by positivity) (by positivity)
    have hval : (256*(128*b)^4/v^4) * (259*b*v^3) = (256*259*128^4)*b^5/v := by
      field_simp
    rw [hval] at hfinal
    have hlast : (256*259*128^4)*b^5/v < c₀/4 := by
      rw [div_lt_div_iff₀ hvpos (by norm_num : (0:ℝ) < 4)]
      have hKv : 4*(256*259*128^4)*b^5/c₀ < v := by linarith
      rw [div_lt_iff₀ hc₀pos] at hKv
      linarith
    linarith
  · -- the curvature bound
    have h1 : m + q + 2 ≤ 2*b*v^3 + 2*v^2 + 2 := by linarith
    have h3 : (0:ℝ) ≤ 32*b*v*(v^2-1) - 4*(2*b*v^3 + 2*v^2 + 2) := by
      have e1 : 32*b*v ≤ 8*b*v^3 := by nlinarith [hv3, hb, hvpos]
      have e2 : 8*v^2 ≤ 8*b*v^3 := by nlinarith [hbv, hvpos, hv3]
      have e3 : (8:ℝ) ≤ 8*b*v^3 := by nlinarith [hbv, hvpos, hv3]
      nlinarith [e1, e2, e3]
    have hstep : 32*b*v*(v^2-1) ≤ 32*b*v*(q-1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have key : 4*(m+q+2) ≤ 32*b*v*(q-1) := by linarith
    have hrw : (1/(2*(m+q+2)))*(q-1)/2 = (q-1)/(4*(m+q+2)) := by
      field_simp
      ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [key]
  · -- the block fits inside `n`
    have h1 : m + q + 2 ≤ 2*b*v^3 + 2*v^2 + 2 := by linarith
    have h2 : (4*b+8) * v^3 ≤ v * v^3 :=
      mul_le_mul_of_nonneg_right hv4b8 (by positivity)
    have h2' : v * v^3 ≤ v^3 * v^3 :=
      mul_le_mul_of_nonneg_right (by nlinarith [hv3, hvpos]) (by positivity)
    have e1 : v^2 ≤ v^3 := by nlinarith [hv3, hvpos]
    have e2 : (1:ℝ) ≤ v^3 := by nlinarith [hv3, hvpos]
    have e3 : v^3 * v^3 = v^6 := by ring
    nlinarith [h1, h2, h2', e1, e2, e3, hb]
  · -- the covering radius
    have h1 : 2*b*ζ ≤ b/v^2 := by
      rw [le_div_iff₀ hv2pos]
      have hz2 : ζ * v^2 ≤ c₀ := by
        have h := hζle
        rw [le_div_iff₀ hv2pos] at h
        exact h
      nlinarith [hz2, hc₀half, hb]
    have h2 : 2*Real.pi*b/v^2 ≤ 8*b/v^2 := by
      refine (div_le_div_iff_of_pos_right hv2pos).mpr ?_
      nlinarith [Real.pi_le_four, hb]
    have h4 : 9*b/v^2 ≤ 9*b/v :=
      div_le_div_of_nonneg_left (by positivity) hvpos (by nlinarith [hv3, hvpos])
    have h5 : 9*b/v ≤ η/2 := by
      rw [div_le_div_iff₀ hvpos (by norm_num : (0:ℝ) < 2)]
      rw [div_le_iff₀ hη] at hvη
      linarith
    have h6 : 12*b/(a*v) ≤ η/2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < a*η)] at hvaη
      nlinarith [hvaη, ha, hvpos]
    have h3 : b/v^2 + 8*b/v^2 = 9*b/v^2 := by ring
    linarith

end SparseFock
