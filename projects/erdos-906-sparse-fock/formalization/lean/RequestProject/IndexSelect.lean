import RequestProject.RadialBounds

/-!
# Selection of the crossing index

For a given derivative order `n` and a given radius `r` in a fixed compact annulus we
select the index `j` with `ρ_j ≤ r < ρ_{j+1}`.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

/-- A threshold turning `n ≥ N` into `V ≤ v` whenever `n ≤ v^6`. -/
theorem exists_threshold_pow_six (V : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ v : ℝ, 0 ≤ v → (n : ℝ) ≤ v ^ 6 → V ≤ v := by
  refine ⟨⌈|V| ^ 6⌉₊, fun n hn v hv hnv => ?_⟩
  have h1 : |V| ^ 6 ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hn
  have h2 : |V| ^ 6 ≤ v ^ 6 := le_trans h1 hnv
  have h3 : |V| ≤ v := le_of_pow_le_pow_left₀ (by norm_num) hv h2
  exact le_trans (le_abs_self V) h3

/-- The auxiliary variable `v = ⁴√j`. -/
theorem exists_quartic_root (j : ℕ) :
    ∃ v : ℝ, 0 ≤ v ∧ v ^ 2 = Real.sqrt j ∧ v ^ 4 = (j : ℝ) :=
  ⟨Real.sqrt (Real.sqrt j), Real.sqrt_nonneg _, sqrt_sqrt_sq _,
    sqrt_sqrt_pow_four _ (Nat.cast_nonneg j)⟩

set_option maxHeartbeats 1000000 in
/-- For all large `n` some crossing radius is below any prescribed positive level. -/
theorem exists_small_crossing {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ j : ℕ, 1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ a := by
  obtain ⟨N₀, hN₀⟩ := exists_threshold_pow_six (max 4 (15 / a))
  refine ⟨max N₀ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hex : ∃ k : ℕ, n ≤ nu (3/2) (k + 1) := by
    refine ⟨n, le_trans ?_ (le_nu (by norm_num) (n + 1))⟩
    omega
  obtain ⟨k, hkspec, hkmin⟩ :
      ∃ k : ℕ, n ≤ nu (3/2) (k + 1) ∧ ∀ i, i < k → ¬ (n ≤ nu (3/2) (i + 1)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  -- `k ≥ 1`
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · exfalso
      subst h0
      rw [show (0:ℕ) + 1 = 1 from rfl, nu_one] at hkspec
      omega
    · exact h
  have hj1 : 1 ≤ k + 1 := by omega
  have hprev : nu (3/2) k < n := by
    have := hkmin (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at this
    omega
  obtain ⟨v, hv0, hv2, hv4⟩ := exists_quartic_root (k + 1)
  have hnv6 : (n : ℝ) ≤ v ^ 6 := by
    have h1 : ((nu (3/2) (k + 1) : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) :=
      nu32_le (k + 1)
    have h2 : (n : ℝ) ≤ ((nu (3/2) (k + 1) : ℕ) : ℝ) := by exact_mod_cast hkspec
    have h3 : ((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) = v ^ 6 := by
      rw [← hv2, ← hv4]
      ring
    linarith
  have hV := hN₀ n hnN₀ v hv0 hnv6
  have hv4' : (4:ℝ) ≤ v := le_trans (le_max_left _ _) hV
  have hv15 : 15 / a ≤ v := le_trans (le_max_right _ _) hV
  have hav : 15 ≤ a * v := by
    rw [div_le_iff₀ ha] at hv15
    linarith
  have hkcast : (k : ℝ) = v ^ 4 - 1 := by
    rw [hv4]
    push_cast
    ring
  -- lower bound on `n`
  have hsqrtk : v ^ 2 - 1 ≤ Real.sqrt (k : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [hkcast]
    nlinarith [hv4', hv0]
  have hnlow : v ^ 6 / 2 ≤ (n : ℝ) := by
    have h1 : (k : ℝ) * Real.sqrt (k : ℝ) - 1 ≤ ((nu (3/2) k : ℕ) : ℝ) := le_nu32 k
    have h2 : ((nu (3/2) k : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hprev
    have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have h3 : (v ^ 4 - 1) * (v ^ 2 - 1) ≤ (k : ℝ) * Real.sqrt (k : ℝ) := by
      calc (v ^ 4 - 1) * (v ^ 2 - 1) = (k : ℝ) * (v ^ 2 - 1) := by rw [hkcast]
        _ ≤ (k : ℝ) * Real.sqrt (k : ℝ) := mul_le_mul_of_nonneg_left hsqrtk hk0
    have hexp : (v ^ 4 - 1) * (v ^ 2 - 1) = v ^ 6 - v ^ 4 - v ^ 2 + 1 := by ring
    rw [hexp] at h3
    have hv2ge : (16:ℝ) ≤ v ^ 2 := by nlinarith
    have hv24 : v ^ 2 ≤ v ^ 4 := by nlinarith
    have hv6 : 16 * v ^ 4 ≤ v ^ 6 := by nlinarith
    linarith
  have hsqrtn : v ^ 3 / (3/2) ≤ Real.sqrt n := by
    refine Real.le_sqrt_of_sq_le ?_
    have hv6nn : (0:ℝ) ≤ v ^ 6 := by positivity
    nlinarith [hnlow, hv6nn]
  -- upper bounds for the gaps
  have hsqk : Real.sqrt (k : ℝ) ≤ v ^ 2 := by
    rw [hv2]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    linarith
  have hq1 : ((qgap (3/2) k : ℕ) : ℝ) ≤ (3/2) * (v ^ 2 + 1) + 1 := by
    have h := qgap32_le hk1
    linarith
  have hq2 : ((qgap (3/2) (k + 1) : ℕ) : ℝ) ≤ (3/2) * (v ^ 2 + 1) + 1 := by
    have h := qgap32_le hj1
    rw [← hv2] at h
    linarith
  have hgapprev : nu (3/2) k + qgap (3/2) k = nu (3/2) (k + 1) :=
    nu_add_qgap (by norm_num) hk1
  have hm : ((mOf (3/2) n (k + 1) : ℕ) : ℝ) + 1 ≤ ((qgap (3/2) k : ℕ) : ℝ) := by
    have hle : mOf (3/2) n (k + 1) + 1 ≤ qgap (3/2) k := by
      simp only [mOf]
      omega
    exact_mod_cast hle
  refine ⟨k + 1, hj1, hkspec, ?_⟩
  obtain ⟨-, hup⟩ := rho_squeeze (p := (3/2 : ℝ)) (by norm_num) hj1 hkspec
  have hm0 : (0:ℝ) ≤ ((mOf (3/2) n (k + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq0 : (0:ℝ) ≤ ((qgap (3/2) (k + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnR : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hsqn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hmono : Real.sqrt n ≤ Real.sqrt ((n : ℝ) + ((mOf (3/2) n (k + 1) : ℕ) : ℝ)
      + ((qgap (3/2) (k + 1) : ℕ) : ℝ)) := Real.sqrt_le_sqrt (by linarith)
  have hnum : ((mOf (3/2) n (k + 1) : ℕ) : ℝ) + ((qgap (3/2) (k + 1) : ℕ) : ℝ)
      ≤ 3 * v ^ 2 + 5 := by linarith
  have hnum0 : (0:ℝ) ≤ ((mOf (3/2) n (k + 1) : ℕ) : ℝ) + ((qgap (3/2) (k + 1) : ℕ) : ℝ) := by
    linarith
  calc rho (3/2) n (k + 1)
      ≤ (((mOf (3/2) n (k + 1) : ℕ) : ℝ) + ((qgap (3/2) (k + 1) : ℕ) : ℝ))
        / Real.sqrt ((n : ℝ) + ((mOf (3/2) n (k + 1) : ℕ) : ℝ)
          + ((qgap (3/2) (k + 1) : ℕ) : ℝ)) := hup
    _ ≤ (((mOf (3/2) n (k + 1) : ℕ) : ℝ) + ((qgap (3/2) (k + 1) : ℕ) : ℝ)) / Real.sqrt n :=
        div_le_div_of_nonneg_left hnum0 hsqn hmono
    _ ≤ (3 * v ^ 2 + 5) / Real.sqrt n := (div_le_div_iff_of_pos_right hsqn).mpr hnum
    _ ≤ a := by
        rw [div_le_iff₀ hsqn]
        have hstep : (3/2) * (3 * v ^ 2 + 5) ≤ a * v ^ 3 := by nlinarith [hav, hv4', hv0]
        nlinarith [hsqrtn, hv0, ha.le]

/-- Selection of the crossing index bracketing a given radius. -/
theorem exists_crossing_index {n : ℕ} {r : ℝ} (hr : 0 < r)
    (hex : ∃ j : ℕ, 1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ r) :
    ∃ j : ℕ, 1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ r ∧ r < rho (3/2) n (j + 1) := by
  classical
  have hbound : ∀ j : ℕ, (1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ r) →
      j < n + ⌈r ^ 2 + r * Real.sqrt n⌉₊ + 1 := by
    rintro j ⟨hj1, hjn, hjr⟩
    have h1 := mOf_add_one_le_of_rho_le hj1 hjn hr hjr
    have h2 : ((mOf (3/2) n j : ℕ) : ℝ) ≤ (⌈r ^ 2 + r * Real.sqrt n⌉₊ : ℝ) := by
      refine le_trans ?_ (Nat.le_ceil _)
      linarith
    have h3 : mOf (3/2) n j ≤ ⌈r ^ 2 + r * Real.sqrt n⌉₊ := by exact_mod_cast h2
    have h4 : j ≤ nu (3/2) j := le_nu (by norm_num) j
    have h5 : nu (3/2) j = n + mOf (3/2) n j := nu_eq_add_mOf hjn
    omega
  obtain ⟨j₀, hj₀⟩ := hex
  have hj₀B : j₀ ≤ n + ⌈r ^ 2 + r * Real.sqrt n⌉₊ + 1 := (hbound j₀ hj₀).le
  have hspec := Nat.findGreatest_spec (P := fun j => 1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ r)
    hj₀B hj₀
  obtain ⟨hJ1, hJn, hJr⟩ := hspec
  refine ⟨Nat.findGreatest (fun j => 1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ r)
    (n + ⌈r ^ 2 + r * Real.sqrt n⌉₊ + 1), hJ1, hJn, hJr, ?_⟩
  have hJB := hbound _ ⟨hJ1, hJn, hJr⟩
  have hnot := Nat.findGreatest_is_greatest
    (P := fun j => 1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ r)
    (n := n + ⌈r ^ 2 + r * Real.sqrt n⌉₊ + 1)
    (k := Nat.findGreatest (fun j => 1 ≤ j ∧ n ≤ nu (3/2) j ∧ rho (3/2) n j ≤ r)
      (n + ⌈r ^ 2 + r * Real.sqrt n⌉₊ + 1) + 1)
    (by omega) (by omega)
  by_contra hcon
  push_neg at hcon
  exact hnot ⟨by omega, le_trans hJn (nu_lt_nu_succ (by norm_num) hJ1).le, hcon⟩

end SparseFock
