import Mathlib

/-!
# Entire functions given by power series

General infrastructure used for the sparse Fock series `F_p` of the paper
*Zeros of high derivatives of sparse Fock series*.

A coefficient sequence `c : ℕ → ℂ` is `EntireCoeff` when `∑ ‖c k‖ r ^ k` converges for every
radius `r > 0`.  For such a sequence the function `sumSeries c z = ∑' k, c k * z ^ k` is entire
and its iterated derivatives are obtained by termwise differentiation.
-/

namespace SparseFock

open scoped BigOperators

/-- Coefficient sequences whose power series converges absolutely at every radius. -/
def EntireCoeff (c : ℕ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → Summable fun k : ℕ => ‖c k‖ * r ^ k

/-- The entire function defined by a coefficient sequence. -/
noncomputable def sumSeries (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑' k : ℕ, c k * z ^ k

variable {c : ℕ → ℂ}

theorem EntireCoeff.summable_norm_at (hc : EntireCoeff c) (z : ℂ) :
    Summable fun k : ℕ => ‖c k * z ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (hc (‖z‖ + 1) (by positivity))
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg z) (by linarith) k) (norm_nonneg _)

theorem EntireCoeff.summable_at (hc : EntireCoeff c) (z : ℂ) :
    Summable fun k : ℕ => c k * z ^ k :=
  Summable.of_norm (hc.summable_norm_at z)

/-- A weighted version of absolute convergence: multiplying by `k` does not destroy it. -/
theorem EntireCoeff.summable_mul (hc : EntireCoeff c) {r : ℝ} (hr : 0 < r) :
    Summable fun k : ℕ => (k : ℝ) * (‖c k‖ * r ^ k) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hc (2 * r) (by linarith))
  have hk : (k : ℝ) ≤ 2 ^ k := by
    have : (k : ℕ) < 2 ^ k := Nat.lt_two_pow_self
    exact_mod_cast this.le
  calc (k : ℝ) * (‖c k‖ * r ^ k) = ‖c k‖ * ((k : ℝ) * r ^ k) := by ring
    _ ≤ ‖c k‖ * (2 ^ k * r ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right hk (by positivity)
    _ = ‖c k‖ * (2 * r) ^ k := by rw [mul_pow]

/-- The shifted coefficient sequence appearing in the `n`-th derivative. -/
noncomputable def shiftCoeff (c : ℕ → ℂ) (n : ℕ) (k : ℕ) : ℂ :=
  ((k + n).descFactorial n : ℂ) * c (k + n)

@[simp] theorem shiftCoeff_zero (c : ℕ → ℂ) : shiftCoeff c 0 = c := by
  funext k; simp [shiftCoeff]

theorem shiftCoeff_succ (c : ℕ → ℂ) (n : ℕ) :
    (fun k => ((k + 1 : ℕ) : ℂ) * shiftCoeff c n (k + 1)) = shiftCoeff c (n + 1) := by
  funext k
  have hidx : k + (n + 1) = (k + 1) + n := by omega
  have hdesc : ((k + 1) + n).descFactorial (n + 1) = (k + 1) * (((k + 1) + n).descFactorial n) := by
    rw [Nat.descFactorial_succ]
    congr 1
    omega
  simp only [shiftCoeff, hidx, hdesc]
  push_cast
  ring

/-- One step of the shift preserves everywhere-absolute convergence. -/
theorem EntireCoeff.shiftOne (hc : EntireCoeff c) :
    EntireCoeff (fun k => ((k + 1 : ℕ) : ℂ) * c (k + 1)) := by
  intro r hr
  have hsum : Summable fun k : ℕ => ((k : ℝ) + 1) * (‖c k‖ * r ^ k) := by
    refine ((hc.summable_mul hr).add (hc r hr)).congr (fun k => ?_)
    ring
  have hmul := ((summable_nat_add_iff 1).2 hsum).mul_left (1 / r)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmul
  have hnn : (0:ℝ) ≤ ‖c (k + 1)‖ * r ^ k := by positivity
  have hrk : r ^ (k + 1) = r * r ^ k := by ring
  rw [norm_mul]
  simp only [Complex.norm_natCast, hrk]
  have hrw : 1 / r * (((k : ℝ) + 1 + 1) * (‖c (k + 1)‖ * (r * r ^ k)))
      = ((k : ℝ) + 2) * (‖c (k + 1)‖ * r ^ k) := by
    field_simp
    ring
  push_cast
  rw [hrw]
  nlinarith [hnn]

theorem EntireCoeff.shift (hc : EntireCoeff c) (n : ℕ) : EntireCoeff (shiftCoeff c n) := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    have := ih.shiftOne
    rwa [shiftCoeff_succ c n] at this

theorem EntireCoeff.hasDerivAt (hc : EntireCoeff c) (z : ℂ) :
    HasDerivAt (sumSeries c) (sumSeries (fun k => ((k + 1 : ℕ) : ℂ) * c (k + 1)) z) z := by
  set R : ℝ := ‖z‖ + 1 with hR_def
  have hR1 : (1:ℝ) ≤ R := by simp [hR_def, norm_nonneg z]
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  set u : ℕ → ℝ := fun k => (k : ℝ) * (‖c k‖ * R ^ k) with hu_def
  have hu : Summable u := hc.summable_mul hR
  have hderiv : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) R →
      HasDerivAt (fun w : ℂ => c k * w ^ k) ((k : ℂ) * c k * w ^ (k - 1)) w := by
    intro k w _
    have h := (hasDerivAt_pow k w).const_mul (c k)
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) R →
      ‖(k : ℂ) * c k * w ^ (k - 1)‖ ≤ u k := by
    intro k w hw
    have hwR : ‖w‖ ≤ R := by
      have := Metric.mem_ball.1 hw
      simpa using this.le
    have hw0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg _
    calc ‖(k : ℂ) * c k * w ^ (k - 1)‖ = (k : ℝ) * ‖c k‖ * ‖w‖ ^ (k - 1) := by
          simp [norm_pow]
      _ ≤ (k : ℝ) * ‖c k‖ * R ^ (k - 1) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hwR _) (by positivity)
      _ ≤ (k : ℝ) * ‖c k‖ * R ^ k := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (by omega)) (by positivity)
      _ = u k := by rw [hu_def]; ring
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    simp [Metric.mem_ball, hR_def]
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by simp [Metric.mem_ball, hR]
  have hmain := hasDerivAt_tsum_of_isPreconnected (u := u) (g := fun k w => c k * w ^ k)
    (g' := fun k w => (k : ℂ) * c k * w ^ (k - 1)) hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected hderiv hbound h0 (hc.summable_at 0) hz
  -- reindex the derivative series
  have hsummable : Summable fun k : ℕ => (k : ℂ) * c k * z ^ (k - 1) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hu)
    intro k
    exact hbound k z hz
  have hshift : (∑' k : ℕ, (k : ℂ) * c k * z ^ (k - 1))
      = sumSeries (fun k => ((k + 1 : ℕ) : ℂ) * c (k + 1)) z := by
    rw [hsummable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add, sumSeries]
    refine tsum_congr (fun k => ?_)
    simp [mul_assoc]
  rw [← hshift]
  exact hmain

theorem EntireCoeff.differentiable (hc : EntireCoeff c) : Differentiable ℂ (sumSeries c) :=
  fun z => (hc.hasDerivAt z).differentiableAt

theorem EntireCoeff.deriv_eq (hc : EntireCoeff c) :
    deriv (sumSeries c) = sumSeries (fun k => ((k + 1 : ℕ) : ℂ) * c (k + 1)) := by
  funext z
  exact (hc.hasDerivAt z).deriv

/-- Termwise differentiation of an everywhere convergent power series, iterated. -/
theorem EntireCoeff.iteratedDeriv_eq (hc : EntireCoeff c) (n : ℕ) :
    iteratedDeriv n (sumSeries c) = sumSeries (shiftCoeff c n) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, (hc.shift n).deriv_eq, shiftCoeff_succ]

/-- The value of a power series at the origin. -/
theorem sumSeries_zero (c : ℕ → ℂ) : sumSeries c 0 = c 0 := by
  rw [sumSeries, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

end SparseFock
