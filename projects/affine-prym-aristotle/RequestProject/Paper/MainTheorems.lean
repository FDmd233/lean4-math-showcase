/-
# Conditional Main Theorems

This file contains the main theorems of the paper
"A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality",
proved conditional on named external inputs (Looijenga, Westwick).

The dependency chain is:
  1. Finite K-orbit → finite-index stabilizer H₀ (hypothesis)
  2. K-invariance + H-equivariance of support → H₀ stabilizes S(x)
  3. Looijenga no-invariant-subspace → S(x) = V_ψ (Proposition 5.4)
  4. Full support → contraction map injective (Corollary 5.5)
  5. Injective + Looijenga → constant rank (Proposition 6.4)
  6. Westwick → dim L ≤ m + n − 1 (Lemma 7.2)
  7. dim V_ψ ≤ m + n − 1 → m + n ≥ 2g − 1 (Theorem 1.2)

**Remaining external assumptions in `two_block_optimality_conditional`:**
- `hstrata_trivial`: Each pulled-back rank stratum Z_r(x) ⊂ P(V∨_ψ) is
  either empty or all of P(V∨_ψ). This follows from Corollary 3.5 (Looijenga)
  applied to determinantal varieties, but that argument (finite MCG-orbit
  of rank strata → strata are trivial) is NOT fully formalized here.

Note: `hTx_nonzero` (T_x(ℓ) ≠ 0 for ℓ ≠ 0) was previously a separate
hypothesis, but is now derived internally from the injectivity of the
contraction map (Corollary 5.5, which IS formalized).
-/
import Mathlib
import RequestProject.Paper.Defs
import RequestProject.Paper.ExternalInputs
import RequestProject.Paper.LinearAlgebraCore

open scoped BigOperators TensorProduct
open LinearMap Module Submodule

noncomputable section

/-! ## Proposition 5.4: Full Prym support through actual mechanism -/

section FullPrymSupport

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

omit [FiniteDimensional ℂ V] in
/--
**Proposition 5.4 (Full Prym support), proved through the actual mechanism.**

Let x ∈ V_ψ ⊗ U be non-zero. Assume:
- (Finite K-orbit data) A finite-index subgroup H₀ ≤ H_ψ stabilizes the
  K-orbit of x: for each h ∈ H₀, there exists k_h ∈ GL(U) such that
  (h ⊗ id)(x) = (id ⊗ k_h)(x).
- (Looijenga input) No finite-index subgroup of H_ψ preserves a proper
  non-zero subspace of V_ψ.

Then S(x) = V_ψ.

**Proof mechanism:**
1. For h ∈ H₀, by H-equivariance (Lemma 5.2): S((h ⊗ id) · x) = h · S(x).
2. By the stabilizer hypothesis: (h ⊗ id)(x) = (id ⊗ k_h)(x).
3. By K-invariance (Lemma 5.2): S((id ⊗ k_h) · x) = S(x).
4. Therefore h · S(x) = S(x) for all h ∈ H₀.
5. Since x ≠ 0, S(x) ≠ ⊥ (by `nonzero_tensor_support_ne_bot`).
6. By the Looijenga no-invariant-subspace input, S(x) = V_ψ.
-/
theorem full_prym_support
    {H : Type*} [Group H]
    (act : H →* (V ≃ₗ[ℂ] V))
    (x : V ⊗[ℂ] U)
    -- x is non-zero
    (hx : x ≠ 0)
    -- Finite K-orbit data: a finite-index subgroup H₀ stabilizes x up to K
    (H₀ : Subgroup H)
    (hH₀_fi : H₀.FiniteIndex)
    (hstab : ∀ h : H, h ∈ H₀ →
      ∃ (k : U ≃ₗ[ℂ] U),
        (TensorProduct.map (act h).toLinearMap LinearMap.id) x =
        (TensorProduct.map LinearMap.id k.toLinearMap) x)
    -- Looijenga input (Corollary 3.5 / Proposition 3.4)
    (looijenga : LooijengaInput V H act) :
    prymSupport x = ⊤ := by
  -- Step 5: S(x) ≠ ⊥ from x ≠ 0
  have hsupp_ne_bot : prymSupport x ≠ ⊥ := nonzero_tensor_support_ne_bot x hx
  -- Step 6: Apply Looijenga to get a contradiction if S(x) ≠ ⊤
  by_contra hne_top
  -- By Looijenga, since S(x) ≠ ⊥ and S(x) ≠ ⊤, there exists h ∈ H₀
  -- with h · S(x) ≠ S(x)
  obtain ⟨h, hh, hne⟩ := looijenga.no_finite_index_invariant_proper_subspace
    (prymSupport x) hsupp_ne_bot hne_top H₀ hH₀_fi
  -- But h ∈ H₀ so h stabilizes x up to K
  obtain ⟨k, hk⟩ := hstab h hh
  -- Derive contradiction: h · S(x) = S(x)
  apply hne
  -- S((h ⊗ id) · x) = h · S(x) by equivariance (Lemma 5.2)
  have heq := support_equivariant x (act h)
  -- S((id ⊗ k) · x) = S(x) by K-invariance (Lemma 5.2)
  have hkinv := support_K_invariant x k
  -- (h ⊗ id)(x) = (id ⊗ k)(x) by stabilizer hypothesis
  -- Therefore h · S(x) = S((h ⊗ id) · x) = S((id ⊗ k) · x) = S(x)
  rw [← heq, hk, hkinv]

end FullPrymSupport

/-! ## Main optimality theorems -/

section MainTheorems

/--
**Theorem 1.1(a): Rank of the affine-Prym representation.**
The representation has rank 1 + dim V_ψ = 1 + (2g − 2) = 2g − 1.
This is immediate from the block structure.
-/
theorem rank_of_affine_prym (pd : PrymData) :
    1 + (2 * pd.g - 2) = 2 * pd.g - 1 := by
  have := pd.hg; omega

/--
**Theorem 1.2, arithmetic core (`two_block_optimality_arithmetic_core`).**

Assuming:
- T_x : V∨_ψ → Hom(N, M) is injective (from Proposition 5.4 + Corollary 5.5),
- The Westwick/constant-rank bound: dim(image of T_x) ≤ dim M + dim N − 1,

then dim M + dim N ≥ 2g − 1.

This isolates the pure arithmetic step: the injective contraction map gives
dim V∨_ψ = dim(image) ≤ m + n − 1, and dim V_ψ = 2g − 2, so m + n ≥ 2g − 1.
-/
theorem two_block_optimality_arithmetic_core
    (pd : PrymData)
    (bd : TwoBlockData pd)
    -- Injectivity of contraction map (from steps 1–4 of the proof chain)
    (Tx : Module.Dual ℂ pd.V →ₗ[ℂ] (bd.N →ₗ[ℂ] bd.M))
    (hTx_inj : Function.Injective Tx)
    -- Westwick bound on the image (External Theorem 7.1 / Lemma 7.2)
    (hwestwick : finrank ℂ (LinearMap.range Tx) ≤
      finrank ℂ bd.M + finrank ℂ bd.N - 1) :
    finrank ℂ bd.M + finrank ℂ bd.N ≥ 2 * pd.g - 1 := by
  have hV_dim := pd.hdim
  have hg := pd.hg
  have hrange : finrank ℂ (LinearMap.range Tx) = finrank ℂ (Module.Dual ℂ pd.V) :=
    LinearMap.finrank_range_of_inj hTx_inj
  have hdual : finrank ℂ (Module.Dual ℂ pd.V) = finrank ℂ pd.V :=
    Subspace.dual_finrank_eq
  rw [hrange, hdual, hV_dim] at hwestwick
  omega

/--
**Theorem 1.2, conditional form (`two_block_optimality_conditional`).**

Derives the rank inequality m + n ≥ 2g − 1 from the formalized
dependency chain plus named external inputs. The proof follows these steps:

1. **Full Prym support** (Proposition 5.4): from x ≠ 0, finite K-orbit data,
   and the Looijenga input. Uses `support_K_invariant`, `support_equivariant`,
   `nonzero_tensor_support_ne_bot`, and
   `LooijengaInput.no_finite_index_invariant_proper_subspace`.

2. **Injectivity** (Corollary 5.5): from full support. Uses
   `contraction_injective_of_full_support`.

3. **Constant rank** (Proposition 6.4): from the rank-strata triviality
   hypothesis (itself a consequence of Looijenga applied to determinantal
   varieties). Uses `constant_rank_from_finite_orbit`.

4. **Westwick bound** (Lemma 7.2): external input, applied via
   `weak_constant_rank_bound_abstract` (contains `sorry`).

5. **Arithmetic conclusion**: combines injectivity (dim L = dim V∨ = 2g−2)
   with the Westwick bound (dim L ≤ m + n − 1) to get m + n ≥ 2g − 1.

**Remaining hypotheses (not derived from the formalized chain):**
- `hstrata_trivial`: Each pulled-back rank stratum is trivial. This is a
  consequence of Looijenga's Corollary 3.5 applied to determinantal
  varieties, but the argument that finite MCG-orbit of rank strata implies
  strata triviality is NOT fully formalized.

Note: `hTx_nonzero` (T_x(ℓ) ≠ 0 for ℓ ≠ 0) is derived internally from
`hinj : Function.Injective (contractionMapLin x)` via `hinj.ne`.

**External inputs (not proved):**
- `LooijengaInput`: Corollary 3.5 / Proposition 3.4 (Looijenga 1997).
- `weak_constant_rank_bound_abstract`: Westwick's theorem (1987).
- Finite K-orbit data from MCG orbit finiteness + Lemma 4.2/4.3.
-/
theorem two_block_optimality_conditional
    (pd : PrymData)
    (bd : TwoBlockData pd)
    {H : Type*} [Group H]
    (act : H →* (pd.V ≃ₗ[ℂ] pd.V))
    -- The extension class in V_ψ ⊗ Hom(N, M)
    (x : pd.V ⊗[ℂ] (bd.N →ₗ[ℂ] bd.M))
    -- Step 1 input: x ≠ 0 (from infinite image, Lemma 4.1)
    (hx_ne_zero : x ≠ 0)
    -- Step 1 input: Finite K-orbit data (from finite MCG orbit + Lemma 4.2/4.3)
    (H₀ : Subgroup H) (hH₀_fi : H₀.FiniteIndex)
    (hstab : ∀ h : H, h ∈ H₀ →
      ∃ (k : (bd.N →ₗ[ℂ] bd.M) ≃ₗ[ℂ] (bd.N →ₗ[ℂ] bd.M)),
        (TensorProduct.map (act h).toLinearMap LinearMap.id) x =
        (TensorProduct.map LinearMap.id k.toLinearMap) x)
    -- Looijenga input (Corollary 3.5)
    (looijenga : LooijengaInput pd.V H act)
    -- Step 3 input: rank strata triviality (from Looijenga applied to rank strata)
    -- NOT fully formalized: the argument that finite MCG-orbit of rank strata
    -- implies strata triviality requires projective algebraic geometry
    (hstrata_trivial : ∀ r : ℕ,
      (∀ ℓ : Module.Dual ℂ pd.V, ℓ ≠ 0 →
        finrank ℂ (LinearMap.range (contractionMapLin x ℓ)) ≤ r) ∨
      (∀ ℓ : Module.Dual ℂ pd.V, ℓ ≠ 0 →
        ¬ finrank ℂ (LinearMap.range (contractionMapLin x ℓ)) ≤ r))
    :
    finrank ℂ bd.M + finrank ℂ bd.N ≥ 2 * pd.g - 1 := by
  -- Step 1: Full Prym support (Proposition 5.4)
  have hfull : prymSupport x = ⊤ :=
    full_prym_support act x hx_ne_zero H₀ hH₀_fi hstab looijenga
  -- Step 2: Injectivity of contraction map (Corollary 5.5)
  have hinj : Function.Injective (contractionMapLin x) :=
    contraction_injective_of_full_support x hfull
  -- Step 3: Constant rank (Proposition 6.4)
  obtain ⟨r₀, hr₀⟩ := constant_rank_from_finite_orbit (contractionMapLin x) hstrata_trivial
  -- Derive hTx_nonzero from injectivity
  have hTx_nonzero : ∀ ℓ : Module.Dual ℂ pd.V, ℓ ≠ 0 →
      contractionMapLin x ℓ ≠ 0 := by
    intro ℓ hℓ h_eq
    exact hℓ (hinj (by simp [h_eq]))
  -- Step 4: Westwick bound (Lemma 7.2, external input with sorry)
  -- We need r₀ ≥ 1: since T_x is injective, for any ℓ ≠ 0, T_x(ℓ) ≠ 0,
  -- so T_x(ℓ) has positive rank.
  have hr₀_pos : 1 ≤ r₀ := by
    -- pd.V has dimension 2g-2 ≥ 2, so the dual is nontrivial
    have hdim := pd.hdim
    have hg := pd.hg
    have hVpos : 0 < finrank ℂ pd.V := by omega
    have : Nontrivial pd.V := Module.nontrivial_of_finrank_pos hVpos
    have hDualPos : 0 < finrank ℂ (Module.Dual ℂ pd.V) := by
      rw [Subspace.dual_finrank_eq]; exact hVpos
    have : Nontrivial (Module.Dual ℂ pd.V) := Module.nontrivial_of_finrank_pos hDualPos
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ pd.V, ℓ ≠ 0 := exists_ne 0
    have hfne := hTx_nonzero ℓ hℓ
    rw [← hr₀ ℓ hℓ]
    exact Submodule.one_le_finrank_iff.mpr (by rwa [ne_eq, LinearMap.range_eq_bot])
  -- Apply weak_constant_rank_bound_abstract to L = range(contractionMapLin x)
  have hwestwick : finrank ℂ (LinearMap.range (contractionMapLin x)) ≤
      finrank ℂ bd.M + finrank ℂ bd.N - 1 := by
    have hcr : ∀ f ∈ LinearMap.range (contractionMapLin x),
        f ≠ 0 → finrank ℂ (LinearMap.range f) = r₀ := by
      intro f hf hf_ne
      obtain ⟨ℓ, rfl⟩ := hf
      have hℓ_ne : ℓ ≠ 0 := fun h => hf_ne (by simp [h, map_zero])
      exact hr₀ ℓ hℓ_ne
    exact weak_constant_rank_bound_abstract bd.hM bd.hN _ r₀ hr₀_pos hcr
  -- Step 5: Apply the arithmetic core
  exact two_block_optimality_arithmetic_core pd bd (contractionMapLin x) hinj hwestwick

end MainTheorems

end
