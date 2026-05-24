/-
# External Inputs and Named Assumptions

This file collects the external results and named assumptions used in the
paper "A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality"
that are NOT proved in this formalization.

Each assumption is documented with its origin, mathematical content, and
role in the proof chain.
-/
import Mathlib
import RequestProject.Paper.Defs

open scoped BigOperators TensorProduct
open LinearMap Module Submodule

noncomputable section

/-! ## Looijenga Input (Section 3)

The Looijenga input is the deep algebro-geometric result that enters the
optimality proof. It originates from:

- **External Theorem 3.1** (Looijenga 1997): The image of the stabilizer
  S^#_C on the Prym module H_C is U^#(H_C), the full unitary group of
  the skew-Hermitian intersection form over the cyclotomic ring R_C.
  Reference: E. Looijenga, "Prym representations of mapping class groups",
  Geom. Dedicata 64 (1997), no. 1, 69–83.

- **Proposition 3.4** (Single-character projective closure): After base
  change to ℂ, the identity component of the projective Zariski closure of
  H_ψ acting on P(V∨_ψ) is PSp(V_ψ) if ψ² = 1, and PSL(V_ψ) if ψ² ≠ 1.

- **Corollary 3.5** (Finite-orbit subvarieties are trivial): If Z ⊂ P(V∨_ψ)
  is a closed subvariety with finite H_ψ-orbit, then Z = ∅ or Z = P(V∨_ψ).

### Convention: ψ vs ψ⁻¹ and the Prym duality

The paper uses the following identifications (Convention 2.6):

  E_ψ ≅ H₁(Σ; ℂ_{ψ⁻¹})    (Prym homology with ψ⁻¹-coefficients)
  E_ψ∨ ≅ H¹(Σ; ℂ_ψ) = V_ψ   (Prym cohomology with ψ-coefficients)

The contraction map T_x : V∨_ψ → Hom(N, M) sends ψ⁻¹-twisted cohomology
classes to homomorphisms between multiplicity spaces. The Looijenga input
(Corollary 3.5) applies to the H_ψ-action on P(V∨_ψ).

Replacing ψ by ψ⁻¹ exchanges E_ψ ↔ E_{ψ⁻¹} and V_ψ ↔ V_{ψ⁻¹}.
Since the Looijenga projective closure is PSp when ψ² = 1 and PSL when
ψ² ≠ 1, and both conditions are symmetric in ψ ↔ ψ⁻¹ (since
(ψ⁻¹)² = ψ⁻² = 1 ⇔ ψ² = 1), the final dichotomy PSp/PSL is
unchanged by this substitution. In particular, the rank inequality
m + n ≥ 2g − 1 is independent of the choice of convention.
-/

/--
**Looijenga input (Corollary 3.5 in linear-algebraic form).**

This structure encodes the consequence of Looijenga's theorem that enters
the optimality proof: for the H_ψ-action on V_ψ, no finite-index subgroup
preserves a proper non-zero linear subspace.

This is the linear-algebraic translation of "every finite-orbit closed
subvariety of P(V∨_ψ) is trivial" (Corollary 3.5). The projective statement
follows from the identity component of the Zariski closure being PSp or PSL
(Proposition 3.4): these groups act irreducibly on V_ψ (i.e., V_ψ has no
proper nonzero invariant subspace), and more generally no finite-index
subgroup preserves such a subspace.

**Not proved here.** Requires: Looijenga's cyclic Prym image theorem (1997),
base change of unitary groups over cyclotomic rings, Zariski closure
computation, and projective algebraic geometry infrastructure not in Mathlib.
-/
structure LooijengaInput (V : Type*) [AddCommGroup V] [Module ℂ V]
    (H : Type*) [Group H] (act : H →* (V ≃ₗ[ℂ] V)) where
  /-- **Single-character projective closure (Proposition 3.4).**
  The projective Zariski closure of the H-action on P(V∨) has identity
  component PSp(V) or PSL(V). This is encoded as: the action admits no
  proper non-zero invariant subspace for any finite-index subgroup. -/
  no_finite_index_invariant_proper_subspace :
    ∀ (W : Submodule ℂ V), W ≠ ⊥ → W ≠ ⊤ →
      ∀ (H₀ : Subgroup H), H₀.FiniteIndex →
        ∃ h ∈ H₀, Submodule.map (act h).toLinearMap W ≠ W

/-! ## Westwick Bound (Section 7)

The Westwick bound is an external result from:

  R. Westwick, "Spaces of matrices of fixed rank",
  Linear Multilinear Algebra 20 (1987), no. 2, 171–174.

It bounds the dimension of a constant-rank linear subspace of matrices.
-/

/--
**External Theorem 7.1 (Westwick, 1987).**
Let 2 ≤ r ≤ m ≤ n. If L ⊂ Hom(ℂⁿ, ℂᵐ) is a complex linear subspace
such that every non-zero element has rank exactly r, then
  dim L ≤ m + n − 2r + 1.

**Not proved here.** This is Westwick's theorem from the 1987 paper cited above.
-/
theorem westwick_bound
    {m n r : ℕ} (hr : 2 ≤ r) (hrm : r ≤ m) (hmn : m ≤ n)
    (L : Submodule ℂ ((Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)))
    (hcr : ∀ f ∈ L, f ≠ 0 → finrank ℂ (LinearMap.range f) = r) :
    finrank ℂ L ≤ m + n - 2 * r + 1 := by
  sorry

/--
**Lemma 7.2 (Weak constant-rank bound).**
If L ⊂ Hom(ℂⁿ, ℂᵐ) is a complex linear subspace where every non-zero
element has the same rank r ≥ 1, then dim L ≤ m + n − 1.

**Not proved here.** Depends on `westwick_bound` for r ≥ 2, and a separate
rank-1 argument for r = 1 (all elements factor as a ⊗ α, giving dim ≤ max(m,n)).
-/
theorem weak_constant_rank_bound
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (L : Submodule ℂ ((Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)))
    (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) (hrn : r ≤ n)
    (hcr : ∀ f ∈ L, f ≠ 0 → finrank ℂ (LinearMap.range f) = r) :
    finrank ℂ L ≤ m + n - 1 := by
  sorry

/--
**Lemma 7.2, abstract version over arbitrary finite-dimensional spaces.**
If L ⊂ Hom(N, M) is a subspace where every non-zero element has the same
rank, then dim L ≤ dim M + dim N − 1.

**Not proved here.** Reduces to `weak_constant_rank_bound` by choosing bases.
-/
theorem weak_constant_rank_bound_abstract
    {M N : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    (hM : 0 < finrank ℂ M) (hN : 0 < finrank ℂ N)
    (L : Submodule ℂ (N →ₗ[ℂ] M))
    (r : ℕ) (hr : 1 ≤ r)
    (hcr : ∀ f ∈ L, f ≠ 0 → finrank ℂ (LinearMap.range f) = r) :
    finrank ℂ L ≤ finrank ℂ M + finrank ℂ N - 1 := by
  sorry

end
