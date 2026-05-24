/-
# A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality

Formalization of the linear-algebraic dependency skeleton from the paper
in Lean 4 / Mathlib.

## File organization

- `Paper/Defs.lean`: Core definitions (PrymData, TwoBlockData, contraction
  map, Prym support, rank strata)
- `Paper/ExternalInputs.lean`: Named external assumptions (Looijenga input,
  Westwick bound) with full documentation of their mathematical origin
- `Paper/Construction.lean`: The affine-Prym construction (Section 2),
  fully proved
- `Paper/LinearAlgebraCore.lean`: Proved linear-algebraic lemmas (support
  invariance/equivariance, nonzero tensor support, rank strata, constant rank)
- `Paper/MainTheorems.lean`: Conditional main theorems deriving the rank
  inequality from the dependency chain plus named external inputs

## Proof status

This project formalizes the linear-algebraic dependency skeleton and proves
the final rank inequality conditional on named external inputs:
- Looijenga's theorem / Corollary 3.5 (encoded as `LooijengaInput`)
- Westwick's fixed-rank bound (encoded as `sorry` in `westwick_bound`)
- Topological inputs (surface groups, MCG, twisted cohomology) are
  parameterized abstractly

The following are NOT formalized: surface topology, mapping class groups,
twisted cohomology, Looijenga's cyclic Prym image theorem, ordinary
conjugacy (Schur lemma for local systems), and Westwick's theorem.

## Prym duality convention

  E_ψ ≅ H₁(Σ; ℂ_{ψ⁻¹})    (Prym homology with ψ⁻¹-coefficients)
  E_ψ∨ ≅ H¹(Σ; ℂ_ψ) = V_ψ   (Prym cohomology with ψ-coefficients)

Replacing ψ by ψ⁻¹ does not change the final projective Zariski-closure
dichotomy PSp/PSL, since ψ² = 1 ⇔ (ψ⁻¹)² = 1.
-/
import RequestProject.Paper.Defs
import RequestProject.Paper.ExternalInputs
import RequestProject.Paper.Construction
import RequestProject.Paper.LinearAlgebraCore
import RequestProject.Paper.MainTheorems

-- Axiom audit for the two final declarations

#print axioms two_block_optimality_arithmetic_core
#print axioms two_block_optimality_conditional
