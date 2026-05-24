/-
# Core Definitions for the Affine-Prym Construction Paper

This file formalizes the core definitions used throughout the paper
"A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality".

Since Mathlib does not contain topological infrastructure for surface groups,
mapping class groups, or twisted cohomology, we parameterize these objects
abstractly and capture their essential properties as hypotheses.
-/
import Mathlib

open scoped BigOperators TensorProduct
open LinearMap Module

noncomputable section

/-! ## Core data structures -/

/--
**Paper, Section 1 (Introduction), Equation (1).**
The Prym dimension axiom: for a closed connected oriented surface Σ_g of
genus g ≥ 2 and a non-trivial finite character ψ, the twisted cohomology
space V_ψ = H¹(Σ_g; ℂ_ψ) has complex dimension 2g − 2.

We bundle the genus `g`, the finite-dimensional ℂ-vector space `V`
(playing the role of V_ψ), and the dimension constraint.
-/
structure PrymData where
  /-- The genus of the surface, satisfying g ≥ 2. -/
  g : ℕ
  hg : g ≥ 2
  /-- The Prym cohomology space V_ψ = H¹(Σ_g; ℂ_ψ). -/
  V : Type*
  instACG : AddCommGroup V
  instMod : Module ℂ V
  instFD : FiniteDimensional ℂ V
  /-- Paper, Equation (1): dim_ℂ V_ψ = 2g − 2. -/
  hdim : finrank ℂ V = 2 * g - 2

attribute [instance] PrymData.instACG PrymData.instMod PrymData.instFD

/--
**Paper, Section 4 (Extension classes and ordinary conjugacy).**
A scalar two-block triangular Prym extension datum packages the multiplicity
spaces M and N appearing in the short exact sequence
  0 → ℂ_ψ ⊗ M → ρ → ℂ ⊗ N → 0.
The extension class lies in V_ψ ⊗ Hom(N, M).
-/
structure TwoBlockData (pd : PrymData) where
  /-- The multiplicity space M (for the ψ-isotypical block). -/
  M : Type*
  /-- The multiplicity space N (for the trivial block). -/
  N : Type*
  instACG_M : AddCommGroup M
  instMod_M : Module ℂ M
  instFD_M : FiniteDimensional ℂ M
  instACG_N : AddCommGroup N
  instMod_N : Module ℂ N
  instFD_N : FiniteDimensional ℂ N
  /-- M ≠ 0 (the ψ-block is non-trivial). -/
  hM : 0 < finrank ℂ M
  /-- N ≠ 0 (the trivial block is non-trivial). -/
  hN : 0 < finrank ℂ N

attribute [instance] TwoBlockData.instACG_M TwoBlockData.instMod_M
  TwoBlockData.instFD_M TwoBlockData.instACG_N TwoBlockData.instMod_N
  TwoBlockData.instFD_N

/-! ## Contraction map and Prym support -/

/--
**Paper, Appendix A (Action conventions for the contraction map).**
The contraction map T_x : V∨ → U associated with x ∈ V ⊗ U is defined by
  T_x(ℓ) = (ℓ ⊗ id_U)(x).
This is the linear map from the dual of V to U obtained by contracting the
first tensor factor of x with a linear functional.

Implementation: we use the canonical chain
  V ⊗ U →[eval ⊗ id] V∨∨ ⊗ U →[dualTensorHom] (V∨ →ₗ U).
-/
def contractionMapLin {V U : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup U] [Module ℂ U] :
    V ⊗[ℂ] U →ₗ[ℂ] (Module.Dual ℂ V →ₗ[ℂ] U) :=
  (dualTensorHom ℂ (Module.Dual ℂ V) U).comp
    (TensorProduct.map (Module.evalEquiv ℂ V).toLinearMap LinearMap.id)

/--
**Paper, Definition 5.1 (Prym support).**
For x ∈ V_ψ ⊗ U, the Prym support S(x) is
  S(x) := span { (id_V ⊗ λ)(x) : λ ∈ U∨ } ⊂ V_ψ.
Equivalently, S(x) is the smallest linear subspace S ⊂ V_ψ such that
x ∈ S ⊗ U. The Prym support equals the range of the transpose of the
contraction map.
-/
def prymSupport {V U : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U]
    (x : V ⊗[ℂ] U) : Submodule ℂ V :=
  Submodule.span ℂ
    (Set.range (fun (f : Module.Dual ℂ U) =>
      (TensorProduct.rid ℂ V)
        ((TensorProduct.map (LinearMap.id : V →ₗ[ℂ] V) (f : U →ₗ[ℂ] ℂ)) x)))

/-! ## Rank strata -/

/--
**Paper, Definition 6.1 (Pulled-back determinantal strata).**
For 0 ≤ r ≤ min(m, n), the pulled-back determinantal stratum is defined as
  Z_r(x) = { [ℓ] ∈ P(V∨_ψ) : rank T_x(ℓ) ≤ r }.
Here we define the linear-algebraic version (before projectivization):
the set of ℓ ∈ V∨ such that the finrank of the range of the linear map
corresponding to T_x(ℓ) is at most r.

In the paper, T_x(ℓ) ∈ U = Hom(N, M), so its rank is the rank as a
linear map from N to M.
-/
def rankStratumSet {V M N : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    (Tx : Module.Dual ℂ V →ₗ[ℂ] (N →ₗ[ℂ] M)) (r : ℕ) :
    Set (Module.Dual ℂ V) :=
  {ℓ | finrank ℂ (LinearMap.range (Tx ℓ)) ≤ r}

end

