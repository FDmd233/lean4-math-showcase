/-
# Proved Linear-Algebraic Core

This file contains the fully proved linear-algebraic lemmas that form
the backbone of the optimality argument in the paper
"A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality".

Every declaration in this file is proved without `sorry`.
-/
import Mathlib
import RequestProject.Paper.Defs

open scoped BigOperators TensorProduct
open LinearMap Module Submodule

noncomputable section

/-! ## Section 5: Support invariance and equivariance -/

section Support

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- The canonical isomorphism V ⊗ U ≃ Hom(U∨, V) for finite-dimensional U. -/
private noncomputable def canonicalTensorHomEquiv (V U : Type*)
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] :
    V ⊗[ℂ] U ≃ₗ[ℂ] (Dual ℂ U →ₗ[ℂ] V) :=
  (TensorProduct.comm ℂ V U).trans
    ((TensorProduct.congr (evalEquiv ℂ U) (LinearEquiv.refl ℂ V)).trans
      (dualTensorHomEquiv ℂ (Dual ℂ U) V))

omit [FiniteDimensional ℂ V] in
private lemma canonicalTensorHomEquiv_eq_contraction (x : V ⊗[ℂ] U) (f : Dual ℂ U) :
    (TensorProduct.rid ℂ V) ((TensorProduct.map LinearMap.id f) x) =
    canonicalTensorHomEquiv V U x f := by
  induction x using TensorProduct.induction_on with
  | zero => simp [canonicalTensorHomEquiv]
  | tmul v u =>
    simp [canonicalTensorHomEquiv, dualTensorHomEquiv, dualTensorHom, TensorProduct.comm_tmul]
  | add x y hx hy => simp_all [map_add]

omit [FiniteDimensional ℂ V] in
/--
**Nonzero tensor has nonzero Prym support.**
If x ≠ 0 in V ⊗ U (with U finite-dimensional), then prymSupport x ≠ ⊥.

Proof: if prymSupport x = ⊥, then for every f : U∨, the contraction
(id ⊗ f)(x) = 0. But the map x ↦ (f ↦ (id ⊗ f)(x)) is the canonical
isomorphism V ⊗ U ≃ Hom(U∨, V), so x = 0, contradicting x ≠ 0.
-/
lemma nonzero_tensor_support_ne_bot
    (x : V ⊗[ℂ] U) (hx : x ≠ 0) :
    prymSupport x ≠ ⊥ := by
  intro h
  apply hx
  have hspan : ∀ f : Dual ℂ U,
      (TensorProduct.rid ℂ V) ((TensorProduct.map LinearMap.id f) x) = 0 := by
    intro f
    have : (TensorProduct.rid ℂ V) ((TensorProduct.map LinearMap.id f) x) ∈ prymSupport x :=
      Submodule.subset_span ⟨f, rfl⟩
    rw [h] at this
    exact this
  have heq : canonicalTensorHomEquiv V U x = 0 := by
    ext f
    rw [← canonicalTensorHomEquiv_eq_contraction]
    exact hspan f
  exact (canonicalTensorHomEquiv V U).injective (by rw [heq]; simp)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] in
/--
**Lemma 5.2, K-invariance of Prym support.**
For an invertible linear map k : U ≃ U, the Prym support is invariant
under the K-action: S((id ⊗ k) · x) = S(x).

Proof: applying a dual functional f to (id ⊗ k)(x) is the same as
applying f ∘ k to x, and as k ranges over all of U∨, so does f ∘ k.
-/
theorem support_K_invariant
    (x : V ⊗[ℂ] U) (f : U ≃ₗ[ℂ] U) :
    prymSupport ((TensorProduct.map LinearMap.id f.toLinearMap) x) =
    prymSupport x := by
  refine' le_antisymm _ _;
  · refine' Submodule.span_le.mpr _;
    rintro _ ⟨ g, rfl ⟩;
    refine' Submodule.subset_span ⟨ g.comp f.toLinearMap, _ ⟩;
    induction x using TensorProduct.induction_on <;> aesop;
  · refine' Submodule.span_le.mpr _;
    rintro _ ⟨ g, rfl ⟩;
    refine' Submodule.subset_span ⟨ g.comp f.symm.toLinearMap, _ ⟩;
    simp +decide [ TensorProduct.map_map ];
    exact congr_arg ( fun f => TensorProduct.map LinearMap.id f x ) ( by ext; simp +decide )

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] in
/--
**Lemma 5.2, H_ψ-equivariance of Prym support.**
For h : V ≃ V (the action of a mapping class on V_ψ),
  S((h ⊗ id) · x) = h · S(x).
The support transforms equivariantly under the Prym monodromy action.
-/
theorem support_equivariant
    (x : V ⊗[ℂ] U) (h : V ≃ₗ[ℂ] V) :
    prymSupport ((TensorProduct.map h.toLinearMap LinearMap.id) x) =
    Submodule.map h.toLinearMap (prymSupport x) := by
  refine' le_antisymm _ _ <;> rw [ prymSupport ] <;>
    simp +decide [ Submodule.map_le_iff_le_comap, Submodule.span_le ];
  · rintro _ ⟨ f, rfl ⟩ ; simp +decide [ prymSupport ] ;
    refine' ⟨ _, Submodule.subset_span ⟨ f, rfl ⟩, _ ⟩;
    induction x using TensorProduct.induction_on <;> simp +decide [ * ];
  · rintro _ ⟨ f, rfl ⟩;
    refine' Submodule.subset_span ⟨ f, _ ⟩;
    refine' TensorProduct.induction_on x _ _ _ <;> simp_all +decide [ TensorProduct.map_tmul ]

omit [FiniteDimensional ℂ U] in
/--
**Corollary 5.5: Injectivity of the contraction map from full support.**
If S(x) = V_ψ (full Prym support), then the contraction map
T_x : V∨_ψ → U is injective.

Proof: T∨_x : U∨ → V_ψ has image S(x). Full support means T∨_x is
surjective, which dualizes to T_x being injective.
-/
theorem contraction_injective_of_full_support
    (x : V ⊗[ℂ] U)
    (hfull : prymSupport x = ⊤) :
    Function.Injective (contractionMapLin (V := V) (U := U) x) := by
  intro l₁ l₂ h_eq
  have h_zero : ∀ v ∈ prymSupport x, l₁ v = l₂ v := by
    intro v hv
    have h_zero : ∀ f : Module.Dual ℂ U, f ((contractionMapLin x) l₁) = f ((contractionMapLin x) l₂) := by
      grind;
    refine' Submodule.span_induction _ _ _ _ hv <;> simp_all +decide [ prymSupport ];
    intro f; replace h_eq := congr_arg ( fun g => f ( g ) ) h_eq; simp_all +decide [ contractionMapLin ] ;
    convert h_eq using 1 <;> simp +decide [ dualTensorHom ];
    · refine' TensorProduct.induction_on x _ _ _ <;>
        simp +decide [ TensorProduct.map_tmul, TensorProduct.rid_tmul ];
      · exact fun _ _ => mul_comm _ _;
      · exact fun x y hx hy => by rw [ hx, hy ] ;
    · simp +decide [ TensorProduct.uncurry ];
      refine' TensorProduct.induction_on x _ _ _ <;>
        simp_all +decide [ TensorProduct.map_tmul, TensorProduct.lift.tmul ];
      exact fun _ _ => mul_comm _ _
  aesop

end Support

/-! ## Section 6: Rank strata -/

section RankStrata

variable {V M N : Type*}
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
  [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ M] [FiniteDimensional ℂ N] in
/--
**Lemma 6.2: Rank strata are K-orbit invariants.**
For k = (A, B) ∈ GL(M) × GL(N) and every r,
  rank(A · T_x(ℓ) · B⁻¹) = rank(T_x(ℓ)).
Left and right multiplication by invertible matrices preserves rank.
-/
theorem rank_strata_K_invariant
    (Tx : Module.Dual ℂ V →ₗ[ℂ] (N →ₗ[ℂ] M))
    (A : M ≃ₗ[ℂ] M) (B : N ≃ₗ[ℂ] N) (_r : ℕ) (ℓ : Module.Dual ℂ V) :
    finrank ℂ (LinearMap.range ((A.toLinearMap.comp (Tx ℓ)).comp B.symm.toLinearMap)) =
    finrank ℂ (LinearMap.range (Tx ℓ)) := by
  rw [ show ( ( A : M →ₗ[ℂ] M ) ∘ₗ Tx ℓ ) ∘ₗ ( B.symm : N →ₗ[ℂ] N ) =
    ( A : M →ₗ[ℂ] M ) ∘ₗ ( Tx ℓ ∘ₗ ( B.symm : N →ₗ[ℂ] N ) ) by rfl ];
  nontriviality;
  have h_range : LinearMap.range (A ∘ₗ Tx ℓ ∘ₗ B.symm.toLinearMap) =
      Submodule.map A.toLinearMap (LinearMap.range (Tx ℓ)) := by
    simp +decide [ LinearMap.range_comp ];
  rw [ h_range, LinearEquiv.finrank_map_eq ]

omit [FiniteDimensional ℂ M] [FiniteDimensional ℂ N] in
/--
**Lemma 6.3: Rank strata transform equivariantly under H_ψ.**
Under the convention T_{h·x}(ℓ) = T_x(h⁻¹·ℓ), the rank strata
transform as Z_r(h·x) = h · Z_r(x).
-/
theorem rank_strata_equivariant
    (Tx : Module.Dual ℂ V →ₗ[ℂ] (N →ₗ[ℂ] M))
    (h : V ≃ₗ[ℂ] V) (r : ℕ) :
    rankStratumSet (Tx.comp h.symm.dualMap.toLinearMap) r =
      h.dualMap '' (rankStratumSet Tx r) := by
  ext ℓ
  simp only [rankStratumSet, Set.mem_setOf_eq, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Set.mem_image]
  constructor
  · intro hℓ
    refine ⟨h.symm.dualMap ℓ, hℓ, ?_⟩
    show h.dualMap (h.symm.dualMap ℓ) = ℓ
    ext v; simp [LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨ℓ', hℓ', rfl⟩
    show finrank ℂ ↑(Tx (h.symm.dualMap (h.dualMap ℓ'))).range ≤ r
    have : h.symm.dualMap (h.dualMap ℓ') = ℓ' := by
      ext v; simp [LinearEquiv.dualMap_apply, LinearEquiv.apply_symm_apply]
    rw [this]; exact hℓ'

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ N] in
/--
**Proposition 6.4: Finite-orbit rank strata force constant rank.**
Suppose T_x : V∨_ψ → Hom(N, M) is injective and each rank stratum is
either empty or everything (the Looijenga/Corollary 3.5 consequence).
Then every non-zero element of the image has the same rank.

The hypothesis `hstrata_trivial` encodes the consequence of Corollary 3.5
applied to rank strata: each Z_r(x) ⊂ P(V∨_ψ) is either ∅ or P(V∨_ψ).
-/
theorem constant_rank_from_finite_orbit
    (Tx : Module.Dual ℂ V →ₗ[ℂ] (N →ₗ[ℂ] M))
    -- Hypothesis: each rank stratum is either empty or everything
    (hstrata_trivial : ∀ r : ℕ,
      (∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 →
        finrank ℂ (LinearMap.range (Tx ℓ)) ≤ r) ∨
      (∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 →
        ¬ finrank ℂ (LinearMap.range (Tx ℓ)) ≤ r)) :
    ∃ r₀ : ℕ, ∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 →
      finrank ℂ (LinearMap.range (Tx ℓ)) = r₀ := by
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, ∀ ℓ : Dual ℂ V, ℓ ≠ 0 →
      finrank ℂ (LinearMap.range (Tx ℓ)) ≤ r₀ := by
    use finrank ℂ M;
    exact fun ℓ _ => Submodule.finrank_le _;
  induction' r₀ using Nat.strong_induction_on with r₀ ih;
  cases' hstrata_trivial ( r₀ - 1 ) with h h;
  · rcases r₀ with ( _ | r₀ );
    · exact ⟨ 0, fun ℓ hℓ => le_antisymm ( hr₀ ℓ hℓ ) ( Nat.zero_le _ ) ⟩;
    · exact ih r₀ ( Nat.lt_succ_self r₀ ) h;
  · exact ⟨ r₀, fun ℓ hℓ => le_antisymm ( hr₀ ℓ hℓ )
      ( not_lt.mp fun contra => h ℓ hℓ ( Nat.le_sub_one_of_lt contra ) ) ⟩

end RankStrata

end
