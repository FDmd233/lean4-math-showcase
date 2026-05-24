/-
# The Affine-Prym Construction (Section 2)

This file formalizes the affine-Prym construction (Section 2) from the paper
"A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality".

The topological content (surface groups, mapping class groups, group
cohomology) is parameterized abstractly. The Looijenga input (Section 3)
is encoded in `Paper/ExternalInputs.lean`.
-/
import Mathlib

open scoped BigOperators TensorProduct
open LinearMap Module

noncomputable section

/-! ## Section 2: The affine-Prym construction -/

section AffinePrymConstruction

variable {G : Type*} [Group G]

/--
**Lemma 2.1 (Block matrix multiplication identity).**
The assignment γ ↦ ρ(γ) where ρ(γ) is the block matrix
  ⎛ ψ(γ)·I  U(γ) ⎞
  ⎝   0      1   ⎠
is a group homomorphism, provided U is a 1-cocycle satisfying
U(γδ) = U(γ) + ψ(γ)·U(δ).

We verify that block(γ) · block(δ) = block(γδ).
-/
theorem block_matrix_mul_identity
    {n : ℕ} (ψ_val : G → ℂ)
    (hψ_mul : ∀ γ δ : G, ψ_val (γ * δ) = ψ_val γ * ψ_val δ)
    (U : G → Fin n → ℂ)
    (hcocycle : ∀ γ δ : G, U (γ * δ) = U γ + ψ_val γ • U δ)
    (γ δ : G) :
    let block (g : G) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      Matrix.of (fun i j =>
        if h₁ : (i : ℕ) < n then
          if h₂ : (j : ℕ) < n then
            ψ_val g * (if i = ⟨j, by omega⟩ then 1 else 0)
          else
            U g ⟨i, h₁⟩
        else
          if (j : ℕ) < n then 0
          else 1)
    block γ * block δ = block (γ * δ) := by
  ext i j; simp +decide [ Matrix.mul_apply, Fin.sum_univ_castSucc, hψ_mul, hcocycle ] ;
  split_ifs <;> simp_all +decide [ Finset.sum_ite, Fin.val_inj ];
  · rw [ Finset.card_eq_one.mpr ] ; aesop;
    exact ⟨ ⟨ j, by linarith ⟩, by ext; aesop ⟩;
  · rw [ add_comm, Finset.sum_eq_single ⟨ i, by linarith ⟩ ] <;> aesop

/--
**Lemma 2.2 (Non-vanishing on the kernel).**
Let K = ker ψ. For any cocycle U representing a non-zero extension class,
U|_K is not identically zero.

Proof: if U|_K = 0, then U descends to a cocycle of the finite group
Γ_g/K = im(ψ). Over ℂ, H¹ of a finite group vanishes, so U is a
coboundary, contradicting the non-zero class assumption.

The hypothesis `hnonzero` asserts that U is *not* a coboundary
(i.e., the cohomology class [U] ≠ 0 in H¹(Γ_g; ℂ_ψ ⊗ V)), not merely
that U is pointwise nonzero. A coboundary has the form
γ ↦ ψ(γ)·v − v for some v ∈ V.
-/
theorem cocycle_nonvanishing_on_kernel
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : G →* ℂˣ) (U : G → V)
    (hcocycle : ∀ γ δ : G, U (γ * δ) = U γ + (ψ γ : ℂ) • U δ)
    -- The cohomology class is nonzero: U is not a coboundary
    (hnonzero : ¬ ∃ v : V, ∀ γ : G, U γ = (ψ γ : ℂ) • v - v)
    (hfinite_image : Set.Finite (Set.range ψ)) :
    ∃ γ : G, ψ γ = 1 ∧ U γ ≠ 0 := by
  have h_nonzero_restrict : ¬(∀ γ ∈ ψ.ker, U γ = 0) := by
    intro h
    generalize_proofs at *; (
    obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, (ψ g₀) ≠ 1 ∧ ∀ γ : G, (ψ γ) ∈ Subgroup.zpowers (ψ g₀) := by
      have h_cyclic : IsCyclic (↥(MonoidHom.range ψ)) := by
        have h_cyclic : Finite (↥(MonoidHom.range ψ)) := by
          exact Set.Finite.to_subtype hfinite_image
        generalize_proofs at *; (
        exact inferInstance)
      generalize_proofs at *; (
      obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ↥(MonoidHom.range ψ), ∀ g : ↥(MonoidHom.range ψ), g ∈ Subgroup.zpowers g₀ := by
        exact h_cyclic.exists_generator
      generalize_proofs at *; (
      rcases g₀ with ⟨ g₀, ⟨ γ, rfl ⟩ ⟩ ; use γ; simp_all +decide [ Subgroup.mem_zpowers_iff ] ; (
      refine' ⟨ _, fun δ => _ ⟩
      all_goals generalize_proofs at *;
      · contrapose! hnonzero; simp_all +decide [ Subtype.ext_iff ] ; (
        exact ⟨ 0, fun γ => by simp +decide [ ← hg₀ γ, h γ ( hg₀ γ ▸ rfl ) ] ⟩);
      · exact Exists.elim ( hg₀ _ _ rfl ) fun k hk => ⟨ k, by simpa [ Subtype.ext_iff ] using hk ⟩)))
    generalize_proofs at *; (
    have h_U_g₀_k : ∀ k : ℤ, U (g₀ ^ k) = ((ψ g₀ : ℂ) ^ k - 1) • ( (ψ g₀ - 1 : ℂ)⁻¹ • U g₀ ) := by
      intro k
      have h_U_g₀_k_step : ∀ k : ℕ, U (g₀ ^ k) = ((ψ g₀ : ℂ) ^ k - 1) • ( (ψ g₀ - 1 : ℂ)⁻¹ • U g₀ ) := by
        intro k
        induction' k with k ih
        generalize_proofs at *; (
        simp +decide [ h ]);
        simp_all +decide [ pow_succ, mul_assoc ];
        simp +decide [ ← smul_assoc, ← add_smul ] ; ring;
        rw [ show ( ψ g₀ : ℂ ) ^ k = ( ψ g₀ : ℂ ) ^ k * 1 by ring, show ( ψ g₀ : ℂ ) ^ k * 1 = ( ψ g₀ : ℂ ) ^ k * ( ( -1 + ( ψ g₀ : ℂ ) ) * ( -1 + ( ψ g₀ : ℂ ) ) ⁻¹ ) by rw [ mul_inv_cancel₀ ( by intro h; exact hg₀.1 <| by rw [ ← Units.val_inj ] ; simp_all +decide [ add_eq_zero_iff_eq_neg ] ) ] ] ; ring;
        grind
      generalize_proofs at *; (
      rcases Int.eq_nat_or_neg k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ zpow_neg, zpow_natCast ];
      have := hcocycle ( g₀ ^ k ) ⁻¹ ( g₀ ^ k ) ; simp_all +decide [ pow_succ, mul_assoc ] ;
      rw [ eq_comm, add_eq_zero_iff_eq_neg ] at this ; simp_all +decide [ sub_smul, smul_sub ] ;)
    generalize_proofs at *; (
    have h_decomp : ∀ γ : G, ∃ k : ℤ, ∃ κ : G, γ = g₀ ^ k * κ ∧ ψ κ = 1 := by
      intro γ
      obtain ⟨k, hk⟩ : ∃ k : ℤ, ψ γ = (ψ g₀) ^ k := by
        exact Exists.elim ( hg₀.2 γ ) fun k hk => ⟨ k, hk.symm ⟩
      generalize_proofs at *; (
      refine' ⟨ k, ( g₀ ^ k ) ⁻¹ * γ, _, _ ⟩ <;> simp +decide [ hk ])
    generalize_proofs at *; (
    refine' hnonzero ⟨ ( ( ψ g₀ - 1 : ℂ ) ⁻¹ • U g₀ ), fun γ => _ ⟩
    generalize_proofs at *; (
    obtain ⟨ k, κ, rfl, hκ ⟩ := h_decomp γ; simp +decide [ *, sub_smul ] ;)))))
  push_neg at h_nonzero_restrict
  obtain ⟨γ, hγ, hU⟩ := h_nonzero_restrict
  exact ⟨γ, hγ, hU⟩

/--
**Corollary 2.3 (Infinite image).**
The image of ρ_ψ^univ is infinite.

Proof: by Lemma 2.2, choose γ ∈ ker ψ with U(γ) ≠ 0. Then ψ(γ) = 1
and ρ(γ) is a non-trivial unipotent element. Its powers ρ(γ)ⁿ have
upper-right entry n·U(γ), so they are pairwise distinct.
-/
theorem infinite_image_of_nonzero_cocycle
    {V : Type*} [AddCommGroup V] [Module ℂ V] [CharZero ℂ]
    (U : G → V)
    (hker_nonvanish : ∃ γ : G, U γ ≠ 0 ∧
      ∀ n : ℕ, U (γ ^ (n + 1)) = (n + 1 : ℕ) • U γ) :
    Set.Infinite (Set.range U) := by
  obtain ⟨γ, hγ_nonzero, hγ_pow⟩ := hker_nonvanish
  have h_injective : Function.Injective (fun n : ℕ => (n + 1) • U γ) := by
    intro m n hmn;
    simp_all +decide [ ← Nat.cast_smul_eq_nsmul ℂ ];
  exact Set.infinite_of_injective_forall_mem h_injective fun n => ⟨ _, hγ_pow n ⟩

/--
**Lemma 2.4 (Stabilizer fixes the universal class up to change of basis).**
Let h : V ≃ V be an automorphism. Then there exists a dual automorphism
k : V∨ ≃ V∨ such that (h ⊗ k⁻¹)(∑ bᵢ ⊗ bᵢ∨) = ∑ bᵢ ⊗ bᵢ∨.

This encodes the fact that the universal extension class id_{V_ψ} ∈ V_ψ ⊗ V∨_ψ
is invariant under the diagonal action of GL(V_ψ).
-/
theorem stabilizer_fixes_universal_class
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (h : V ≃ₗ[ℂ] V) :
    ∃ (k : Module.Dual ℂ V ≃ₗ[ℂ] Module.Dual ℂ V),
      ∀ (b : Basis (Fin (finrank ℂ V)) ℂ V),
      (TensorProduct.map h.toLinearMap k.symm.toLinearMap)
        (∑ i, (b i) ⊗ₜ[ℂ] (b.dualBasis i)) =
      ∑ i, (b i) ⊗ₜ[ℂ] (b.dualBasis i) := by
  refine' ⟨ _, _ ⟩;
  exact ( LinearEquiv.dualMap h );
  intro b; simp +decide [ TensorProduct.map_tmul, Finset.sum_apply' ] ;
  have h_basis : ∀ i, h (b i) = ∑ j, (h.toMatrix b b) j i • b j := by
    simp +decide [ toMatrix_apply, Finsupp.single_apply ];
  have h_dual_basis : ∀ i, h.symm.dualMap (b.coord i) = ∑ j, (h.symm.toMatrix b b) i j • b.coord j := by
    intro i; ext j; simp +decide [ h_basis, LinearMap.dualMap_apply, h.symm.toMatrix_apply ] ;
    rw [ ← b.sum_repr j ] ; simp +decide [ mul_comm ] ;
    rw [ ← b.sum_repr j ] ; simp +decide ; ring;
    have h_dual_basis : h.symm j = ∑ x, (b.repr j) x • h.symm (b x) := by
      conv_lhs => rw [ ← b.sum_repr j ];
      rw [ map_sum, Finset.sum_congr rfl ] ; intros ; simp +decide [ h.symm.map_smul ];
    rw [ h_dual_basis, map_sum ] ; simp +decide ;
  simp +decide only [h_basis, h_dual_basis, TensorProduct.tmul_sum, TensorProduct.sum_tmul];
  simp +decide [ TensorProduct.smul_tmul, mul_comm, smul_smul ];
  have h_matrix_mul : ∀ i j, ∑ k, (h.toMatrix b b) i k * (h.symm.toMatrix b b) k j = if i = j then 1 else 0 := by
    intro i j; have := congr_fun ( congr_fun ( show ( toMatrix b b ) ( h : V →ₗ[ℂ] V ) * ( toMatrix b b ) ( h.symm : V →ₗ[ℂ] V ) = 1 from ?_ ) i ) j; simp_all +decide [ Matrix.mul_apply ] ;
    · simp +decide [ Matrix.one_apply ];
    · rw [ ← toMatrix_comp ] ; aesop;
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun i _ => _;
  rw [ Finset.sum_comm ];
  rw [ Finset.sum_congr rfl fun j _ => by rw [ ← Finset.sum_smul, h_matrix_mul ] ] ; aesop

/--
**Lemma 2.5 (Finite character orbit).**
The Mod(Σ_g)-orbit of a finite character ψ is finite.

Proof: if the order of ψ divides q, then ψ factors through the finite
group H₁(Σ_g; ℤ/qℤ). There are only finitely many characters of a
finite group.
-/
theorem finite_character_orbit
    {A : Type*} [CommGroup A] [Fintype A] :
    Finite (A →* ℂˣ) :=
  inferInstance

end AffinePrymConstruction

end
