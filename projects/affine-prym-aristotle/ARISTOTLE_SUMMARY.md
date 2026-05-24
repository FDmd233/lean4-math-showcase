# Summary of changes for run 404e2044-8d4e-418b-92d7-0d948a687116
All three requested cleanups have been applied:

## 1. Removed `hTx_nonzero` from `two_block_optimality_conditional`

The hypothesis `(hTx_nonzero : ∀ ℓ : Module.Dual ℂ pd.V, ℓ ≠ 0 → contractionMapLin x ℓ ≠ 0)` has been removed from the theorem signature. It is now derived internally after establishing injectivity:

```lean
have hTx_nonzero : ∀ ℓ : Module.Dual ℂ pd.V, ℓ ≠ 0 →
    contractionMapLin x ℓ ≠ 0 := by
  intro ℓ hℓ h_eq
  exact hℓ (hinj (by simp [h_eq]))
```

The file header and docstrings have been updated to document this change.

## 2. Replaced inaccurate "acts transitively on proper linear subspaces"

In `ExternalInputs.lean`, the sentence in the `LooijengaInput` docstring:
> "which acts transitively on proper linear subspaces"

has been replaced with the irreducibility formulation:
> "these groups act irreducibly on V_ψ (i.e., V_ψ has no proper nonzero invariant subspace), and more generally no finite-index subgroup preserves such a subspace."

## 3. Build output included

Raw `lake build RequestProject.Main` output and `#print axioms` output are saved in `BUILD_OUTPUT.txt`. Summary:

```
'two_block_optimality_arithmetic_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_block_optimality_conditional' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Build completed successfully (8031 jobs).
```

The `sorryAx` in `two_block_optimality_conditional` comes exclusively from the three Westwick-related theorems in `ExternalInputs.lean`. The arithmetic core is fully proved.

# Summary of changes for run 71de8281-3bf7-45cf-ba07-fde85f458508
# Final Verification and Cleanup — Summary

## 1. Build Verification

**`lake build RequestProject.Main`** completes successfully (8031 jobs).

**Axiom audit output:**
```
'two_block_optimality_arithmetic_core' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'two_block_optimality_conditional' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` in `two_block_optimality_conditional` comes exclusively from the three Westwick-related theorems in `ExternalInputs.lean`. The arithmetic core is fully proved (no `sorryAx`).

## 2. Unstable Development Artifacts — Removed

- **`RequestProject/Paper/Construction.lean`**: Replaced the remaining `exact?` in `cocycle_nonvanishing_on_kernel` with an explicit proof using `push_neg` and `obtain`.
- **`RequestProject/Paper/LinearAlgebraCore.lean`**: Replaced `grind +suggestions` in `rank_strata_equivariant` with a stable `ext`/`simp`/`constructor` proof that explicitly handles both directions of the set equality.

No `exact?` or `grind +suggestions` calls remain in the project.

## 3. Assumption Audit — `hsupp_ne_bot` Eliminated

**Result:** `hsupp_ne_bot : prymSupport x ≠ ⊥` **can** be proved from `x ≠ 0`, and has been.

Added the lemma `nonzero_tensor_support_ne_bot` in `LinearAlgebraCore.lean`:
```lean
lemma nonzero_tensor_support_ne_bot
    (x : V ⊗[ℂ] U) (hx : x ≠ 0) :
    prymSupport x ≠ ⊥
```

**Proof:** If `prymSupport x = ⊥`, all contractions `(id ⊗ f)(x) = 0` for every `f : U∨`. The canonical isomorphism `V ⊗ U ≃ Hom(U∨, V)` (built from `TensorProduct.comm`, `evalEquiv`, and `dualTensorHomEquiv`) then gives `x = 0`, contradicting `x ≠ 0`.

Both `full_prym_support` and `two_block_optimality_conditional` now derive `hsupp_ne_bot` internally from `hx_ne_zero` using this lemma. The `hsupp_ne_bot` hypothesis has been removed from both theorem statements.

## 4. Conditional Theorem Clarity

`two_block_optimality_conditional` still assumes:
- **`hstrata_trivial`**: Each pulled-back rank stratum Z_r(x) ⊂ P(V∨_ψ) is either empty or all of P(V∨_ψ). The argument that finite MCG-orbit of rank strata implies strata triviality is **NOT** fully formalized.
- **`hTx_nonzero`**: T_x(ℓ) ≠ 0 for ℓ ≠ 0. This is a consequence of injectivity (which IS formalized), but listed for transparency.

This is explicitly documented in the file header and docstrings.

## 5. Prym Convention Documentation

Corrected and standardized the convention comments in `ExternalInputs.lean`:
```
  E_ψ ≅ H₁(Σ; ℂ_{ψ⁻¹})    (Prym homology with ψ⁻¹-coefficients)
  E_ψ∨ ≅ H¹(Σ; ℂ_ψ) = V_ψ   (Prym cohomology with ψ-coefficients)
```

Explains that replacing ψ by ψ⁻¹ does not change the final projective Zariski-closure dichotomy PSp/PSL, since (ψ⁻¹)² = ψ⁻² = 1 ⟺ ψ² = 1.

## 6. External Inputs

- **`LooijengaInput`**: Kept as the named abstraction of the single-character projective closure / no finite-index invariant proper subspace consequence (Corollary 3.5).
- **Westwick bound**: Kept as external theorem (`sorry` in `ExternalInputs.lean`).

## Remaining External Assumptions

1. **`LooijengaInput`** (Corollary 3.5 / Proposition 3.4) — Looijenga 1997: no finite-index subgroup of H_ψ preserves a proper non-zero subspace of V_ψ.
2. **`westwick_bound`** (Theorem 7.1) — Westwick 1987: constant-rank subspace dimension bound.
3. **`weak_constant_rank_bound`** / **`weak_constant_rank_bound_abstract`** — consequences of Westwick.
4. **`hstrata_trivial`** (hypothesis) — rank strata triviality, from Looijenga applied to determinantal varieties.
5. **`hTx_nonzero`** (hypothesis) — contraction map non-degeneracy.
6. **Finite K-orbit data** (hypothesis `hstab`) — from finite MCG orbit + Lemma 4.2/4.3.

**This formalizes the linear-algebraic dependency skeleton and proves the final rank inequality conditional on named external inputs.**

# Summary of changes for run 492b4ff0-7b1a-4771-bb92-fc017f46a6b0
## Restructured formalization of "A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality"

The project has been completely restructured to honestly match the paper's logical dependency structure, separating external inputs from proved core results.

### File organization (4 logical layers)

1. **`Paper/Defs.lean`** — Core definitions (PrymData, TwoBlockData, contraction map, Prym support, rank strata)

2. **`Paper/ExternalInputs.lean`** — Named external assumptions:
   - `LooijengaInput` structure encoding Corollary 3.5 (no finite-index invariant proper subspace), with documentation of single-character projective closure (Prop 3.4) and the ψ vs ψ⁻¹ convention
   - `westwick_bound` (sorry) — Westwick 1987
   - `weak_constant_rank_bound` / `weak_constant_rank_bound_abstract` (sorry)

3. **`Paper/LinearAlgebraCore.lean`** — Fully proved linear-algebraic core (no sorry):
   - `support_K_invariant`, `support_equivariant` (Lemma 5.2)
   - `contraction_injective_of_full_support` (Corollary 5.5)
   - `rank_strata_K_invariant`, `rank_strata_equivariant` (Lemmas 6.2–6.3)
   - `constant_rank_from_finite_orbit` (Proposition 6.4)

4. **`Paper/MainTheorems.lean`** — Conditional main theorems:
   - `full_prym_support` (Proposition 5.4) — proved through the actual mechanism: finite K-orbit of x → K-invariance of support → H-equivariance of support → Looijenga no-invariant-subspace consequence → S(x) = V_ψ
   - `two_block_optimality_arithmetic_core` — assumes injectivity + Westwick
   - `two_block_optimality_conditional` — derives injectivity/constant rank from the formalized chain + named external inputs

5. **`Paper/Construction.lean`** — Section 2 results (block matrix identity, cocycle non-vanishing, infinite image, etc.), fully proved

### Removed vacuous declarations

The previous `conjugacy_iff_K_orbit` (proved `True := trivial`), `finite_MCG_orbit_gives_finite_K_orbit` (proved `Finset.finite_toSet`), and `no_finite_index_invariant_proper_subspace` (identity function on its hypothesis) have been removed. The previous `extension_class_zero_iff_finite_image` (only proved `x = 0 → contractionMapLin x = 0`) has been removed.

### Axiom audit

```
'two_block_optimality_arithmetic_core' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'two_block_optimality_conditional' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` in `two_block_optimality_conditional` comes exclusively from Westwick's theorem (1987), via `weak_constant_rank_bound_abstract`.

### Build output

`lake build RequestProject.Main` completes successfully (8031 jobs). All sorry instances are confined to `ExternalInputs.lean` (the three Westwick-related theorems).

### ARISTOTLE_SUMMARY.md

Updated to honestly state: "formalizes the linear-algebraic dependency skeleton and proves the final rank inequality conditional on named external inputs" — not "fully formalized".

# Summary of Formalization

## "A Rank (2g−1) Affine-Prym Construction and Its Two-Block Optimality"

This project formalizes the linear-algebraic dependency skeleton and proves
the final rank inequality conditional on named external inputs. It does NOT
claim to fully formalize surface topology, mapping class groups, twisted
cohomology, Looijenga's cyclic Prym image theorem, ordinary conjugacy
(Schur lemma for local systems), or Westwick's theorem.

### File structure

- **`RequestProject/Paper/Defs.lean`** — Core definitions (PrymData,
  TwoBlockData, contraction map, Prym support, rank strata)
- **`RequestProject/Paper/ExternalInputs.lean`** — Named external
  assumptions with full documentation:
  - `LooijengaInput` structure encoding Corollary 3.5 (no finite-index
    invariant proper subspace), derived from Looijenga 1997 + Proposition 3.4
  - `westwick_bound` (sorry) — Westwick 1987
  - `weak_constant_rank_bound` / `weak_constant_rank_bound_abstract` (sorry)
  - Documents the ψ vs ψ⁻¹ convention explicitly
- **`RequestProject/Paper/Construction.lean`** — Section 2, fully proved:
  block matrix identity, cocycle non-vanishing on kernel, infinite image,
  stabilizer invariance, finite character orbit
- **`RequestProject/Paper/LinearAlgebraCore.lean`** — Proved linear-algebraic
  core (no sorry):
  - `support_K_invariant` (Lemma 5.2, K-invariance)
  - `support_equivariant` (Lemma 5.2, H-equivariance)
  - `contraction_injective_of_full_support` (Corollary 5.5)
  - `rank_strata_K_invariant` (Lemma 6.2)
  - `rank_strata_equivariant` (Lemma 6.3)
  - `constant_rank_from_finite_orbit` (Proposition 6.4)
- **`RequestProject/Paper/MainTheorems.lean`** — Conditional main theorems:
  - `full_prym_support` (Proposition 5.4) — proved through the actual
    mechanism: finite K-orbit → K-invariance of support → H-equivariance
    of support → Looijenga no-invariant-subspace consequence
  - `two_block_optimality_arithmetic_core` — assumes injectivity and
    Westwick; fully proved (no sorry, no sorryAx)
  - `two_block_optimality_conditional` — derives injectivity/constant rank
    from the formalized dependency chain plus named external inputs;
    sorry only from Westwick via `weak_constant_rank_bound_abstract`

### Axiom audit

```
'two_block_optimality_arithmetic_core' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'two_block_optimality_conditional' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` in `two_block_optimality_conditional` comes exclusively from
`weak_constant_rank_bound_abstract` (Westwick's theorem, 1987).

### What is NOT formalized

- Surface topology, surface groups π₁(Σ_g), mapping class groups Mod(Σ_g)
- Twisted cohomology H¹(Σ_g; ℂ_ψ)
- Looijenga's cyclic Prym image theorem (1997) — enters as `LooijengaInput`
- Ordinary conjugacy / Schur lemma for non-isomorphic simple local systems
- Westwick's fixed-rank bound (1987) — enters as `sorry` in `ExternalInputs.lean`
- Projective algebraic geometry (Zariski closures, PSp/PSL actions)

### Build output

```
lake build RequestProject.Main
info: 'two_block_optimality_arithmetic_core' depends on axioms:
  [propext, Classical.choice, Quot.sound]
info: 'two_block_optimality_conditional' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
Build completed successfully
```
