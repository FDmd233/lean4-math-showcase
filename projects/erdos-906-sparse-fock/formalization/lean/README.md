# `p=3/2` Lean formalization

This Lake project contains the Lean 4 / Mathlib source accompanying *Zeros of high derivatives of sparse Fock series* for the fixed parameter `p=3/2`.

The code proves the cofinite theorem together with the annular zero-geometry statements used in the paper. Broader general-`p` results and endpoint questions are kept in the research archive and are not part of this formalized theorem package.

## Build

```bash
lake build RequestProject.Main
```

The project is pinned to Lean/mathlib `v4.28.0`.

## Main declarations

`RequestProject/Main.lean` imports the development and prints the axiom dependencies of:

- `SparseFock.annular_covering_rate_p32`
- `SparseFock.erdos906_sparse_fock_p32`
- `SparseFock.model_disk_zero_count_one_p32`
- `SparseFock.annular_zero_exclusion_p32`
- `SparseFock.annular_zeros_simple_p32`
- `SparseFock.annular_zeros_simple_deriv_p32`
- `SparseFock.model_disks_pairwise_disjoint_p32`
- `SparseFock.zero_count_model_disk_union_p32`

## File guide

The early files (`Support`, `Curvature`, `Growth`, `Fock`, `Radii`) set up the sparse series and its weights. `Tail`, `TwoTerm`, and `ModelDisk` develop the local two-term picture. `Covering32` proves the annular covering rate. `Exclusion`, `Annulus`, `Simplicity`, `Disjoint`, and `ZeroCountUnion` give the fixed-annulus classification.

For the paper-to-code correspondence and the formalization boundary, see `../formalization_map.md` and `../FORMALIZATION_STATUS.md`.

## Scope

The source does not formalize the general `4/3<p<2` theory, the critical `p=4/3` compactness argument, sector asymptotics, limiting zero measures, or the exact lower growth estimate. Those topics belong to the research archive rather than the fixed `p=3/2` paper.

## Preparation note

AI-assisted tools, including formalization tools, were used during development. The public Lean source and its stated axiom dependencies are the basis for checking the formal claims.
