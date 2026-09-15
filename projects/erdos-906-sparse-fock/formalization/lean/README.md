This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# `p=3/2` Lean formalization

This Lake project contains the published Lean 4 / Mathlib source for the `p=3/2` part of *Zeros of high derivatives of sparse Fock series*.

I have tried to keep the boundary straightforward: the code proves the cofinite theorem and a substantial amount of the annular zero geometry, while the general `p` range and the critical endpoint remain in the manuscript.

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

The early files (`Support`, `Curvature`, `Growth`, `Fock`, `Radii`) set up the sparse series and its weights. `Tail`, `TwoTerm`, and `ModelDisk` develop the local two-term picture. `Covering32` proves the annular covering rate. `Exclusion`, `Annulus`, `Simplicity`, `Disjoint`, and `ZeroCountUnion` give the stronger fixed-annulus classification.

For the paper-to-code correspondence and the remaining gaps, see `../formalization_map.md` and `../FORMALIZATION_STATUS.md`.

## Scope

The source does not formalize the general `4/3<p<2` theorem, the `p=4/3` compactness argument, the sector asymptotic, the limiting zero measure, or the exact lower growth estimate. I prefer to leave those gaps explicit rather than suggest that the whole manuscript is already machine-checked.
