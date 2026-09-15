# Formalization status

Current source snapshot: September 13, 2026.

## Theorems present in the published `p=3/2` project

The Lean source contains the following principal declarations:

- `erdos906_sparse_fock_p32`
- `annular_covering_rate_p32`
- `model_disk_zero_count_one_p32`
- `annular_zero_exclusion_p32`
- `annular_zeros_simple_p32`
- `annular_zeros_simple_deriv_p32`
- `model_disks_pairwise_disjoint_p32`
- `zero_count_model_disk_union_p32`

There are 35 `.lean` files and 6727 lines under `RequestProject/`.

## Integrity and build status

The publication import checked the source archive against its SHA-256 digest, then checked the imported tree for the expected file/line counts and for the absence of `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, and `@[implemented_by]` in `RequestProject/`.

The supplied build record reports a clean `lake build` and reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for the principal declarations printed by `RequestProject/Main.lean`. I keep a distinction between that supplied clean-build record and the publication-time static integrity scan; the latter did not independently rerun Lake.

## What the `p=3/2` layer establishes

For sufficiently high derivatives on a fixed annulus, the formalized structure includes:

- existence of the expected model-disk zero;
- uniqueness and simplicity of that zero;
- exclusion of additional annular zeros outside the model disks;
- pairwise disjointness of the relevant disks;
- exact counts of **distinct** zeros on finite unions of model disks;
- the cofinite zero-hitting statement for Erdős #906;
- the quantitative annular covering rate `n^{-1/6}`.

`zero_count_model_disk_union_p32` uses `Set.ncard`, so its count is a distinct-point count rather than a divisor-valued multiplicity count. This is compatible with the simplicity theorem, but multiplicity is not encoded there as a separate divisor object.

## Manuscript results not yet formalized

The following remain outside the published Lean development:

- the sector zero-count asymptotic;
- the limiting zero measure;
- the full structural theorem for general `4/3 < p < 2`;
- the critical `p=4/3` compactness argument;
- the lower growth bound needed for exact order two and exact type `1/2`.

For a proof-by-proof map, see [`formalization_map.md`](formalization_map.md).
