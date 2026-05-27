# Affine-Prym scalar two-block optimality formalization

This is a standalone Lean 4 project associated with the paper:

> **A Rank (2g-1) Affine-Prym Construction and Its Scalar Two-Block Optimality**

It is kept separate from the top-level showcase project because it uses Lean/mathlib `v4.28.0`, while the root project uses a different toolchain.

## Build

From this directory:

```bash
lake build RequestProject.Main
```

The original build output is preserved in [`BUILD_OUTPUT.txt`](BUILD_OUTPUT.txt).

## Layout

```text
.
|-- lakefile.toml
|-- lean-toolchain
|-- lake-manifest.json
|-- RequestProject/
|   |-- Main.lean
|   `-- Paper/
|       |-- Defs.lean
|       |-- ExternalInputs.lean
|       |-- Construction.lean
|       |-- LinearAlgebraCore.lean
|       `-- MainTheorems.lean
|-- ARISTOTLE_SUMMARY.md
|-- BUILD_OUTPUT.txt
`-- paper.pdf
```

## Formalization status

This is not a full formalization of the whole paper. The Lean files formalize the linear-algebraic dependency skeleton and prove the final rank inequality conditional on named external inputs.

In particular:

- `two_block_optimality_arithmetic_core` has no `sorryAx` dependency in the recorded axiom audit.
- `two_block_optimality_conditional` depends on `sorryAx` only through the Westwick-related external theorem wrappers in `ExternalInputs.lean`.
- Looijenga's Prym image theorem, surface topology, mapping class groups, twisted cohomology, ordinary conjugacy, and Westwick's theorem are recorded as external inputs rather than formalized here.

See [`ARISTOTLE_SUMMARY.md`](ARISTOTLE_SUMMARY.md) for the detailed summary and axiom audit.

## Main Lean files

- `RequestProject/Paper/Defs.lean` -- abstract Prym/two-block data, contraction map, Prym support, and rank strata.
- `RequestProject/Paper/ExternalInputs.lean` -- named external assumptions, including the Looijenga input and Westwick bound wrappers.
- `RequestProject/Paper/Construction.lean` -- formalized construction ingredients.
- `RequestProject/Paper/LinearAlgebraCore.lean` -- the support and rank-strata linear algebra core.
- `RequestProject/Paper/MainTheorems.lean` -- the conditional theorem chain and final rank inequality.

## Provenance

The initial formalization was prepared with Aristotle. The generated summary and build record are kept in the repository for reproducibility.