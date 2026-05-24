# Affine-Prym scalar two-block optimality formalization

This directory contains the Aristotle-generated Lean 4 formalization associated
with the paper:

> **A Rank (2g-1) Affine-Prym Construction and Its Scalar Two-Block Optimality**

The code is stored as a **standalone Lake project** because it uses
Lean/mathlib `v4.28.0`, while the top-level showcase project currently uses a
different Lean/mathlib version.

## Build

From this directory:

```bash
lake build RequestProject.Main
```

The original Aristotle build log is preserved in [`BUILD_OUTPUT.txt`](BUILD_OUTPUT.txt).

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

This is not a full formalization of the whole paper. It formalizes the
linear-algebraic dependency skeleton and proves the final rank inequality
conditional on named external inputs.

In particular:

- `two_block_optimality_arithmetic_core` has no `sorryAx` dependency in the
  recorded axiom audit.
- `two_block_optimality_conditional` depends on `sorryAx` only through the
  Westwick-related external theorem wrappers in `ExternalInputs.lean`.
- Looijenga's Prym image theorem, surface topology, mapping class groups,
  twisted cohomology, ordinary conjugacy, and Westwick's theorem are documented
  as external/non-formalized inputs.

See [`ARISTOTLE_SUMMARY.md`](ARISTOTLE_SUMMARY.md) for the detailed Aristotle
summary and axiom audit.

## Main Lean files

- `RequestProject/Paper/Defs.lean` -- abstract Prym/two-block data,
  contraction map, Prym support, rank strata.
- `RequestProject/Paper/ExternalInputs.lean` -- named external assumptions,
  including the Looijenga input and Westwick bound wrappers.
- `RequestProject/Paper/Construction.lean` -- formalized Section 2 construction
  ingredients.
- `RequestProject/Paper/LinearAlgebraCore.lean` -- proved support/rank-strata
  linear algebra core.
- `RequestProject/Paper/MainTheorems.lean` -- conditional main theorem chain
  and final rank inequality.

## Attribution

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

Suggested citation/attribution from the generated project:

- Tag `@Aristotle-Harmonic` on related GitHub PRs/issues when appropriate.
- Add commit co-author line when committing Aristotle-generated code:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
