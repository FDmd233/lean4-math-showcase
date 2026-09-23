# Affine-Prym scalar two-block formalization

This Lean 4 project records the linear-algebraic formalization developed from an earlier Affine-Prym argument. It is maintained as a separate Lake project because it uses Lean/mathlib `v4.28.0`, while the examples at the repository root use a different toolchain.

The project isolates the linear-algebraic core from the topological and representation-theoretic inputs that remain external.

## Build

From this directory:

```bash
lake build RequestProject.Main
```

The recorded build output is in [`BUILD_OUTPUT.txt`](BUILD_OUTPUT.txt).

## What is formalized

The project proves the linear-algebraic chain leading to the rank inequality, conditional on named external inputs. In particular:

- `two_block_optimality_arithmetic_core` has no `sorryAx` dependency in the recorded axiom audit;
- `two_block_optimality_conditional` reaches the final rank inequality but inherits `sorryAx` through the Westwick wrappers in `ExternalInputs.lean`;
- the support, contraction-map, rank-strata, and finite-orbit linear algebra is proved in the project itself.

This is a dependency-level formalization, not a full formalization of the surrounding topology and representation theory. Surface topology, mapping class groups, twisted cohomology, Looijenga's Prym image theorem, ordinary conjugacy, projective algebraic geometry, and Westwick's theorem remain external to this Lean development.

See [`FORMALIZATION_NOTES.md`](FORMALIZATION_NOTES.md) for the precise boundary.

## Main files

- `RequestProject/Paper/Defs.lean` - abstract Prym/two-block data, contraction map, Prym support, and rank strata.
- `RequestProject/Paper/ExternalInputs.lean` - Looijenga and Westwick inputs, with their mathematical role stated explicitly.
- `RequestProject/Paper/Construction.lean` - the algebraic part of the affine-Prym construction.
- `RequestProject/Paper/LinearAlgebraCore.lean` - the proved support and rank-strata core.
- `RequestProject/Paper/MainTheorems.lean` - the conditional theorem chain and final rank inequality.

## Preparation note

The initial development used Aristotle as a formalization assistant. The public Lean source and recorded build output are retained so that the resulting formalization can be inspected independently.
