# Affine-Prym scalar two-block formalization

This is the Lean 4 companion to *A Rank (2g-1) Affine-Prym Construction and Its Scalar Two-Block Optimality*. I keep it as a separate Lake project because it uses Lean/mathlib `v4.28.0`, while the small examples at the repository root use another toolchain.

What I find useful here is the dependency boundary: the linear-algebraic core is visible in Lean, while the genuinely external topology and representation-theoretic input is named rather than hidden.

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

I do **not** regard this as a full formalization of the paper. Surface topology, mapping class groups, twisted cohomology, Looijenga's Prym image theorem, ordinary conjugacy, projective algebraic geometry, and Westwick's theorem remain external to this Lean development.

See [`FORMALIZATION_NOTES.md`](FORMALIZATION_NOTES.md) for the exact boundary.

## Main files

- `RequestProject/Paper/Defs.lean` - abstract Prym/two-block data, contraction map, Prym support, and rank strata.
- `RequestProject/Paper/ExternalInputs.lean` - Looijenga and Westwick inputs, with their mathematical role stated explicitly.
- `RequestProject/Paper/Construction.lean` - the algebraic part of the affine-Prym construction.
- `RequestProject/Paper/LinearAlgebraCore.lean` - the proved support and rank-strata core.
- `RequestProject/Paper/MainTheorems.lean` - the conditional theorem chain and final rank inequality.

## Assistance

AI-assisted tools were used during development of the formalization. Its mathematical status is determined by the source, the explicit external assumptions, and the axiom/build audit above.
