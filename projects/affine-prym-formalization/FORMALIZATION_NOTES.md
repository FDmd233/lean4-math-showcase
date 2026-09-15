# Formalization notes

This note records the current mathematical boundary of the Affine-Prym Lean project and its remaining external inputs.

## Build and axiom audit

The recorded command

```bash
lake build RequestProject.Main
```

completed successfully with 8031 jobs. The stored axiom audit reports:

```text
'two_block_optimality_arithmetic_core' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'two_block_optimality_conditional' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` in the conditional theorem comes through the Westwick-related declarations in `ExternalInputs.lean`. The arithmetic core itself is proved without `sorryAx`.

## Proved inside Lean

The development includes the following parts of the paper's dependency chain:

- nonzero tensors have nontrivial Prym support;
- support is invariant/equivariant under the stated linear actions;
- full support implies injectivity of the contraction map;
- rank strata are invariant/equivariant;
- the finite-orbit hypothesis gives the constant-rank conclusion used in the final argument;
- the arithmetic step from the constant-rank bound to `m + n >= 2g - 1` is proved.

The theorem `two_block_optimality_conditional` packages this chain together with the named external inputs.

## External or conditional input

The following material is not formalized here:

- surface topology and surface groups;
- mapping class groups and twisted cohomology;
- Looijenga's cyclic Prym image theorem and the projective Zariski-closure argument;
- ordinary conjugacy / Schur-lemma input for local systems;
- Westwick's fixed-rank theorem;
- the geometric step turning finite mapping-class-group orbit information into the rank-strata hypothesis used by the conditional theorem.

`LooijengaInput` records the irreducibility consequence needed by the linear-algebra argument. Westwick's theorem enters through the declarations in `ExternalInputs.lean` that carry `sorry`.

## Reading the result

I think the cleanest way to read this project is as a dependency audit, not as a claim that the whole paper has been machine-checked. The useful point is that the final linear-algebraic reduction is explicit, and the remaining external mathematics is named in the theorem statements rather than absorbed into undocumented assumptions.
