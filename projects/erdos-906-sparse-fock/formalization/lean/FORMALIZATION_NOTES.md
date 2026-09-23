# Lean notes for the `p=3/2` development

This note records what the current source proves and where the formalization boundary lies.

## Core theorem

`SparseFock.erdos906_sparse_fock_p32` has the cofinite quantifier required by Erdős #906:

```lean
theorem erdos906_sparse_fock_p32 (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z ∈ U, iteratedDeriv n (F (3/2)) z = 0
```

The formalized function is the sparse series with support `nu (3/2) j = floor(j^(3/2))` and coefficients `1 / sqrt(k!)` on that support.

## Annular structure

For fixed annuli and sufficiently high derivatives, the project also proves:

- the quantitative `n^{-1/6}` covering rate;
- exactly one simple zero in each admissible model disk;
- exclusion of additional annular zeros;
- eventual simplicity of all annular zeros;
- pairwise disjointness of the model disks;
- exact distinct-zero counts on finite unions of model disks.

The uniqueness/simplicity argument is proved directly from analytic estimates in `ZeroCount.lean`; it does not depend on a formal Rouché theorem in Mathlib.

## Axiom and integrity checks

`RequestProject/Main.lean` prints the axioms of the main declarations. The supplied build record reports only `propext`, `Classical.choice`, and `Quot.sound` for those declarations. The public source contains no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or `@[implemented_by]` under `RequestProject/`.

## Outside the formalized scope

The Lean project does not contain the sector-count asymptotic, limiting zero measure, general `4/3<p<2` structural results, the critical `p=4/3` compactness argument, or the lower growth bound giving exact order/type. These topics are retained as research material and are not claims of the current formalization.
