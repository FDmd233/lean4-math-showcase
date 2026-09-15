# Erdős Problem 906 - sparse Fock series

This directory is the public version of my work on an explicit deterministic construction for the cofinite form of Erdős Problem #906. The family is

\[
F_p(z)=\sum_{j\ge 1}\frac{z^{\lfloor j^p\rfloor}}{\sqrt{\lfloor j^p\rfloor!}},
\qquad \frac43\le p<2.
\]

What I find most useful about the construction is not the existence statement by itself, but the fact that the derivative zeros can be followed rather explicitly. For `p>4/3` the paper obtains annular zero localization near circular grids, sharp covering scales, eventual simplicity away from the origin, counting asymptotics, and a limiting zero measure. The endpoint `p=4/3` is less explicit and is handled by a compactness argument.

## Files

- [`paper/paper_en.pdf`](paper/paper_en.pdf) - compiled English manuscript.
- [`paper/paper_en.tex`](paper/paper_en.tex) - manuscript source.
- [`paper/PRIORITY_AND_SCOPE.md`](paper/PRIORITY_AND_SCOPE.md) - what is and is not being claimed about priority.
- [`formalization/formalization_map.md`](formalization/formalization_map.md) - proof-to-Lean dependency map.
- [`formalization/FORMALIZATION_STATUS.md`](formalization/FORMALIZATION_STATUS.md) - current formalization boundary.
- [`formalization/lean/`](formalization/lean/) - the published `p=3/2` Lean 4 / Mathlib source.

The Chinese undergraduate thesis and defense material are intentionally not part of this public directory.

## Scope and priority

I do **not** claim the first solution of Erdős #906. Earlier probabilistic constructions exist, including Eric Hou's work. My narrower claim is that the paper gives an explicit deterministic sparse-Fock construction and develops additional quantitative zero geometry. I also avoid a historical-priority claim for the sparse construction until the older lacunary-entire-function literature has been checked more completely.

## Lean formalization

The `p=3/2` source contains 35 `.lean` files and 6727 lines under `RequestProject/`. The main entry point is [`formalization/lean/RequestProject/Main.lean`](formalization/lean/RequestProject/Main.lean), which prints the axiom dependencies of the principal theorems.

The formalized layer includes the cofinite theorem, the `n^{-1/6}` annular covering rate, unique simple zeros in admissible model disks, exclusion of extra annular zeros, eventual annular simplicity, disjointness of the model disks, and exact distinct-zero counts on finite unions of such disks. The general `4/3<p<2` structural theorem, the `p=4/3` compactness argument, the sector asymptotic, limiting zero measure, and the exact lower growth estimate are still manuscript-only.

The project uses Lean/mathlib `v4.28.0`. From the Lean directory:

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

## AI assistance

I used language-model tools substantially during exploration, proof checking, exposition, and formalization; the first Lean formalization pass also used Aristotle. I keep this disclosure explicit, but I do not treat tool output as evidence of correctness. The mathematical claims are meant to stand or fall with the written proofs, the Lean source where available, and independent checking.
