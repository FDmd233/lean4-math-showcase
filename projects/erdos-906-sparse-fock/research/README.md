# Research extension - not part of the formalized submission

This directory is deliberately separate from `../paper/` and `../formalization/`.

The canonical website submission is the `p = 3/2` paper in `../paper/`, together with the Lean development in `../formalization/`. Nothing in this directory is used as a premise of that submission.

## Archived general-parameter manuscript

The broader manuscript preceding the scope split studied

\[
F_p(z)=\sum_{j\ge1}\frac{z^{\lfloor j^p\rfloor}}{\sqrt{\lfloor j^p\rfloor!}},
\qquad 4/3\le p<2,
\]

including results and arguments that are not all present in the current Lean project. Its mathematical content is preserved in the repository history and may be reintroduced here as a research artifact, but it is not the website-submission paper.

## Current research directions

The active research program includes, at varying levels of completion:

- extension of the sparse-Fock zero geometry beyond `p = 3/2`;
- the critical `p = 4/3` bilateral-Gaussian compactness theory;
- the subcritical `1 < p < 4/3` regime;
- mesoscopic-gap and support-profile universality questions;
- the `p = 2` sea-to-circle-crystal boundary behavior;
- microscopic direct / self-dual / dual phase-transition mechanisms.

These items are research targets, not claims of the formalized submission. Some have detailed proofs or proof skeletons in working notes, but their status must be assessed individually before publication.

## Promotion rule

A research statement is promoted into the canonical submission only after all of the following hold:

1. the mathematical proof is line-audited;
2. the manuscript statement has stable quantifiers and constants;
3. a corresponding Lean declaration is present;
4. `lake build RequestProject.Main` succeeds on the exact commit;
5. the paper-to-Lean map and the literature-scope file are updated.

This rule is intended to prevent manuscript-only extensions from being conflated with machine-checked claims.
