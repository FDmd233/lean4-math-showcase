# Research extension - not part of the formalized submission

This directory is deliberately separate from `../paper/` and `../formalization/`.

The canonical website submission is the fixed `p = 3/2` paper in `../paper/`, together with the Lean development in `../formalization/`. Nothing in this directory is used as a premise of that submission, and nothing here should be read as machine verified merely because it is public in the repository.

## Status vocabulary

To keep the public record unambiguous, this directory uses the following distinctions.

- **Formalized submission** means a statement appears in the canonical `p = 3/2` paper and has a corresponding Lean declaration in `../formalization/lean/RequestProject/`.
- **Manuscript-level result** means a paper proof has been written and audited within the project, but the statement is not part of the canonical Lean-checked submission and has not been independently refereed.
- **Research candidate** means there is a coherent proof architecture or substantial partial proof, but the final statement, hypotheses, constants, or literature position are still under audit.
- **Open** means a genuine proof obligation remains.

Only the first category is claimed as machine checked in this repository.

## Archived general-parameter manuscript

Before the scope split, the project studied

\[
F_p(z)=\sum_{j\ge1}\frac{z^{\lfloor j^p\rfloor}}{\sqrt{\lfloor j^p\rfloor!}},
\qquad \frac43\le p<2.
\]

The pre-split manuscript is preserved in repository history, including at commit

`d23fed4692bd04195555d9f176a2ca31e6405918`.

That manuscript contains paper-level arguments for a broader parameter range than the canonical submission, including the noncritical two-term regime and a critical `p = 4/3` compactness argument. Those statements are research material, not part of the current website-submission theorem package and not all are represented in Lean.

## Current macroscopic research direction

The strongest current extension studies high derivatives through normalized logarithmic potentials and the geometry of the active Taylor support.

For the original sparse Fock normalization, the main paper-level target is a phase-independent macroscopic zero law in which a scaled active support profile determines a radial limiting potential and hence a limiting zero measure. The power-support family `nu_j = floor(j^p)` is expected to give the same two-dimensional zero sea throughout `1 < p < 2`, with the Erdős-906 cofinite property as a corollary.

This direction is substantially more general than the canonical `p = 3/2` submission, but it is **not** presently part of the formalized theorem package. The general statement is being kept outside `../paper/` until its hypotheses, proof, and literature position are frozen.

A related convex/Riesz description associates gaps in a limiting support profile with circular components of the limiting zero measure. In the factorially normalized model, the crossing radius is expressed by the identric mean of the gap endpoints. This is a research-level structural consequence of the support-profile framework, not a claim of the canonical submission.

## Broader extensions under audit

Several stronger formulations are being investigated. They include:

- weakening global gap assumptions to local mesoscopic sparsity conditions in the active derivative window;
- extensions from the Fock exponent `1/2` to more general Le Roy-type factorial normalizations;
- realization and inverse questions for limiting support profiles and radial zero measures;
- the macroscopic boundary between a two-dimensional zero sea, radial circle-type limits, and zero escape.

These are **active research candidates**. Their exact optimal hypotheses and their overlap with classical Fabry-gap, Wiman-Valiron, lacunary-entire-function, Turán-Nazarov, and modern coefficient-profile zero-distribution theory are still being audited. They should not be cited from this README as established theorems.

## Microscopic research direction

The finer zero geometry is a separate layer.

- For the direct two-term regime, the project has detailed manuscript arguments based on adjacent-term dominance and local zero localization.
- At `p = 4/3`, the archived manuscript develops a bilateral-Gaussian compactness mechanism.
- In the subcritical regime `1 < p < 4/3`, a dual Poisson/Stokes picture is under investigation.

The last item remains **open** at the level needed for a full sharp microscopic phase diagram. In particular, the required uniform steepest-descent / Poisson-summation control has not been promoted to a theorem.

## What is not being claimed here

This directory does **not** currently claim that:

- every statement discussed here has been formalized;
- the general `1 < p < 2` theory is part of the website submission;
- the support-profile, identric-mean, Le Roy, mesoscopic-sparsity, or phase-diagram extensions have completed external peer review;
- any proposed sparsity threshold is already proved optimal in the strongest possible formulation;
- this project has priority over all classical or modern work on lacunary entire functions, coefficient profiles, repeated differentiation, or zero distributions;
- the microscopic dual-Stokes regime is complete.

The purpose of this separation is precisely to prevent promising research extensions from being conflated with the fixed, auditable `p = 3/2` result.

## Promotion rule for the canonical submission

A statement is added to the canonical formalized submission only after all of the following hold:

1. the mathematical proof has been line-audited;
2. the manuscript statement has stable quantifiers and constants;
3. a corresponding Lean declaration is present;
4. `lake build RequestProject.Main` succeeds on the exact commit;
5. the paper-to-Lean map and the literature/scope audit are updated.

Separate future research papers may have a different publication workflow, but they should not be described as part of the canonical website submission unless this promotion rule is satisfied.
