# Erdős Problem 906 - sparse Fock series

This project contains a fixed explicit construction for Erdős Problem 906, its quantitative annular zero theory, and a Lean 4 formalization of the `p = 3/2` theorem package. Broader generalizations are kept separately in `research/` and are not part of the formalized submission.

## Paper and formalization

Main files:

- [`paper/paper_en.pdf`](paper/paper_en.pdf) - compiled manuscript.
- [`paper/paper_en.tex`](paper/paper_en.tex) - manuscript source.
- [`paper/PRIORITY_AND_SCOPE.md`](paper/PRIORITY_AND_SCOPE.md) - literature, priority, and scope notes.
- [`formalization/formalization_map.md`](formalization/formalization_map.md) - paper-to-Lean dependency map.
- [`formalization/FORMALIZATION_STATUS.md`](formalization/FORMALIZATION_STATUS.md) - machine-verification boundary.
- [`formalization/lean/`](formalization/lean/) - Lean 4 / Mathlib source.

The function studied in the formalized paper is

\[
F(z)=\sum_{j\ge1}\frac{z^{\lfloor j^{3/2}\rfloor}}{\sqrt{\lfloor j^{3/2}\rfloor!}}.
\]

The paper and Lean development establish:

- the cofinite zero-hitting property required by Erdős Problem 906;
- an `O(n^{-1/6})` covering rate on fixed annuli;
- exactly one simple zero in each admissible model disk;
- exhaustion of annular zeros by the model disks;
- eventual simplicity of all annular zeros;
- eventual pairwise disjointness of admissible model disks;
- exact distinct-zero counts on finite unions of model disks;
- the analytic and support-arithmetic statements used in the proof.

The printed proof and the Lean development use the same main chain: support arithmetic, discrete curvature, crossing radii, tail domination, local zero localization, annular exclusion, disjointness/counting, and annular covering.

To build the formalization:

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

## Research extensions

The [`research/`](research/) directory contains work beyond the fixed `p = 3/2` submission, including general sparse-support regimes, limiting zero distributions, support-profile questions, and related extensions. These notes have varying status and are not part of the machine-checked theorem package unless stated otherwise.

## Scope and priority

No first-solution priority is claimed for Erdős Problem 906. The project instead records a fixed explicit sparse construction and its quantitative zero localization. Historical and literature details are given in [`paper/PRIORITY_AND_SCOPE.md`](paper/PRIORITY_AND_SCOPE.md).

## AI assistance

AI tools were used during parts of the derivation, checking, exposition, repository preparation, and formalization. Mathematical claims should be judged from the paper, source code, and stated verification boundary.
