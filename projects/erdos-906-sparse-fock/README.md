# Erdős Problem 906: sparse Fock construction

This directory contains the public research version of **Zhijie He's** work on an explicit deterministic construction for the cofinite formulation of Erdős Problem #906.

The central family is

\[
F_p(z)=\sum_{j\ge 1}\frac{z^{\lfloor j^p\rfloor}}{\sqrt{\lfloor j^p\rfloor!}},
\qquad \frac43\le p<2.
\]

The manuscript proves that these functions are transcendental entire functions of order 2 and type \(1/2\), and that every nonempty open set contains a zero of every sufficiently high derivative. For \(p>4/3\), it also studies the complete zero geometry on fixed annuli, including localization near explicit circular grids, sharp covering scales, eventual simplicity away from the origin, counting asymptotics, and a limiting zero measure. The endpoint \(p=4/3\) is treated separately by a compactness argument for bilateral Gaussian series.

## Files

- [`paper/paper_en.tex`](paper/paper_en.tex): English research manuscript source.
- `paper/paper_en.pdf`: compiled manuscript when available from the repository build workflow.
- [`paper/PRIORITY_AND_SCOPE.md`](paper/PRIORITY_AND_SCOPE.md): publication/priority boundary and comparison with earlier work.
- [`formalization/formalization_map.md`](formalization/formalization_map.md): theorem-by-theorem proof dependency map.
- [`formalization/FORMALIZATION_STATUS.md`](formalization/FORMALIZATION_STATUS.md): current status of the Aristotle/Lean development.

The undergraduate thesis and thesis-specific Chinese exposition are intentionally **not** included in this public directory.

## Status and priority

This repository does **not** claim the first solution of Erdős Problem #906. Earlier probabilistic constructions exist, including Eric Hou's work. The intended contribution here is the explicit deterministic sparse-Fock construction and the additional quantitative zero geometry.

## Formalization

For the concrete case \(p=3/2\), an Aristotle-generated Lean 4 / Mathlib development has reached the cofinite #906 conclusion and substantial annular zero-structure statements. The latest static audit reports no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or `@[implemented_by]` in the supplied project, and records theorem statements including:

- `erdos906_sparse_fock_p32`
- `annular_covering_rate_p32`
- `model_disk_zero_count_one_p32`
- `annular_zero_exclusion_p32`
- `annular_zeros_simple_p32`
- `annular_zeros_simple_deriv_p32`
- `model_disks_pairwise_disjoint_p32`
- `zero_count_model_disk_union_p32`

The full Lean source archive is not yet present in this GitHub directory because the current ChatGPT GitHub connector could not export the original Project-file archive bytes. The status document records exactly what was audited; the source tree should be added verbatim from the latest Aristotle Round 4 archive rather than reconstructed or replaced by placeholders.

## AI assistance disclosure

Language-model tools were used substantially during derivation, checking, exposition, and formalization. The manuscript separates mathematical claims from priority claims, and the formalization status file distinguishes machine-checked portions from manuscript-only results.

## Citation / discussion

This material is intended for mathematical review, including discussion on the Erdős Problems website. In particular, feedback on the global tail-domination/Rouché argument and on possible overlap with older lacunary-entire-function literature is welcome.
