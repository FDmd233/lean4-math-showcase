# Erdős Problem 906: sparse Fock construction

This directory contains the public research version of **Zhijie He's** work on an explicit deterministic construction for the cofinite formulation of Erdős Problem #906.

The central family is

\[
F_p(z)=\sum_{j\ge 1}\frac{z^{\lfloor j^p\rfloor}}{\sqrt{\lfloor j^p\rfloor!}},
\qquad \frac43\le p<2.
\]

The manuscript proves that these functions are transcendental entire functions of order 2 and type \(1/2\), and that every nonempty open set contains a zero of every sufficiently high derivative. For \(p>4/3\), it also studies the complete zero geometry on fixed annuli, including localization near explicit circular grids, sharp covering scales, eventual simplicity away from the origin, counting asymptotics, and a limiting zero measure. The endpoint \(p=4/3\) is treated separately by a compactness argument for bilateral Gaussian series.

## Files

- [`paper/paper_en.pdf`](paper/paper_en.pdf): compiled English research manuscript.
- [`paper/paper_en.tex`](paper/paper_en.tex): manuscript source.
- [`paper/PRIORITY_AND_SCOPE.md`](paper/PRIORITY_AND_SCOPE.md): publication/priority boundary and comparison with earlier work.
- [`formalization/formalization_map.md`](formalization/formalization_map.md): theorem-by-theorem proof dependency map.
- [`formalization/FORMALIZATION_STATUS.md`](formalization/FORMALIZATION_STATUS.md): independent static audit/status note.
- [`formalization/lean/`](formalization/lean/): full Aristotle Round 4 Lean 4 / Mathlib source tree for the \(p=3/2\) formalization.

The undergraduate thesis and thesis-specific Chinese exposition are intentionally **not** included in this public directory.

## Status and priority

This repository does **not** claim the first solution of Erdős Problem #906. Earlier probabilistic constructions exist, including Eric Hou's work. The intended contribution here is the explicit deterministic sparse-Fock construction and the additional quantitative zero geometry.

## Formalization

For the concrete case \(p=3/2\), the published Round 4 source contains 35 `.lean` files and 6727 lines under `RequestProject/`. Its main entry point is [`formalization/lean/RequestProject/Main.lean`](formalization/lean/RequestProject/Main.lean). It records theorem statements including:

- `erdos906_sparse_fock_p32`
- `annular_covering_rate_p32`
- `model_disk_zero_count_one_p32`
- `annular_zero_exclusion_p32`
- `annular_zeros_simple_p32`
- `annular_zeros_simple_deriv_p32`
- `model_disks_pairwise_disjoint_p32`
- `zero_count_model_disk_union_p32`

The source uses Lean/mathlib `v4.28.0`. From the Lean project directory, the intended build command is:

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

The supplied Aristotle report records a clean build. During publication, the source archive was independently checked against its SHA-256 digest, and the imported tree was checked for the expected 35 Lean files / 6727 lines and for the absence of `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, and `@[implemented_by]` in `RequestProject/`. That publication import did **not** independently rerun Lake, so the distinction between the supplied build report and the publication-time static integrity check is intentional.

The general \(4/3<p<2\) structural theorem, the critical \(p=4/3\) analysis, the sector-count asymptotic, limiting zero measure, and the exact order/type lower bound are manuscript results and are not claimed to be fully Lean-formalized here.

## AI assistance disclosure

Language-model tools were used substantially during derivation, checking, exposition, and formalization. The manuscript separates mathematical claims from priority claims, and the formalization status file distinguishes machine-checked portions from manuscript-only results.

## Citation / discussion

This material is intended for mathematical review, including discussion on the Erdős Problems website. In particular, feedback on the global tail-domination/Rouché argument and on possible overlap with older lacunary-entire-function literature is welcome.
