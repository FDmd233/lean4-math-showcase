# Erdős Problem 906 - sparse Fock series

This project is deliberately split into two independent parts. The separation is part of the mathematical quality control: the website-submission paper contains only statements backed by the published Lean development, while broader research is kept outside the submission tree.

## Part I - fully formalized website submission

Canonical submission files:

- [`paper/paper_en.pdf`](paper/paper_en.pdf) - compiled submission manuscript.
- [`paper/paper_en.tex`](paper/paper_en.tex) - authoritative manuscript source.
- [`paper/PAGE_BY_PAGE_GUIDE.md`](paper/PAGE_BY_PAGE_GUIDE.md) - page-level proof guide.
- [`paper/PRIORITY_AND_SCOPE.md`](paper/PRIORITY_AND_SCOPE.md) - citation, priority, and scope audit.
- [`paper/REFEREE_AUDIT.md`](paper/REFEREE_AUDIT.md) - mathematical and expository release audit.
- [`paper/RELEASE_CHECKLIST.md`](paper/RELEASE_CHECKLIST.md) - exact publication checklist and recommended website post.
- [`formalization/formalization_map.md`](formalization/formalization_map.md) - paper-to-Lean dependency map.
- [`formalization/FORMALIZATION_STATUS.md`](formalization/FORMALIZATION_STATUS.md) - precise machine-verification boundary.
- [`formalization/lean/`](formalization/lean/) - Lean 4 / Mathlib source.

The submitted function is fixed once and for all as

\[
F(z)=\sum_{j\ge1}\frac{z^{\lfloor j^{3/2}\rfloor}}{\sqrt{\lfloor j^{3/2}\rfloor!}}.
\]

The formalized submission proves:

- the cofinite zero-hitting property required by Erdős Problem 906;
- the quantitative annular covering rate `O(n^{-1/6})`;
- exactly one simple zero in every admissible model disk;
- exhaustion of all zeros on a fixed annulus by model disks;
- eventual simplicity of all annular zeros;
- eventual pairwise disjointness of admissible model disks;
- exact distinct-zero counts on finite unions of admissible model disks;
- the entire-function, derivative-series, transcendence, upper-growth, and origin-multiplicity facts used by the paper.

The printed proof follows the same structural chain as the Lean development. In particular, the final paper retains the exact polynomial factor in the formal tail estimate, uses the same minimum-modulus existence mechanism, the same Cauchy-error uniqueness/simplicity mechanism, and the same three-case annular exclusion argument.

The principal declarations are audited in `RequestProject/Main.lean` with `#print axioms`.

From the Lean project directory:

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

The CI workflow performs a static scan for proof escapes before building the Lean project. The paper workflow compiles the manuscript and rejects undefined references/citations, LaTeX errors, and overfull horizontal boxes before updating the checked-in PDF.

## Part II - research extension, not part of the submission

The [`research/`](research/) directory contains broader mathematical work that is intentionally **not** used to support the formalized submission. It includes the earlier general-parameter manuscript and status notes on subsequent research directions.

Nothing in `research/` should be read as machine verified merely because it appears in this repository. A research result moves into Part I only after its paper statement, proof, and Lean declaration have been synchronized and audited.

## Scope and priority

I do **not** claim the first solution of Erdős Problem 906. Eric Hou gave a probabilistic bounded-coefficient Fock-series construction in 2026, with a public Lean formalization. The present submission has a different purpose: it gives a fixed explicit sparse series and a fully formalized quantitative localization theory for its high-derivative zeros.

Erdős's 1982 discussion also states that the relevant existence questions had been proved earlier, while the directly checked Barth-Schneider theorem under the cited title is a different interpolation statement. The repository therefore keeps the historical-priority claim deliberately narrow; see [`paper/PRIORITY_AND_SCOPE.md`](paper/PRIORITY_AND_SCOPE.md).

## AI assistance disclosure

Language-model tools were used substantially during derivation, checking, exposition, repository maintenance, and formalization. This disclosure is kept separate from the mathematical prose. The paper and formalization files state precisely which claims are machine checked.
