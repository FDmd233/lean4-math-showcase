# Priority and scope

Literature audit date: 2026-09-17.

This file concerns the **fully formalized website-submission paper only**. Research-only material is kept in `../research/` and is not part of the claims below.

## Public claim

I do **not** claim that this is the first solution of Erdős Problem 906. The submission makes the narrower claim that the explicit deterministic sparse series

\[
F(z)=\sum_{j\ge1}\frac{z^{\lfloor j^{3/2}\rfloor}}{\sqrt{\lfloor j^{3/2}\rfloor!}}
\]

has the cofinite high-derivative zero-hitting property and admits the quantitative annular zero geometry stated in the paper, with those theorem-level statements backed by the accompanying Lean development.

No theorem in the submission depends on an originality claim.

## Sources checked directly

The bibliography of the submission has been restricted to sources whose bibliographic data and cited role were checked directly.

1. **P. Erdős (1982).** *Some of my favourite problems which recently have been solved*, Proceedings of the International Mathematical Conference, Singapore 1981, North-Holland Mathematics Studies 74, 59-79. DOI: `10.1016/S0304-0208(08)70415-8`. Page 72, item (i), asks for an entire function such that for every increasing infinite sequence of derivative orders, the union of the corresponding zero sets is dense. This is the formulation whose quantifiers are converted explicitly to the cofinite open-set formulation in the paper.

2. **K. F. Barth and W. J. Schneider (1972).** *On a problem of Erdös concerning the zeros of the derivatives of an entire function*, Proceedings of the American Mathematical Society 32, 229-232. DOI: `10.2307/2038336`. Their Theorem 1 says that for any sequence of discrete sets `S_k`, one can choose derivative orders `n_k` and a transcendental entire function with `f^(n_k)=0` on `S_k`. This is a different interpolation statement and does not itself state the cofinite quantifier proved in the submission.

3. **R. M. Gethner (1985).** *On the zeros of the derivatives of some entire functions of finite order*, Proceedings of the Edinburgh Mathematical Society 28, 381-407. DOI: `10.1017/S001309150001720X`. Gethner's final set is defined through neighborhoods containing points of infinitely many derivatives. This is a different, weaker quantifier than the cofinite condition.

4. **Eric Hou (2026).** *Cofinite Zeros of High Derivatives*, arXiv:2607.20816. The arXiv abstract states a probabilistic bounded-coefficient Fock-series construction satisfying the cofinite property and a Lean 4 formalization of the existence theorem, growth bound, and supporting lemmas.

## Historical caution

Erdős's 1982 article says immediately after items (i) and (ii) that the existence of both functions had been proved more than ten years earlier, with a footnote listing Barth-Schneider and other Barth-Schneider papers. The directly checked Barth-Schneider 1972 theorem available under the cited title is the discrete interpolation theorem described above, not the cofinite statement of item (i).

Accordingly, the submission does not infer historical priority from this note and does not claim to settle who first proved the cofinite statement. This is deliberate: the mathematical theorem proved here is independent of any priority conclusion.

## What is deliberately not claimed

The formalized submission does not claim:

- first-solution priority for Erdős Problem 906;
- historical priority for sparse-Fock or lacunary constructions;
- exact order two or exact type `1/2`;
- sectorial zero-count asymptotics;
- a limiting zero measure;
- a theorem for all `4/3 < p < 2`;
- the critical `p = 4/3` compactness theorem;
- later support-profile or phase-diagram research statements.

Some of these statements occur in the research directory or in repository history. They are excluded from the website submission precisely so that the submitted theorem package and Lean package have the same mathematical scope.

## Comparison with Hou

The comparison in the paper is factual rather than evaluative. Hou's construction is probabilistic and uses bounded Fock coefficients. The present construction is the fixed explicit sparse series above. The additional result emphasized here is quantitative annular localization of high-derivative zeros, together with a synchronized machine-checked development.

No numerical growth constant is used as a superiority claim; such constants are sensitive to rescaling.

## AI assistance

Language-model tools were used substantially during derivation, checking, exposition, repository maintenance, and formalization. The mathematical prose is otherwise written as ordinary journal prose. The separate disclosure in the paper is retained intentionally.
