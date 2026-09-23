# Priority and scope

Literature review date: 2026-09-17.

This note concerns the fixed `p = 3/2` paper. Research material in `../research/` lies outside the claims below.

## Scope of the paper

The paper does not claim first-solution priority for Erdős Problem 906. It proves that the explicit deterministic sparse series

\[
F(z)=\sum_{j\ge1}\frac{z^{\lfloor j^{3/2}\rfloor}}{\sqrt{\lfloor j^{3/2}\rfloor!}}
\]

has the cofinite high-derivative zero-hitting property and the quantitative annular zero geometry stated in the manuscript. The theorem-level statements in the paper have corresponding declarations in the accompanying Lean development.

No theorem depends on an originality claim.

## Literature used for the historical discussion

1. **P. Erdős (1982).** *Some of my favourite problems which recently have been solved*, Proceedings of the International Mathematical Conference, Singapore 1981, North-Holland Mathematics Studies 74, 59-79. DOI: `10.1016/S0304-0208(08)70415-8`. Page 72, item (i), asks for an entire function such that for every increasing infinite sequence of derivative orders, the union of the corresponding zero sets is dense.

2. **K. F. Barth and W. J. Schneider (1972).** *On a problem of Erdös concerning the zeros of the derivatives of an entire function*, Proceedings of the American Mathematical Society 32, 229-232. DOI: `10.2307/2038336`. Their Theorem 1 is a discrete interpolation statement in which derivative orders are chosen together with prescribed discrete zero sets.

3. **R. M. Gethner (1985).** *On the zeros of the derivatives of some entire functions of finite order*, Proceedings of the Edinburgh Mathematical Society 28, 381-407. DOI: `10.1017/S001309150001720X`. Gethner's final set is defined through neighborhoods containing points of infinitely many derivatives.

4. **Eric Hou (2026).** *Cofinite Zeros of High Derivatives*, arXiv:2607.20816. The arXiv record describes a probabilistic bounded-coefficient Fock-series construction satisfying the cofinite property and an accompanying Lean formalization.

## Historical caution

Erdős's 1982 article states that the existence questions in items (i) and (ii) had been proved more than ten years earlier, but the article does not identify a proof or precise reference for the cofinite statement in item (i). The directly checked Barth-Schneider theorem is the interpolation result described above rather than the same cofinite statement.

For that reason, the paper does not attempt to assign historical priority for the first proof of the cofinite statement.

## Claims not made in the paper

The fixed formalized paper does not claim:

- first-solution priority for Erdős Problem 906;
- historical priority for sparse-Fock or lacunary constructions;
- exact order two or exact type `1/2`;
- sectorial zero-count asymptotics;
- a limiting zero measure;
- a theorem for all `4/3 < p < 2`;
- the critical `p = 4/3` compactness theorem;
- later support-profile or phase-diagram results.

Some of these topics occur in the research directory or repository history. They are not part of the `p=3/2` theorem package.

## Comparison with Hou

Hou's construction is probabilistic and uses bounded Fock coefficients. The present paper studies the fixed explicit sparse series above and obtains quantitative annular localization of its high-derivative zeros. The comparison is descriptive rather than a claim of superiority.

## AI assistance

AI tools were used during parts of the derivation, checking, exposition, repository preparation, and formalization. The mathematical claims and verification boundary are stated independently of that assistance.
