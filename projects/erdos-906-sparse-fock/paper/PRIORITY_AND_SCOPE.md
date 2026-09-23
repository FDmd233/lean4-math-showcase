# Priority and scope

Literature review date: 2026-09-23.

This note concerns the fixed `p = 3/2` paper. Research material in `../research/` lies outside the claims below.

## Scope of the paper

The paper does not claim first-solution priority for Erdős Problem 906. It proves that the explicit deterministic sparse series

\[
F(z)=\sum_{j\ge1}\frac{z^{\lfloor j^{3/2}\rfloor}}{\sqrt{\lfloor j^{3/2}\rfloor!}}
\]

has the cofinite high-derivative zero-hitting property and the quantitative annular zero geometry stated in the manuscript. The theorem-level statements in the paper have corresponding declarations in the accompanying Lean development.

No theorem depends on an originality claim.

## Database numbering and source note

The label **Erdős Problem #906** is the numbering used by the contemporary [Erdős Problems database](https://www.erdosproblems.com/906), not a numbering from Erdős's original publications. The database lists `[Er56d]` and `[Er82e,p.72]` as sources and notes that `[Er56d]` is a 1956 Hungarian source. The present paper has directly checked the 1982 survey but does not claim an independent reading or translation of `[Er56d]`; the 1956 source trace is therefore attributed explicitly to the database.

## Literature used for the historical discussion

1. **Erdős Problems database, Problem #906.** `https://www.erdosproblems.com/906`, accessed 2026-09-23. This source is used for the modern problem number and the cross-reference to `[Er56d]`; it is not used in place of the primary 1982 text for Erdős's wording.

2. **P. Erdős (1982).** *Some of my favourite problems which recently have been solved*, Proceedings of the International Mathematical Conference, Singapore 1981, North-Holland Mathematics Studies 74, 59-79. DOI: `10.1016/S0304-0208(08)70415-8`. Page 72, item (i), asks for an entire function such that for every increasing infinite sequence of derivative orders, the union of the corresponding zero sets is dense.

3. **K. F. Barth and W. J. Schneider (1972).** *On a problem of Erdös concerning the zeros of the derivatives of an entire function*, Proceedings of the American Mathematical Society 32, 229-232. DOI: `10.2307/2038336`. Their Theorem 1 is a discrete interpolation statement in which derivative orders are chosen together with prescribed discrete zero sets.

4. **R. M. Gethner (1985).** *On the zeros of the derivatives of some entire functions of finite order*, Proceedings of the Edinburgh Mathematical Society 28, 381-407. DOI: `10.1017/S001309150001720X`. Gethner's final set is defined through neighborhoods containing points of infinitely many derivatives.

5. **Eric Hou (2026).** *Cofinite Zeros of High Derivatives*, arXiv:2607.20816. The arXiv record describes a probabilistic bounded-coefficient Fock-series construction satisfying the cofinite property and an accompanying Lean formalization.

## Historical caution

Erdős's 1982 article states that the existence questions in items (i) and (ii) had been proved more than ten years earlier. The survey passage does not identify a specific theorem establishing item (i), the cofinite statement used in the present paper. The Erdős Problems database notes that the surrounding context suggests work of Barth and Schneider, but the directly checked 1972 Barth--Schneider theorem is the discrete interpolation result described above rather than the same cofinite statement.

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
