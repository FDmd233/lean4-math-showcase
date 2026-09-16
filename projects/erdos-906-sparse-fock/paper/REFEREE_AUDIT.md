# Referee-style audit of the canonical submission

Audit date: 2026-09-17.

This file records the changes made to bring the website-submission paper into exact scope alignment with the Lean development. It is not part of the mathematical proof.

## 1. Scope corrections

The previous manuscript mixed a fully formalized `p = 3/2` layer with manuscript-only generalizations. The canonical paper now fixes `p = 3/2` from the first definition onward.

The following were removed from the submission theorem package because they are not yet part of the published Lean development:

- exact order two and exact type `1/2`;
- sectorial zero-count asymptotics;
- limiting zero measure;
- the full `4/3 < p < 2` theorem;
- the `p = 4/3` compactness theorem;
- later support-profile and phase-diagram results.

They are research material only.

## 2. Quantifier audit

The Erdős statement is written with the exact cofinite quantifier

`for every nonempty open U, there exists N such that for every n >= N ...`.

The paper explicitly distinguishes this from:

- choosing a subsequence of derivative orders;
- requiring infinitely many derivative orders only.

The proof from annular covering to an arbitrary open set selects a nonzero point of the open set, then a small disk contained in an annulus. This matches `erdos906_sparse_fock_p32`.

## 3. Local-zero audit

The model disks in the canonical paper have radius

`c rho_j / q_j`

with a fixed small constant `c`, matching `modelRadius` and `model_disk_zero_count_one_p32`. The exponentially small disks used in the broader manuscript are not asserted here.

The paper states exactly one zero and simplicity. The Lean theorem encodes `∃!` together with nonvanishing derivative at every zero in the disk.

## 4. Exhaustion and simplicity audit

Exhaustion and annular simplicity are now separate statements.

- Proposition 1.4 corresponds to `annular_zero_exclusion_p32` and contains only the model-disk capture statement.
- Corollary 1.5 corresponds to `annular_zeros_simple_deriv_p32`.

The printed proof explicitly invokes Proposition 1.3 on the enlarged annulus before concluding simplicity. This removes the previous logical shorthand in which simplicity appeared to follow from exclusion alone.

## 5. Disjointness and counting audit

Pairwise disjointness and finite zero counting are now separate propositions, matching separate Lean declarations.

The finite count is stated as a **distinct-zero** count, because the formal theorem uses `Set.ncard`. The simultaneous simplicity conclusion explains why total multiplicity has the same numerical value on the chosen disks.

## 6. Origin audit

No global eventual-simplicity statement is made. The paper records that the origin can have multiplicity `nu_{j0}-n`, matching the formal development. All simplicity theorems are annular.

## 7. Proof-structure audit

The paper and Lean development follow the same dependency chain:

`support arithmetic -> discrete curvature -> crossing radii -> tail domination -> local two-term zero -> exhaustion -> disjointness/count -> covering -> cofinite hitting`.

The only deliberate expository difference is the local-zero transfer: the paper uses Rouché's theorem because it is the shortest conventional proof; the Lean code proves the same local count and simplicity directly instead of depending on a general Rouché theorem in Mathlib.

## 8. Citation audit

The final bibliography has four entries. Their bibliographic data and cited roles were checked against the original/publisher or arXiv records:

- Barth-Schneider, Proc. Amer. Math. Soc. 32 (1972), 229-232, DOI `10.2307/2038336`;
- Erdős, North-Holland Math. Stud. 74 (1982), 59-79, DOI `10.1016/S0304-0208(08)70415-8`;
- Gethner, Proc. Edinburgh Math. Soc. 28 (1985), 381-407, DOI `10.1017/S001309150001720X`;
- Hou, arXiv:2607.20816 (2026).

No novelty claim depends on incomplete comparison with the older lacunary-entire-function literature.

## 9. Typesetting and symbol audit

The revised source compiles under `amsart` without overfull boxes. The compiled PDF was rendered page by page and visually inspected. Notation is fixed before use; model-disk radii, annulus conventions, derivative orders, and the distinction between `q_j` and `m_j` are consistent throughout.

## 10. Release criterion

The submission should be treated as synchronized only on a commit for which both of the following are green:

1. LaTeX build of `paper/paper_en.tex`;
2. Lean integrity scan and `lake build RequestProject.Main`.
