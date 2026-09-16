# Referee-style audit of the canonical submission

Audit date: 2026-09-17.

This file records the release audit used to bring the website-submission paper into exact scope and proof alignment with the Lean development. It is not part of the mathematical proof.

## 1. Scope corrections

The earlier manuscript mixed a fully formalized `p = 3/2` layer with manuscript-only generalizations. The canonical paper now fixes `p = 3/2` from the first definition onward.

The following are excluded from the submission theorem package because they are not part of the synchronized Lean development:

- exact order two and exact type `1/2`;
- sectorial zero-count asymptotics;
- limiting zero measure;
- the full `4/3 < p < 2` theorem;
- the `p = 4/3` compactness theorem;
- later support-profile and phase-diagram results.

They remain research material only.

## 2. Quantifier audit

The Erdős statement is written with the exact cofinite quantifier

`for every nonempty open U, there exists N such that for every n >= N ...`.

The equivalence with the original formulation using every increasing sequence of derivative orders is proved explicitly in the introduction: if cofinite hitting fails, choose the increasing sequence of exceptional orders; conversely, an increasing sequence is eventually above the cofinite threshold for each fixed open set.

The proof from annular covering to an arbitrary open set selects a nonzero point of the open set, then a closed disk contained in the open set and bounded away from the origin. This matches `erdos906_sparse_fock_p32`.

## 3. Tail-estimate audit

A substantive mismatch was found and corrected during the release audit. An earlier paper draft replaced the full left tail by a pure geometric-series factor. That was stronger than the bound actually proved in Lean.

The canonical paper now prints the same structural estimate as `tail_sum_bound`:

`exp(-(c-gamma)Q) * ((m+1) + exp(q gamma)/(1-exp(-(c-gamma))))`.

The polynomial factor `(m+1)` is retained. In the `p = 3/2` saddle range, `(c-gamma)Q` is of order `n^(1/6)` while `m = O(sqrt(n))`, so the exponential decay still dominates the polynomial factor. The explicit threshold inequalities used later are those formalized in the numeric/local modules. No theorem depends on the previously over-strong simplification.

## 4. Local-zero audit

The model disks have radius

`c rho_j / q_j`

with one fixed small constant `c`, matching `modelRadius` and `model_disk_zero_count_one_p32`.

The paper and Lean now use the same proof mechanism and compatible constants:

- in logarithmic coordinates, the normalized model is `1 - exp(q w) + E(w)`;
- a minimum-modulus argument supplies a zero within distance `2 rho c0/q` of the model centre;
- taking `s = 2 c0/q` places that zero inside the disk used for uniqueness;
- `q s <= 1/8` gives the formal `1/7` control of `t^(q-1)-1`;
- Cauchy's estimate on the doubled disk gives `|R'| <= K/s`;
- the formal lower Lipschitz estimate for `t -> t^q` then proves uniqueness and simplicity.

Thus the printed existence disk and the printed uniqueness disk are no longer left with an implicit constant-compatibility gap.

## 5. Exhaustion and simplicity audit

Exhaustion and annular simplicity are separate statements.

The printed exclusion proof now follows the exact formal trichotomy. If `rho_j <= |z| < rho_(j+1)`, then either

1. `log(|z|/rho_j) <= c0/q_j`, so the left transition theorem captures the zero;
2. `log(rho_(j+1)/|z|) <= c0/q_(j+1)`, so the right transition theorem captures it; or
3. both inequalities fail, and `T_(j+1)` dominates the sum of all other terms, so no zero is possible.

Proposition 1.4 corresponds only to the capture statement. Corollary 1.5 explicitly combines capture with Proposition 1.3 on the enlarged annulus before concluding simplicity.

## 6. Disjointness and counting audit

Pairwise disjointness and finite zero counting are separate propositions, matching separate Lean declarations.

The finite count is stated as a **distinct-zero** count, because the formal theorem uses `Set.ncard`. The simultaneous simplicity conclusion explains why total multiplicity has the same numerical value on the selected disks.

The statements now explicitly retain the active-index hypothesis where the Lean declarations require it.

## 7. Covering audit

The covering proof no longer uses a hand-waved “initial case” or an informal nearest-support selection. It follows the formal route:

- for a target radius in a fixed annulus, choose consecutive crossing radii `rho_j <= r < rho_(j+1)`;
- the formal radial spacing bound gives an `O(n^(-1/6))` radial displacement;
- the nearest model angle contributes only `O(q_j^(-1)) = O(n^(-1/3))`;
- the one-zero model-disk theorem contributes another `O(n^(-1/3))`.

The radial term dominates and gives Theorem 1.2.

## 8. Origin audit

No global eventual-simplicity statement is made. The paper records that the origin can have multiplicity `nu_(j0)-n`, and `origin_multiplicity` is now included explicitly in the paper-to-Lean crosswalk and `Main.lean` axiom audit.

## 9. Proof-structure audit

The printed paper and Lean development follow the same dependency chain:

`support arithmetic -> discrete curvature -> crossing radii -> exact tail domination -> local existence -> local uniqueness/simplicity -> exhaustion -> disjointness/count -> covering -> cofinite hitting`.

No general Rouché theorem is used as a black box. The existence argument is the minimum-modulus argument formalized in `TwoTerm.lean`; the uniqueness/simplicity argument is the Cauchy-error argument formalized in `ZeroCount.lean` and `ZeroCount32.lean`.

## 10. Citation audit

The final bibliography has four entries, and both bibliographic data and cited role were checked against primary/publisher/arXiv records.

- **Erdős 1982.** North-Holland Math. Stud. 74, 59-79, DOI `10.1016/S0304-0208(08)70415-8`. Page 72 states item (i), the increasing-sequence dense-union problem used here.
- **Barth-Schneider 1972.** Proc. Amer. Math. Soc. 32, 229-232, DOI `10.2307/2038336`. Theorem 1 chooses derivative orders together with prescribed discrete zero sets. It does not itself state the cofinite quantifier of item (i).
- **Gethner 1985.** Proc. Edinburgh Math. Soc. 28, 381-407, DOI `10.1017/S001309150001720X`. The final set is defined through neighborhoods containing points of infinitely many derivatives.
- **Hou 2026.** arXiv:2607.20816. The abstract states a probabilistic bounded-coefficient Fock construction with the cofinite property and a Lean 4 formalization of the existence theorem, growth bound, and supporting lemmas.

Erdős's 1982 article says that the existence questions in items (i) and (ii) had been proved more than ten years earlier and gives a note citing Barth-Schneider. Because the printed Barth-Schneider theorem that is directly available proves the distinct interpolation statement above, the submission makes no first-solution or historical-priority claim.

## 11. Typesetting and symbol audit

The revised source compiles under `amsart`. The local release build has no undefined references, undefined citations, LaTeX errors, or overfull horizontal boxes. The PDF was rendered page by page and visually inspected. Notation is fixed before use; model-disk radii, annulus conventions, active-index conditions, derivative orders, and the distinction among `q_j`, `m_j`, and the tail-separation parameter `Q` are consistent throughout.

## 12. Release criterion

The submission is synchronized only on a commit for which all of the following are green:

1. LaTeX compilation of `paper/paper_en.tex`;
2. automated rejection of undefined citations/references, LaTeX errors, and overfull boxes in the paper log;
3. Lean static integrity scan;
4. `lake build RequestProject.Main` using the pinned toolchain and project manifest.

The final website link must point to `main` only after the audited branch has been merged and these checks have passed on the release state.
