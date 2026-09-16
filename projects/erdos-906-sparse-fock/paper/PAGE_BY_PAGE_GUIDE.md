# Page-by-page proof guide

This guide is for checking the compiled five-page paper `paper_en.pdf`. It is explanatory only; the paper itself remains the authoritative submission.

## Page 1 - problem, literature, and the explicit function

The page fixes the quantifier that matters: every nonempty open set must contain a zero of **every sufficiently high derivative**. The short equivalence with the subsequence-density formulation is proved immediately by taking the exceptional derivative orders when cofinite hitting fails.

The literature paragraph separates three nearby statements:

- Barth-Schneider choose derivative orders together with prescribed discrete zero sets;
- Gethner's final set uses infinitely many derivative orders;
- Hou proves the cofinite condition by a probabilistic bounded-coefficient Fock series.

The page then fixes the single function used in the formalized submission, `nu_j = floor(j^(3/2))`, and introduces the differentiated monomials `T_j`, crossing radii `rho_j`, and the circular two-term model centers. No general-`p` theorem is stated.

## Page 2 - theorem package and the first scale estimates

The complete theorem package is stated before the proof:

1. cofinite zero hitting;
2. `O(n^(-1/6))` annular covering;
3. one simple zero per admissible model disk;
4. exhaustion of all annular zeros by model disks;
5. eventual annular simplicity;
6. pairwise disjointness of model disks;
7. exact finite distinct-zero counts.

Each item has a separate Lean declaration. The page then derives the two elementary scales of the support. From the mean-value theorem and the floor error, `q_j` is comparable to `sqrt(j)`; in the differentiated saddle window this becomes `q_j ~ n^(1/3)`. The full sparse series is dominated by the standard factorial series, giving the upper quadratic-exponential bound and legitimizing termwise differentiation.

## Page 3 - discrete curvature, crossing radii, and tail domination

The logarithmic weight `Phi_{n,r}` is introduced on the full integer support before sparsification. Its discrete slope is strictly decreasing. In the relevant range the curvature is of order `n^(-1/2)`.

A crossing radius is the geometric mean arising from one entire sparse gap. Averaging the monotone full slope gives

- `rho_j = m_j/sqrt(n) + O(n^(-1/6))`;
- consecutive relevant crossing radii are separated on the `n^(-1/6)` scale.

At a crossing, curvature across a sparse gap of length `q_j ~ n^(1/3)` produces a slope margin `q_j/sqrt(n)`. Taking another sparse step multiplies this by another gap, producing the logarithmic tail loss `E_n ~ q_j^2/sqrt(n) ~ n^(1/6)`. This is the mechanism that reduces the derivative to two adjacent terms.

## Page 4 - local zero, exhaustion, disjointness, covering, and cofinite hitting

Near a model center, after division by the nonvanishing principal monomial, the two-term model is `1-(1+u)^q`. On a fixed `c/q` boundary this has a uniform lower bound, while the remaining sparse tail is exponentially small. The printed proof uses Rouché for the local count; the Lean development proves the same count and simplicity directly from the underlying estimates.

The exhaustion argument then treats two cases between consecutive crossing radii. Away from both transition regions one term dominates the sum of all others, so no zero exists. In a transition region the two-term estimate forces any zero into a model disk. Combining exhaustion with the one-zero theorem gives annular simplicity.

Angular separation is `O(q_j^(-1)) = O(n^(-1/3))`, whereas radial circle separation is `O(n^(-1/6))`; this proves disk disjointness and the finite count. Finally, the nearest crossing radius plus nearest model angle gives covering radius `O(n^(-1/6))`. A small annular disk inside an arbitrary open set converts covering into the cofinite theorem.

The origin is treated separately: high derivatives can have a large zero there, so global eventual simplicity would be false.

## Page 5 - machine-verification crosswalk and references

The first table is a one-to-one crosswalk from each printed theorem-level statement to its Lean declaration. It also records the distinction between distinct-zero counting (`Set.ncard`) and multiplicity; simplicity makes them numerically agree on the model disks.

The integrity paragraph records the proof-escape scan and the `#print axioms` audit. Research-only generalizations are explicitly excluded from the submission.

The four references are the only works used for historical/contextual claims in the paper. Their roles and bibliographic data are separately audited in `PRIORITY_AND_SCOPE.md`.
