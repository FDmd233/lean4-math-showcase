# Page-by-page proof guide

This guide is for checking the compiled six-page paper `paper_en.pdf`. It is explanatory only; the paper itself remains the authoritative submission.

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

At a crossing, curvature across a sparse gap of length `q_j ~ n^(1/3)` produces a slope margin `q_j/sqrt(n)`. Taking another sparse step multiplies this by another gap, producing the logarithmic tail loss `E_n ~ q_j^2/sqrt(n) ~ n^(1/6)`. This is the mechanism that reduces the derivative to two adjacent terms. The page ends by introducing the normalized logarithmic local model `1-exp(qw)+E(w)`.

## Page 4 - existence, uniqueness, simplicity, and annular exhaustion

The existence proof is the same mechanism formalized in `TwoTerm.lean`. On a logarithmic disk `|w| <= c_0/q`, the normalized tail is exponentially small. At the centre the two principal terms cancel, while on the boundary the elementary estimate `|1-exp(qw)| >= c_0/2` dominates the tail. If the true function were zero-free, the maximum-modulus principle applied to its reciprocal would contradict the strict centre-versus-boundary modulus inequality. Hence a true zero lies near each model centre.

Uniqueness and simplicity follow the formalized `ZeroCount.lean` argument. In the coordinate `t=z/z_0`, write `G(t)=1-t^q+R(t)`. A tail bound on the doubled disk and Cauchy's estimate give `|R'| <= K/s`; the condition `q s <= 1/8` keeps `t^(q-1)` uniformly close to `1`. Thus `t -> t^q` has a quantitative lower Lipschitz bound on the model disk, while the error is strictly smaller. Two zeros would violate these two inequalities, and the same derivative comparison rules out a multiple zero.

The page then begins the exhaustion step. Strictly ordered crossing radii make the normalized block slopes decrease with the support index. Away from transition regions one term dominates the sum of all others, so no zero is possible; inside a transition region the two-term estimate forces a zero into a model disk.

## Page 5 - disjointness, covering, cofinite hitting, and machine crosswalk

Exhaustion plus the one-zero theorem on an enlarged annulus gives eventual annular simplicity. Same-circle model centres are separated on the `q_j^(-1)=O(n^(-1/3))` scale, while adjacent crossing circles are separated on the larger `n^(-1/6)` radial scale; this proves pairwise disk disjointness and exact finite distinct-zero counts.

For an arbitrary point `w` of a fixed annulus, the support index nearest the continuous saddle `n+|w| sqrt(n)` has a crossing radius within `O(n^(-1/6))`. Choosing the nearest model angle adds only `O(n^(-1/3))`; the local model-disk zero adds another error of the same smaller order. This proves the covering theorem. A small annular disk inside any nonempty open set then gives the cofinite theorem.

The origin is separated from the annular simplicity statement because its multiplicity can be large. The remainder of the page gives the one-to-one crosswalk from printed theorem-level statements to Lean declarations and records the proof-escape/axiom audit.

## Page 6 - bibliography

The final page contains only the four references used for historical or contextual claims. Their roles and bibliographic data are separately audited in `PRIORITY_AND_SCOPE.md`.
