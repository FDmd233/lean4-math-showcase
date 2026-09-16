# Page-by-page proof guide

This guide is for checking the compiled six-page paper `paper_en.pdf`. It is explanatory only; the paper itself remains the authoritative submission.

## Page 1 - exact quantifier, literature, and explicit function

The page fixes the quantifier that matters: every nonempty open set must contain a zero of **every sufficiently high derivative**. The equivalence with the original increasing-sequence formulation is proved in both directions by using the exceptional derivative orders when cofinite hitting fails.

The literature paragraph separates three nearby statements:

- Barth-Schneider choose derivative orders together with prescribed discrete zero sets;
- Gethner's final set uses infinitely many derivative orders;
- Hou proves the cofinite condition by a probabilistic bounded-coefficient Fock series.

The paper makes no first-solution claim. It then fixes the single function used in the formalized submission, `nu_j = floor(j^(3/2))`, and introduces `T_j`, the crossing radii `rho_j`, and the circular two-term model centres.

## Page 2 - theorem package and support scale

The complete theorem package is stated before the proof:

1. cofinite zero hitting;
2. `O(n^(-1/6))` annular covering;
3. one simple zero per admissible model disk;
4. exhaustion of all annular zeros by model disks;
5. eventual annular simplicity;
6. pairwise disjointness of model disks;
7. exact finite distinct-zero counts.

Every statement retains the active-index and annulus hypotheses present in its Lean declaration. The page then derives `q_j ~ sqrt(j)` and, in the differentiated saddle window, `q_j ~ n^(1/3)`. The factorial majorant gives the printed upper growth estimate and justifies termwise differentiation.

## Page 3 - curvature, crossing radii, and the exact tail bound

The logarithmic weight `Phi_(n,r)` is introduced on the full integer support. Its first difference is strictly decreasing; in the relevant range the discrete curvature is comparable to `n^(-1/2)`.

The crossing radius is an average of the full slope over one sparse gap. This yields the radial `n^(-1/6)` scale and the angular `n^(-1/3)` scale.

The important release correction is equation (3.2). The paper now prints the same structural bound as `tail_sum_bound` in `Tail.lean`:

`exp(-(c-gamma)Q) * ((m+1) + exp(q gamma)/(1-exp(-(c-gamma))))`.

The factor `(m+1)` is essential: an earlier draft incorrectly replaced the left tail by a pure geometric-series factor. In the `p = 3/2` saddle range the exponential `exp(-c n^(1/6))` still dominates this polynomial factor, and the formal numeric lemmas provide the fixed thresholds required later.

## Page 4 - local existence, uniqueness, simplicity, and exclusion

Existence follows the mechanism formalized in `TwoTerm.lean`. In logarithmic coordinates, after division by the principal monomial,

`Psi(w) = 1 - exp(q w) + E(w)`.

On `|w| = c0/q`, the two-term model has modulus at least `c0/2`, while the tail is smaller than `c0/4` for large `n`. At the centre the two main terms cancel. If the true function were zero-free, applying the maximum-modulus principle to its reciprocal would contradict this centre-versus-boundary modulus comparison.

The paper then synchronizes the constants for existence and uniqueness. Taking `s = 2 c0/q` puts the existence zero in the disk used for the uniqueness theorem. On the doubled `t`-disk, Cauchy's estimate gives `|R'| <= K/s`; `q s <= 1/8` gives the formal `1/7` estimate for `t^(q-1)-1` and hence the lower Lipschitz bound for `t -> t^q`. This proves uniqueness and simplicity.

The page begins the global exclusion argument with the exact formal trichotomy: near the left crossing, near the right crossing, or one-term dominance away from both.

## Page 5 - exhaustion, disjointness, covering, and the cofinite conclusion

The exclusion trichotomy captures every annular zero in a model disk whose crossing radius lies in a fixed enlarged annulus. Combining this with the one-zero theorem gives eventual annular simplicity.

Same-circle model centres have separation at least `4 rho_j/q_j`. Different crossing circles are separated on the larger radial `n^(-1/6)` scale, while model-disk radii are `O(n^(-1/3))`. This proves eventual pairwise disjointness and the exact finite distinct-zero count.

The covering proof now follows the Lean route exactly. For a target radius `r`, choose consecutive crossing radii `rho_j <= r < rho_(j+1)`. Their spacing gives an `O(n^(-1/6))` radial error. Choosing the nearest model angle and then the true zero inside its model disk adds only `O(n^(-1/3))`. A small closed disk contained in any nonempty open set then proves cofinite zero hitting.

The origin is kept separate because its zero can have large multiplicity. The exact multiplicity statement is backed by `origin_multiplicity`.

## Page 6 - machine crosswalk, disclosure, and references

The final page gives the paper-to-Lean declaration table, identifies the exact modules containing the tail, local-zero, and exclusion mechanisms, and records the pinned Lean/toolchain information. `RequestProject/Main.lean` audits every declaration in the crosswalk, including the origin-multiplicity remark.

The page ends with the separate AI-assistance disclosure and the four references used for historical/contextual claims. Their roles and bibliographic data are separately audited in `PRIORITY_AND_SCOPE.md` and `REFEREE_AUDIT.md`.
