# Verification notes: sparse Fock series at p = 3/2

These notes document the correspondence between the mathematical argument and the Lean development. The manuscript and its formally checked theorem statements are authoritative. No result for the full interval 1 < p < 2 is asserted here.

## Scope and quantifiers

Let
\[
F(z)=\sum_{j\ge1}\frac{z^{\lfloor j^{3/2}\rfloor}}{\sqrt{\lfloor j^{3/2}\rfloor!}}.
\]
The cofinite zero-hitting theorem states
\[
\forall U\subseteq\mathbb C\;
\bigl(U\text{ nonempty and open}\bigr)
\ \Longrightarrow\
\exists N\in\mathbb N\;\forall n\ge N,\quad
Z\bigl(F^{(n)}\bigr)\cap U\ne\varnothing.
\]
The paper proves the equivalence with Erdős's increasing-sequence formulation. Its quantitative statements concern this fixed function only.

## Tail estimate

At an active crossing radius, use the paper's notation
\(m=m_j\), \(q=q_j\), \(Q=\min(q_{j-1},q_{j+1})\), with
\(0\le\gamma<c\) and \(|z|=\rho_j e^\sigma\), \(|\sigma|\le\gamma\).
The bound actually used is
\[
\frac{\displaystyle\sum_{h\ne j,j+1}|T_h(z)|}{|T_j(z)|}
\le e^{-(c-\gamma)Q}
\left((m+1)+\frac{e^{q\gamma}}{1-e^{-(c-\gamma)}}\right).
\]
The factor \(m+1\) belongs to the left-tail estimate; it cannot simply be omitted.
For \(p=3/2\) in the fixed saddle range, the exponential decay dominates
this polynomial factor.

## Local zeros and annular exclusion

For an admissible model centre \(z_0\), logarithmic coordinates
\(z=z_0e^w\) reduce the normalized derivative to
\[
1-e^{qw}+E(w).
\]
The minimum-modulus argument yields a zero in a sufficiently small
model disk. Cauchy estimates for the error on a larger disk establish
uniqueness and simplicity.

Between two consecutive crossing radii, the annular exclusion argument
covers three alternatives: proximity to the left crossing, proximity to
the right crossing, and the central region where one term strictly
dominates the others. The paper and Lean development use the same
trichotomy.

## Disjointness, counting, and covering

On one crossing circle, model centres have angular spacing on the
scale \(\rho_j/q_j\). Distinct crossing circles have radial separation
on the scale \(n^{-1/6}\); model disks are eventually pairwise disjoint.

The finite-union theorem counts distinct zeros. The separately proved
simplicity statement identifies this count with total multiplicity
within those disks.

For a target point in a fixed annulus, the nearest crossing circle
contributes a radial error \(O(n^{-1/6})\); angular and local-model
errors are \(O(n^{-1/3})\). The resulting covering estimate implies
cofinite zero hitting on every nonempty open set.

The origin is treated separately; the paper does not claim that all
zeros at the origin are simple. The formal statement recording its
multiplicity is named origin_multiplicity.

## Proof dependencies and audit boundary

The main chain is
\[
\text{support arithmetic}\longrightarrow
\text{discrete curvature}\longrightarrow
\text{crossing radii}\longrightarrow
\text{tail domination}\longrightarrow
\text{local zeros}\longrightarrow
\text{annular exclusion}\longrightarrow
\text{disjointness and counting}\longrightarrow
\text{covering}\longrightarrow
\text{cofinite zero hitting}.
\]
The statement-to-declaration crosswalk is in the adjacent
formalization/formalization_map.md file. The Lean sources must be
compiled against the pinned Lean and Mathlib revisions; the absence
of unfinished proof placeholders alone is not a compilation certificate.

Results about exact order and type, sectorial zero counts, limiting
zero measures, general \(p\), and endpoint regimes are outside the
theorem package.

## Historical references

The manuscript distinguishes its scope from the related work of
Erdős (1982), Barth–Schneider (1972), Gethner (1985), and Hou (2026).
See PRIORITY_AND_SCOPE.md for the precise priority discussion.
