# Proof guide

This note gives a compact guide to the six-page manuscript `paper_en.pdf`. The paper itself is the authoritative statement.

## Page 1 - formulation and explicit function

The paper states the cofinite formulation used throughout: every nonempty open set contains a zero of every sufficiently high derivative. It also explains the equivalence with Erdős's increasing-sequence formulation.

The historical paragraph distinguishes the related results of Barth-Schneider, Gethner, and Hou, and makes no first-solution claim.

The fixed function is
[
F(z)=sum_{jge1}rac{z^{lfloor j^{3/2}floor}}{sqrt{lfloor j^{3/2}floor!}}.
]
The notation for the active monomials, crossing radii, and two-term model centres is introduced here.

## Page 2 - theorem package and support scale

The main statements are:

1. cofinite zero hitting;
2. `O(n^{-1/6})` annular covering;
3. one simple zero per admissible model disk;
4. exhaustion of annular zeros by model disks;
5. eventual annular simplicity;
6. pairwise disjointness of model disks;
7. exact finite distinct-zero counts.

The support gaps satisfy (q_jasymp j^{1/2}), and in the differentiated saddle window (q_jasymp n^{1/3}).

## Page 3 - curvature, crossing radii, and tail domination

The logarithmic weight is discretely concave in the relevant range. This controls the spacing of crossing radii and yields the radial scale (n^{-1/6}) and angular scale (n^{-1/3}).

The tail estimate used in the proof is
[
 rac{sum_{h
e j,j+1}|T_h(z)|}{|T_j(z)|}
 le
 e^{-(c-gamma)Q}
 left((m+1)+rac{e^{qgamma}}{1-e^{-(c-gamma)}}ight).
]
The polynomial factor ((m+1)) is retained explicitly. In the (p=3/2) saddle range, the exponential decay dominates it.

## Page 4 - local existence, uniqueness, simplicity, and exclusion

Near a model centre, logarithmic coordinates reduce the derivative to
[
Psi(w)=1-e^{qw}+E(w).
]
A minimum-modulus argument gives existence of a zero. Cauchy control of the error derivative gives uniqueness and simplicity on the corresponding model disk.

The annular exclusion argument has three cases: proximity to the left crossing, proximity to the right crossing, or one-term dominance between them.

## Page 5 - global annular geometry and cofinite hitting

The exclusion theorem captures every annular zero in a model disk. Radial spacing is of order (n^{-1/6}), while model-disk radii and angular spacing are of order (n^{-1/3}). This gives disjointness and the stated covering rate.

A small closed disk contained in any nonempty open set then yields the cofinite zero-hitting theorem.

The origin is treated separately because its multiplicity can be larger than one.

## Page 6 - formal verification and references

The final page records the paper-to-Lean correspondence, the principal source modules, and the pinned Lean/mathlib environment. The detailed declaration map is in `../formalization/formalization_map.md`.

A brief AI-assistance statement is included separately from the mathematical content.
