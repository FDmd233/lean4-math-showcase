# Proof guide for the six-page sparse Fock manuscript

This guide summarizes the mathematical structure of paper_en.pdf.
The paper itself is the authoritative source for hypotheses, constants,
quantifiers, and the exact scope of formal verification.

## Page 1 — the function and the problem

The function under consideration is
\[
F(z)=\sum_{j\ge1}
\frac{z^{\lfloor j^{3/2}\rfloor}}
     {\sqrt{\lfloor j^{3/2}\rfloor!}}.
\]
The paper proves the cofinite formulation: each nonempty open subset
of \(\mathbb C\) contains a zero of every sufficiently high derivative
of \(F\). It explains the relationship to the increasing-sequence
formulation of Erdős Problem 906 and distinguishes earlier related
results without making an unsupported priority claim.

## Page 2 — theorem package and support scales

The main results establish cofinite zero hitting, an annular
\(O(n^{-1/6})\) covering estimate, one simple zero in every admissible
model disk, exclusion of other zeros in a fixed annulus, eventual
annular simplicity, separation of model disks, and exact finite-union
distinct-zero counts.

The support gaps satisfy \(q_j\asymp j^{1/2}\). In the relevant
differentiated saddle range, \(q_j\asymp n^{1/3}\).

## Page 3 — curvature and tail domination

Discrete concavity of the logarithmic weights controls consecutive
crossing radii. The radial spacing is of order \(n^{-1/6}\), while
the angular spacing is of order \(n^{-1/3}\).

The estimate used for the nonprincipal terms is
\[
\frac{\displaystyle\sum_{h\ne j,j+1}|T_h(z)|}{|T_j(z)|}
\le e^{-(c-\gamma)Q}
\left((m+1)+\frac{e^{q\gamma}}{1-e^{-(c-\gamma)}}\right).
\]
The factor \(m+1\) is essential to the stated estimate. It remains
controlled by the exponential decay in the \(p=3/2\) saddle range.

## Page 4 — local zeros and annular exclusion

Near a model centre, set \(z=z_0e^w\) and normalize the derivative:
\[
\Psi(w)=1-e^{qw}+E(w).
\]
A minimum-modulus argument proves zero existence; Cauchy estimates
for the error derivative imply local uniqueness and simplicity.
Annular exclusion treats proximity to either crossing radius and
the intervening one-term-dominance region.

## Page 5 — global annular geometry

Exclusion captures all annular zeros inside admissible model disks.
Crossing radii are separated on the scale \(n^{-1/6}\), while angular
spacing and local model radii are on the scale \(n^{-1/3}\).
This yields eventual disk disjointness and the covering estimate.
A closed disk contained in any nonempty open set then gives the
cofinite zero-hitting conclusion.

The multiplicity of a possible zero at the origin is handled separately.

## Page 6 — formalization and references

The final page states the paper-to-Lean correspondence and identifies
the pinned Lean and Mathlib environment. Consult
formalization/formalization_map.md and
formalization/FORMALIZATION_STATUS.md for the exact declarations and
verification boundary. The disclosed AI assistance is separate from
the mathematical proof.
