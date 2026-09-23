# Verification notes for the fixed (p=3/2) paper

This note records several points where the printed proof and Lean development are matched explicitly.

## 1. Scope

The paper fixes (p=3/2). Results concerning exact order/type, sectorial zero counts, limiting zero measures, general (p), and endpoint regimes are kept outside the theorem package of this manuscript.

## 2. Quantifiers

The main theorem is stated as
[
orall U
earnothing	ext{ open},quad exists Nquad
orall nge N,quad Z(F^{(n)})cap U
earnothing.
]
The paper also proves its equivalence with the increasing-sequence formulation of Erdős Problem 906.

## 3. Tail estimate

The proof uses the bound
[
e^{-(c-gamma)Q}
left((m+1)+rac{e^{qgamma}}{1-e^{-(c-gamma)}}ight).
]
The factor (m+1) from the left tail is part of the formal statement. In the (p=3/2) saddle range the exponential term still dominates this polynomial factor.

## 4. Local zero theorem

The model-disk theorem uses one fixed small constant. In logarithmic coordinates the normalized function is
[
1-e^{qw}+E(w).
]
Existence follows from a minimum-modulus argument. Uniqueness and simplicity follow from Cauchy control of the normalized error on a slightly larger disk.

## 5. Annular exhaustion

For consecutive crossing radii (ho_jle |z|<ho_{j+1}), the proof divides into three cases:

1. the radius is close to (ho_j);
2. the radius is close to (ho_{j+1});
3. it is separated from both, in which case the middle term dominates the remaining series.

This is the same trichotomy used in the formal development.

## 6. Disjointness and counting

Same-circle model centres are separated on the scale (ho_j/q_j). Distinct crossing circles are separated on the larger radial scale (n^{-1/6}). The model disks are therefore eventually pairwise disjoint.

The finite-union counting theorem is a distinct-zero count; simplicity implies equality with total multiplicity on those disks.

## 7. Covering

Given a target point in a fixed annulus, the nearest crossing circle produces radial error (O(n^{-1/6})), while the angular and local model errors are (O(n^{-1/3})). The radial term dominates.

## 8. Origin

No global simplicity statement is made at the origin. Its multiplicity is recorded separately by `origin_multiplicity`.

## 9. Paper-to-Lean correspondence

The principal dependency chain is
[
	ext{support arithmetic}
	o 	ext{curvature}
	o 	ext{crossing radii}
	o 	ext{tail domination}
	o 	ext{local zero theorem}
	o 	ext{annular exclusion}
	o 	ext{disjointness/counting}
	o 	ext{covering}
	o 	ext{cofinite hitting}.
]

The detailed statement-to-declaration map is in `../formalization/formalization_map.md`.

## 10. References

The historical discussion uses Erdős (1982), Barth-Schneider (1972), Gethner (1985), and Hou (2026). The scope of the corresponding claims is summarized in `PRIORITY_AND_SCOPE.md`.
