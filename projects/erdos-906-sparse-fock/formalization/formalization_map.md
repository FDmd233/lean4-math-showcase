# Formalization map: sparse Fock derivative zeros

I use this file as a compact proof map between the manuscript and the Lean development. The authoritative mathematical statements remain in `../paper/paper_en.tex`.

## Definitions

- `nu p j = floor (j^p)`, for `j >= 1` and real `p` in `[4/3,2)`.
- `q p j = nu p (j+1) - nu p j`, after strict positivity of the gap is established.
- `F p z = sum_{j>=1} z^(nu p j) / sqrt ((nu p j)!)`.
- At derivative order `n`, `j0 = min {j : n <= nu p j}` and `m j = nu p j - n` for active indices.
- `A j = sqrt ((nu p j)!)/(m j)!`; `T j z = A j * z^(m j)`.
- `rho j = (A j/A (j+1))^(1/q j)`.

## Dependency table

| Module | Paper label | Main output |
|---|---|---|
| Quantifiers | `eq:cofinite` | Cofinite hitting iff density along every increasing infinite sequence |
| Sparse support | `lem:gaps` | Positive gaps and local/global gap bounds |
| Entire function | `lem:analytic` | Normal convergence, derivative identity, transcendence |
| Growth | `lem:analytic` | Upper growth bound in Lean; full exact growth in the manuscript |
| Full weights | `lem:curvature` | Decreasing slope and saddle curvature |
| Radial grid | `lem:radii` | Exact crossing formula and radial control |
| Global tails | `lem:tail` | Geometric domination of nonprincipal terms |
| Model roots | `prop:rouche` | A true zero near each admissible model root |
| Local uniqueness | `prop:rouche` | Unique simple zero in each model disk for `p=3/2` |
| Exhaustion | `prop:exclusion` | Every fixed-annulus zero lies in a model disk |
| Covering | `sec:count` | `p=3/2` annular covering, including the `n^{-1/6}` rate |
| Disk geometry | `thm:geometry` | Disjoint model disks and eventual annular simplicity |
| Finite counts | `thm:geometry` | Exact distinct-zero count on finite unions of model disks |
| General/critical theory | Sections 4-5 | Manuscript only at present |

## Quantitative tail step

Write `Q=n^beta`, with `beta>1/4`. In the saddle range, the curvature gives an endpoint slope margin of order `q/sqrt(n)`. Monotonicity carries that margin away from the crossing block, and the active-gap lower bound gives a per-step logarithmic loss

`E_n = c Q^2 / sqrt(n)`.

The normalized tail is then bounded by a geometric expression of the form

`(1+exp L) exp(-E_n)/(1-exp(-E_n))`.

## Local zero step

At a model center `z0=rho exp((2 ell+1) pi i/q)`, divide by the nonvanishing principal monomial. The two-term model becomes `1-(1+u)^q`. The tail is smaller than the boundary size of the model term, giving existence of a nearby true zero. The Lean development then adds a separate uniqueness/simplicity estimate rather than relying on a formal Rouché theorem.

## Exhaustion step

The normalized block slopes `log r - log rho_j` decrease with `j`. At a maximal term, at most one neighboring term can stay comparable; the remaining terms are exponentially smaller. A true annular zero is therefore forced into one of the transition regions and then into a model disk. This is the step that justifies total annular statements rather than only existence near prescribed model points.

## What remains

The current `p=3/2` development reaches the finite model-disk count. The next genuinely new formalization work would be the sector asymptotic and limiting measure, followed by the general `4/3<p<2` range and the critical endpoint `p=4/3`. I would rather extend in that order than hide the remaining analytic arguments behind larger assumptions.
