# Formalization map: sparse Fock derivative zeros

This is a proof specification, not a Lean development. The authoritative statements and proofs are in `../paper/paper_en.tex`.

## Definitions and scope

- `nu p j = floor (j^p)`, `j >= 1`, `p` real in `[4/3,2)`.
- `q p j = nu p (j+1) - nu p j`, with strict positivity established before natural subtraction is used.
- `F p z = sum_{j>=1} z^(nu p j) / sqrt ((nu p j)!)`.
- At derivative order `n`, `j0 = min {j : n <= nu p j}`; `m j = nu p j - n` is used only for active indices `j >= j0`.
- `A j = sqrt ((nu p j)!)/(m j)!`; `T j z = A j * z^(m j)`.
- `rho j = (A j/A (j+1))^(1/q j)` is positive real.
- Distance statements concern the zero set of a nonzero analytic derivative; counting statements use multiplicity in the manuscript.

## Dependency table

| Module | Paper label | Main output |
|---|---|---|
| Quantifiers | `eq:cofinite` | Cofinite hitting iff density along every increasing infinite sequence |
| Sparse support | `lem:gaps` | Positive gaps, local asymptotic `q ~ p n^beta`, global active-gap lower bound |
| Entire function | `lem:analytic` | Normal convergence, derivative identity, transcendence |
| Growth | `lem:analytic` | `log M(r)=r^2/2+O(log r)`; exact order and type |
| Full weights | `lem:curvature` | Globally decreasing slope and saddle curvature `~1/sqrt(n)` |
| Radial grid | `lem:radii` | Exact crossing formula, `rho=m/sqrt(n)+O(Q/sqrt(n))`, annular separation |
| Global tails | `lem:tail` | Geometric domination of all nonprincipal terms |
| Model roots | `prop:rouche` | One simple model root in each localization disk |
| Rouché transfer | `prop:rouche` | One true zero in every indicated disk |
| Exhaustion | `prop:exclusion` | All fixed-annulus zeros lie in localization disks |
| Supercritical cover | `sec:count` | Disk-uniform upper bound, including origin |
| Counting | `sec:count` | Sector asymptotic and local weak zero-measure limit |
| Supercritical sharpness | `sec:count` | Annular lower covering scale |
| Gaussian limits | `lem:gaussian` | Every limiting bilateral Gaussian series has a zero |
| Critical compactness | `lem:criticalcompact` | Locally uniform subsequential convergence of critical rescalings |
| Critical cover | `sec:critical` | Uniform annular `O(n^(-1/4))` covering |
| Disk zero count | `lem:diskcount` | `O(sqrt(n))` zeros in fixed disks |
| Critical sharpness | `sec:final` | Matching annular lower scale at `p=4/3` |

## Quantitative tail obligation

Let `Q=n^beta`, `beta>1/4`. In a fixed saddle range, local curvature gives an endpoint slope margin of order `q/sqrt(n)`. Global monotonicity propagates this outside the local range, while the global active-gap lower bound yields a per-sparse-step logarithmic loss

`E_n = c Q^2 / sqrt(n)`.

This leads to a geometric bound of the form

`(1+exp L) exp(-E_n)/(1-exp(-E_n))`

for the normalized tail near a crossing radius.

## Rouché obligation

For a model center `z0=rho exp((2 ell+1) pi i/q)` and radius `rho eta_n/q`, divide by the nonvanishing principal monomial. The model is `1-(1+u)^q`. A boundary lower bound of order `eta_n` dominates the normalized tail `O(exp(-E_n))`, so zero-counting Rouché gives exactly one true zero in each disk.

## Exhaustion obligation

Use the strictly decreasing normalized block slopes `log r - log rho_j`. At a maximal term, at most one immediate neighbor can remain comparable. Farther terms are exponentially suppressed. A true zero is therefore forced into one of the localization disks. This step is essential before claiming total annular counts or eventual annular simplicity.

## Critical endpoint

At `p=4/3`, two-term domination no longer improves with `n`. Normalize around a target point and extract subsequential limits. The limiting object is a bilateral Gaussian series with arbitrary unit phases. Every such limit has a zero; Rouché transfers a nearby zero back to the original derivative. The contradiction argument restores an all-sufficiently-large-`n` covering statement.

## Formalization strategy

The practical implementation order is:

1. `p=3/2` sparse support and analytic setup;
2. discrete weights and crossing radii;
3. global tails;
4. two-term model and Rouché transfer;
5. all-`n` covering theorem;
6. annular exclusion and simplicity;
7. finite zero counts on unions of model disks;
8. only then the general `p` range and critical endpoint.

The latest Aristotle Round 4 audit indicates that the concrete `p=3/2` chain has reached step 7 in substantial form. See `FORMALIZATION_STATUS.md`.
