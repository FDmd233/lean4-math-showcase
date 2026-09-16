# Formalization map: canonical `p = 3/2` submission

This map is intentionally one-directional: the authoritative submitted mathematics is `../paper/paper_en.tex`, and each theorem-level statement below points to the Lean declaration that checks it. Research-only material is excluded.

## Definitions

The paper fixes

- `nu j = floor(j^(3/2))`;
- `q j = nu (j+1) - nu j`;
- `F(z) = sum_{j>=1} z^(nu j) / sqrt((nu j)!)`;
- at derivative order `n`, `m j = nu j - n` on active indices;
- `A j = sqrt((nu j)!)/(m j)!` and `T j z = A j * z^(m j)`;
- `rho j = (A j/A (j+1))^(1/q j)`;
- model centers `z_(j,l) = rho_j exp((2l+1) pi i/q_j)`;
- closed model disks of radius `c rho_j/q_j`.

The Lean definitions `nu`, `qgap`, `F`, `mOf`, `rho`, `modelCenter`, `modelRadius`, and `modelDisk` implement these objects.

## Paper statement to Lean declaration

| Paper statement | Lean declaration | Main module |
| --- | --- | --- |
| Entire function | `F_differentiable` | `Fock.lean` |
| Differentiated series formula | `iteratedDeriv_F` | `Fock.lean` |
| Transcendence | `F_not_polynomial` | `Fock.lean` |
| Upper growth bound | `F_norm_le` | `Fock.lean` |
| Theorem 1.1: cofinite derivative zeros | `erdos906_sparse_fock_p32` | `Erdos906.lean` |
| Theorem 1.2: `n^(-1/6)` annular covering | `annular_covering_rate_p32` | `Covering32.lean` |
| Proposition 1.3: one simple zero per model disk | `model_disk_zero_count_one_p32` | `ModelDisk.lean` |
| Proposition 1.4: exhaustion of annular zeros | `annular_zero_exclusion_p32` | `Annulus.lean` |
| Corollary 1.5: eventual annular simplicity | `annular_zeros_simple_deriv_p32` | `Simplicity.lean` |
| Proposition 1.6: pairwise disjoint model disks | `model_disks_pairwise_disjoint_p32` | `Disjoint.lean` |
| Proposition 1.7: finite model-disk zero count | `zero_count_model_disk_union_p32` | `ZeroCountUnion.lean` |

## Proof dependency map

The mathematical proof and the Lean development use the same structural chain:

1. **Support arithmetic.** `Aux32.lean`, `Support.lean` establish explicit upper and lower bounds for `q_j` and the `j^(3/2)` support.
2. **Entire series and derivatives.** `Fock.lean` establishes the analytic object, its derivatives, transcendence, and the upper growth estimate.
3. **Discrete curvature.** `Curvature.lean`, `Concavity.lean` control the decreasing full-weight slope.
4. **Crossing radii.** `Radii.lean`, `Crossing.lean`, `RadialBounds.lean` locate and separate the radii at which adjacent sparse terms have equal modulus.
5. **Tail domination.** `Tail.lean` uses curvature plus support gaps to control all terms outside the principal pair.
6. **Two-term localization.** `TwoTerm.lean`, `ModelDisk.lean`, and the zero-count modules transfer the two-term geometry to the true derivative. The printed proof invokes Rouché's theorem for readability; the Lean proof establishes the local count and simplicity directly from analytic estimates rather than importing a general Rouché theorem as a black box.
7. **Exhaustion.** `Dominant.lean`, `Exclusion.lean`, `Annulus.lean` show that outside transition regions one term dominates and hence no zero occurs; every annular zero is therefore captured by a model disk.
8. **Geometry and count.** `Simplicity.lean`, `Disjoint.lean`, `ZeroCountUnion.lean` prove annular simplicity, pairwise disk disjointness, and exact finite distinct-zero counts.
9. **Covering and cofinite conclusion.** `Covering32.lean` proves the explicit covering rate; `Erdos906.lean` inserts a small annular disk into an arbitrary nonempty open set.

## Counting convention

`zero_count_model_disk_union_p32` uses `Set.ncard`; it therefore counts distinct zeros. Its companion simplicity conclusion shows that on these model disks the same integer is also the total multiplicity. The paper states the theorem in distinct-zero language to match the encoded statement exactly.

## Axiom and integrity audit

`RequestProject/Main.lean` prints the axioms of all declarations used in the paper's theorem crosswalk. The synchronized CI also scans `RequestProject/` for proof escapes and builds `RequestProject.Main`.

No theorem from `../research/` is imported into this map.
