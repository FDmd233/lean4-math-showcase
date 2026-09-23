# Formalization map for the \(p=3/2\) paper

The paper source is \`../paper/paper_en.tex\`. Each theorem-level statement below points to the Lean declaration that verifies it. Material in \`../research/\` is outside this map.

## Definitions

The paper fixes

- \`nu j = floor(j^(3/2))\`;
- \`q j = nu (j+1) - nu j\`;
- \`F(z) = sum_{j>=1} z^(nu j) / sqrt((nu j)!)\`;
- at derivative order \`n\`, \`m j = nu j - n\` on active indices;
- \`A j = sqrt((nu j)!)/(m j)!\` and \`T j z = A j * z^(m j)\`;
- \`rho j = (A j/A (j+1))^(1/q j)\`;
- model centers \`z_(j,l) = rho_j exp((2l+1) pi i/q_j)\`;
- closed model disks of radius \`c rho_j/q_j\`.

The Lean definitions \`nu\`, \`qgap\`, \`F\`, \`mOf\`, \`rho\`, \`modelCenter\`, \`modelRadius\`, and \`modelDisk\` implement these objects.

## Paper statement to Lean declaration

| Paper statement | Lean declaration | Main module |
| --- | --- | --- |
| Entire function | \`F_differentiable\` | \`Fock.lean\` |
| Differentiated series formula | \`iteratedDeriv_F\` | \`Fock.lean\` |
| Transcendence | \`F_not_polynomial\` | \`Fock.lean\` |
| Upper growth bound | \`F_norm_le\` | \`Fock.lean\` |
| Theorem 1.1: cofinite derivative zeros | \`erdos906_sparse_fock_p32\` | \`Erdos906.lean\` |
| Theorem 1.2: \`n^(-1/6)\` annular covering | \`annular_covering_rate_p32\` | \`Covering32.lean\` |
| Proposition 1.3: one simple zero per model disk | \`model_disk_zero_count_one_p32\` | \`ModelDisk.lean\` |
| Proposition 1.4: exhaustion of annular zeros | \`annular_zero_exclusion_p32\` | \`Annulus.lean\` |
| Corollary 1.5: eventual annular simplicity | \`annular_zeros_simple_deriv_p32\` | \`Simplicity.lean\` |
| Proposition 1.6: pairwise disjoint model disks | \`model_disks_pairwise_disjoint_p32\` | \`Disjoint.lean\` |
| Proposition 1.7: finite model-disk zero count | \`zero_count_model_disk_union_p32\` | \`ZeroCountUnion.lean\` |
| Remark 4.1: multiplicity at the origin | \`origin_multiplicity\` | \`Fock.lean\` |

## Printed intermediate estimates

The paper also uses displayed intermediate estimates whose formal counterparts lie inside the same dependency chain:

- support and gap arithmetic: \`Aux32.lean\`, \`Support.lean\`;
- discrete curvature of the full logarithmic weight: \`Curvature.lean\`, \`Concavity.lean\`;
- crossing identities and endpoint slope bounds: \`Radii.lean\`, \`Crossing.lean\`;
- radial location and spacing estimates: \`RadialBounds.lean\`, \`Spacing.lean\`;
- the exact tail estimate printed as equation (3.2): \`tail_sum_bound\` in \`Tail.lean\`;
- minimum-modulus existence near each model zero: \`exists_zero_of_dominant_two_term\` and its sparse specialization in \`TwoTerm.lean\`;
- uniqueness and simplicity from Cauchy control of the normalized error: \`unique_zero_of_two_term\` and \`unique_zero_near_model\` in \`ZeroCount.lean\` / \`ZeroCount32.lean\`;
- transition capture and one-term exclusion: \`transition_zero_p32\`, \`no_zero_dominant_p32\`, and \`annular_zero_exclusion_p32\` in \`Exclusion.lean\` / \`Annulus.lean\`.

The tail estimate includes the polynomial left-tail factor. In the \(p=3/2\) range, the formal numerical lemmas absorb that factor using the exponential \`exp(-c n^(1/6))\` decay.

## Proof dependency map

The mathematical proof and the Lean development use the same structural chain:

1. **Support arithmetic.** \`Aux32.lean\`, \`Support.lean\` establish explicit bounds for \`q_j\` and the \`j^(3/2)\` support.
2. **Entire series and derivatives.** \`Fock.lean\` establishes the analytic object, its derivatives, transcendence, upper growth, and the origin-multiplicity statement.
3. **Discrete curvature.** \`Curvature.lean\`, \`Concavity.lean\` control the decreasing full-weight slope.
4. **Crossing radii.** \`Radii.lean\`, \`Crossing.lean\`, \`RadialBounds.lean\` locate and separate radii at which adjacent sparse terms have equal modulus.
5. **Tail domination.** \`Tail.lean\` uses curvature and support gaps to control all terms outside the principal pair.
6. **Two-term localization.** \`TwoTerm.lean\`, \`ModelDisk.lean\`, \`ZeroCount.lean\`, and \`ZeroCount32.lean\` transfer the two-term geometry to the true derivative. Existence comes from a minimum-modulus argument in logarithmic coordinates; uniqueness and simplicity come from a Cauchy derivative estimate and a quantitative lower bound for the two-term model.
7. **Exhaustion.** \`Dominant.lean\`, \`Exclusion.lean\`, \`Annulus.lean\` implement the three-case argument: near the left crossing, near the right crossing, or one-term dominance away from both.
8. **Geometry and count.** \`Simplicity.lean\`, \`Disjoint.lean\`, \`ZeroCountUnion.lean\` prove annular simplicity, pairwise disk disjointness, and exact finite distinct-zero counts.
9. **Covering and cofinite conclusion.** \`Covering32.lean\` brackets a target radius by consecutive crossing radii, proves the covering rate, and \`Erdos906.lean\` inserts a small annular disk into an arbitrary nonempty open set.

## Counting convention

\`zero_count_model_disk_union_p32\` uses \`Set.ncard\`; it therefore counts distinct zeros. Its companion simplicity conclusion shows that on these model disks the same integer is also the total multiplicity.

## Axiom dependencies and integrity checks

\`RequestProject/Main.lean\` prints the axioms of every declaration in the theorem crosswalk, including \`origin_multiplicity\`. The CI configuration scans \`RequestProject/\` for the repository's forbidden proof escapes and builds \`RequestProject.Main\` with the pinned Lean toolchain and project manifest.

No theorem from \`../research/\` is imported into this map.
