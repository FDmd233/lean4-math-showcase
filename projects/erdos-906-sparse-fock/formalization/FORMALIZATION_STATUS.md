# Formalization status

Current synchronized submission snapshot: September 17, 2026.

## Canonical scope

The canonical website-submission paper is `../paper/paper_en.tex`. It is intentionally restricted to the single explicit parameter value `p = 3/2`.

Every theorem, proposition, corollary, and the origin-multiplicity remark in that submission has a corresponding Lean declaration in `lean/RequestProject/`. Broader results are kept in `../research/` and are not claims of the formalized submission.

## Principal declarations used by the paper

- `F_differentiable`
- `iteratedDeriv_F`
- `F_not_polynomial`
- `F_norm_le`
- `annular_covering_rate_p32`
- `erdos906_sparse_fock_p32`
- `model_disk_zero_count_one_p32`
- `annular_zero_exclusion_p32`
- `annular_zeros_simple_p32`
- `annular_zeros_simple_deriv_p32`
- `model_disks_pairwise_disjoint_p32`
- `zero_count_model_disk_union_p32`
- `origin_multiplicity`

`RequestProject/Main.lean` prints the axiom dependencies of these declarations.

## Mathematical content of the checked layer

For the function

`F(z) = sum_{j>=1} z^(floor(j^(3/2))) / sqrt(floor(j^(3/2))!)`,

the Lean development checks:

- entire-function construction and the differentiated series formula;
- transcendence;
- the upper quadratic-exponential growth estimate used in the paper;
- the support-gap arithmetic for `floor(j^(3/2))`;
- discrete curvature and crossing-radius control;
- the exact tail domination inequality used in equation (3.2) of the paper, including its polynomial left-tail factor;
- the two-term minimum-modulus existence argument;
- local uniqueness and simplicity from Cauchy control of the normalized error;
- the explicit `n^(-1/6)` annular covering rate;
- the cofinite zero-hitting theorem for every nonempty open set;
- exactly one simple zero in every admissible model disk;
- exclusion of additional zeros on a fixed annulus by the left-transition/right-transition/one-term-dominance trichotomy;
- eventual simplicity of all annular zeros;
- eventual pairwise disjointness of admissible model disks;
- exact distinct-zero counts on finite unions of admissible model disks;
- the exact multiplicity of the possible zero at the origin.

The finite-union theorem uses `Set.ncard`, so its formal count is a distinct-point count. The separately checked simplicity statement makes the corresponding total multiplicity equal to the same number.

## Integrity status

The published `RequestProject/` tree contains no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or `@[implemented_by]`. The principal declarations printed by `RequestProject/Main.lean` use only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` in the supplied build record.

The repository CI performs a static integrity scan and builds `RequestProject.Main`. A green CI run on the exact submission commit is the release criterion for describing the checked layer as synchronized.

The Lean toolchain is pinned to `leanprover/lean4:v4.28.0`; the Mathlib revision is pinned by the project manifest.

## Research-only statements

The following are intentionally outside the canonical submission and are not represented as machine-checked results here:

- exact order two and exact type `1/2`;
- the sector zero-count asymptotic;
- the limiting zero measure;
- the full structural theorem for general `4/3 < p < 2`;
- the critical `p = 4/3` compactness argument;
- the later `1 < p < 4/3`, support-profile, sea-to-crystal, and microscopic phase-diagram investigations.

See `../research/README.md` for the research boundary.
