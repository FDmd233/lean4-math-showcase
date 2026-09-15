This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Formalization of *Zeros of high derivatives of sparse Fock series*

This project contains a Lean 4 / Mathlib formalization of the elementary backbone of the
manuscript `paper_en.pdf` (`paper_en.tex`), by Zhijie He.

Everything in the `RequestProject` directory compiles with no `sorry`, no additional axioms
and no `native_decide`.

## Files

| File | Contents |
| --- | --- |
| `RequestProject/EntirePowerSeries.lean` | Power series with everywhere absolutely convergent coefficients: entirety of the sum, termwise differentiation, iterated derivatives. |
| `RequestProject/Support.lean` | The support exponents `ν_j = ⌊j^p⌋`, their strict monotonicity and two-sided gap bounds (Lemma 2.1). |
| `RequestProject/Curvature.lean` | The logarithmic weights `Φ_{n,r}`, their differences `d_{n,r}`, the discrete curvature Lemma 2.3 and the factorial bounds (2.7). |
| `RequestProject/Growth.lean` | The Cauchy–Schwarz bound (2.6) for `∑ r^k/√(k!)` and its specialization `ε = r^{-2}`. |
| `RequestProject/Fock.lean` | The series `F_p`, its entirety (Lemma 2.2), the growth bound (upper half of (1.3)), the derivative formula (2.5), positivity on the positive real axis, transcendence, and the origin multiplicity (4.2). |
| `RequestProject/Radii.lean` | The crossing radii `ρ_j`: the exact formula (2.11), the squeeze (2.14), strict monotonicity, and `ρ_j ≤ b ⟹ m_j = O(√n)`. |
| `RequestProject/Counting.lean` | The majorant `S_n(r)` and the estimates (5.1) and (5.2) behind the `O(√n)` zero count. |
| `RequestProject/Concavity.lean` | Telescoping of `Φ_{n,r}`, antitonicity of the differences, and the two slope bounds at a crossing radius. |
| `RequestProject/MinModulus.lean` | The minimum-modulus zero-detection principle (maximum principle applied to `1/f`), the complex-analytic replacement for Rouché. |
| `RequestProject/Tail.lean` | The coefficients of `F_p^{(n)}` and the global tail domination: the full left and right tails are exponentially small compared with the principal term. |
| `RequestProject/TwoTerm.lean` | The two-term model `A z^{m₀}(1 - e^{qw})` and the localisation of each of its zeros to a true zero of `F_p^{(n)}`. |
| `RequestProject/Aux32.lean` | Elementary exponential estimates and the `p = 3/2` support arithmetic. |
| `RequestProject/RadialBounds.lean` | `m_j = O(√n)` on a compact annulus and the spacing of consecutive crossing radii. |
| `RequestProject/Crossing.lean` | The crossing identities and the `p = 3/2` slope bounds. |
| `RequestProject/Phase.lean` | The `q` model phases `(e^{iθ})^q = -1` and their angular mesh `2π/q`. |
| `RequestProject/IndexSelect.lean` | Selection of the crossing index bracketing a given radius. |
| `RequestProject/Numeric.lean` | The purely numerical core of all size comparisons for `p = 3/2`. |
| `RequestProject/Covering32.lean` | The quantitative annular covering theorem for `p = 3/2`. |
| `RequestProject/Erdos906.lean` | **Erdős Problem 906 for `p = 3/2`: the cofinite zero-hitting theorem.** |
| `RequestProject/ZeroCount.lean` | Abstract local zero-counting: a two-term dominant model has at most one zero in the disk, and it is simple. |
| `RequestProject/ZeroCount32.lean` | The same for `iteratedDeriv n (F p)` under a tail bound. |
| `RequestProject/ModelDisk.lean` | Model centers, radii and disks; **exactly one zero, counted with multiplicity, in each model disk (`p = 3/2`)**. |
| `RequestProject/RootLoc.lean` | Quantitative root localisation for `‖1 + w^q‖ ≤ K`. |
| `RequestProject/Spacing.lean` | The radial spacing lower bound (2.16) for the crossing radii. |
| `RequestProject/TailGeneral.lean` | The tail bound outside a block of consecutive support points. |
| `RequestProject/ExclusionAux.lean` | Support arithmetic for three-term blocks. |
| `RequestProject/ExclusionNum.lean` | The purely numerical inequalities of the exclusion argument. |
| `RequestProject/Transition.lean` | A zero in a transition region lies in a model disk. |
| `RequestProject/Dominant.lean` | One-term dominance excludes zeros. |
| `RequestProject/Exclusion.lean` | The two halves of the exclusion dichotomy for `p = 3/2`. |
| `RequestProject/Annulus.lean` | **Every zero in a fixed annulus lies in a model disk (`p = 3/2`).** |
| `RequestProject/Simplicity.lean` | **Eventual simplicity of all zeros on a fixed annulus (`p = 3/2`).** |
| `RequestProject/Disjoint.lean` | **Eventual pairwise disjointness of the relevant model disks.** |
| `RequestProject/ZeroCountUnion.lean` | **Exact zero count on a finite union of model disks.** |
| `RequestProject/Main.lean` | Imports all of the above and prints the axioms of the main theorems. |

## Correspondence with the paper

| Paper | Lean |
| --- | --- |
| `ν_j = ⌊j^p⌋`, `q_j` | `SparseFock.nu`, `SparseFock.qgap` |
| Lemma 2.1 (monotonicity, gap size) | `nu_lt_nu_succ`, `one_le_qgap`, `qgap_le`, `le_qgap` |
| Series (1.2), `F_p` | `SparseFock.F` (via `SparseFock.fcoeff`, `SparseFock.sumSeries`) |
| Lemma 2.2 (entirety) | `F_differentiable` |
| (2.5) (termwise derivative) | `iteratedDeriv_F` |
| (2.6) (Cauchy–Schwarz) | `tsum_pow_div_sqrt_factorial_le`, `tsum_pow_div_sqrt_factorial_le'` |
| (1.3), upper half | `F_norm_le`, `F_norm_le_exp` |
| transcendence | `F_not_polynomial` (via `iteratedDeriv_F_pos`) |
| (2.7) (factorial bounds) | `log_factorial_lower`, `log_factorial_upper` |
| Lemma 2.3 (discrete curvature) | `dstep_eq`, `dstep_sub_dstep_succ`, `dstep_sub_dstep_succ_pos`, `dstep_curvature_lower`, `dstep_curvature_lower_sqrt` |
| (2.11), (2.14), radial monotonicity | `log_rho_eq`, `rho_squeeze`, `rho_lt_rho_succ`, `sq_le_of_rho_le` |
| (4.2) (origin multiplicity) | `origin_multiplicity` |
| (5.1), (5.2) | `Ssum_le`, `log_Ssum_le` |
| Lemma 3.1 (stable tail bound, full tails) | `tail_term_left`, `tail_term_right`, `tail_sum_bound`, `norm_sub_two_terms_le` |
| model centers (eq. `centers`) | `exists_phase` |
| Proposition 3.2 (Rouché transfer), existence half | `exists_zero_of_norm_lt_on_sphere`, `exists_zero_of_dominant_two_term`, `exists_zero_near_model` |
| Proposition 3.2 (Rouché transfer), exactly one zero with multiplicity | `unique_zero_of_two_term`, `unique_zero_near_model`, `model_disk_zero_count_one_p32` |
| model disks (eq. `disks`) | `modelCenter`, `modelRadius`, `modelDisk` |
| eq. (2.16) radial spacing / log spacing | `rho_log_spacing32` |
| Proposition 3.3 (exclusion), transition half | `zero_in_model_disk_of_transition`, `transition_zero_p32` |
| Proposition 3.3 (exclusion), dominance half | `no_zero_of_dominant`, `no_zero_dominant_p32` |
| Proposition 3.3 (exclusion), full statement | `annular_zero_exclusion_p32` |
| Proposition 3.3 / Theorem 1.2 (disjointness of the disks) | `model_disks_pairwise_disjoint_p32` |
| Theorem 1.2 (eventual annular simplicity) | `annular_zeros_simple_p32`, `annular_zeros_simple_deriv_p32` |
| Theorem 1.2 (zero count on a finite union of model disks) | `zero_count_model_disk_union_p32` |
| Section 4 covering, `p = 3/2` | `annular_covering`, `annular_covering_rate_p32` |
| Theorem 1.1, cofinite statement (eq. `cofinite`) | `erdos906_sparse_fock_p32` |

## Not formalized

The following parts of the manuscript are *not* covered by this development:

* the asymptotic statements of Lemmas 2.1 and 2.4 (`q_j = p ν_j^β (1+o(1))`, `ρ_j = m_j/√n + O(Q/√n)`,
  the two-sided spacing (2.15));
* the lower half of the growth estimate (1.3), hence the exact order two and type `1/2`
  (only the upper bound and the elementary lower bound `le_F_re_of_isSupp` are proved);
* the annular/sector zero-counting asymptotic (4.3) `N_n(S) = (ω/2π)(b-a)√n + O(n^{1/3})`
  and the limiting-measure statement (1.5) of Section 4;
* the two-term regime and the cofinite theorem for general `4/3 < p < 2` (only `p = 3/2` is
  formalized; the tail, model and minimum-modulus lemmas are however stated for general `p`);
* the critical exponent `p = 4/3` of Section 5 (bilateral Gaussian series, compactness of
  rescalings) and the Jensen-formula step of Lemma 5.1.
