# Completion report — Erdős Problem 906 for the `p = 3/2` sparse Fock series

> **Note (superseded in part).** The scope disclaimers of this report describing
> the *exactly one zero* clause, the exclusion of additional zeros, eventual
> annular simplicity, disjointness of the model disks and the model-disk zero
> count as not formalized are **no longer accurate**.  All of these are now
> proved; see `ARISTOTLE_ZERO_STRUCTURE_REPORT.md`.  The remaining genuine gap
> is the sector zero-counting asymptotic of Section 4.

## A. Final theorem

**Name:** `SparseFock.erdos906_sparse_fock_p32` (file `RequestProject/Erdos906.lean`).

```lean
theorem erdos906_sparse_fock_p32 (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ z ∈ U, iteratedDeriv n (F (3/2)) z = 0
```

Here

```lean
def IsSupp (p : ℝ) (k : ℕ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ nu p j = k
noncomputable def nu    (p : ℝ) (j : ℕ) : ℕ := ⌊(j : ℝ) ^ p⌋₊
noncomputable def fcoeff (p : ℝ) (k : ℕ) : ℝ := if IsSupp p k then 1 / Real.sqrt (k !) else 0
noncomputable def F     (p : ℝ) (z : ℂ) : ℂ := sumSeries (fun k => (fcoeff p k : ℂ)) z
```

so `F (3/2) z = ∑_{j ≥ 1} z^{ν_j} / √(ν_j !)` with `ν_j = ⌊j^{3/2}⌋`, exactly the
function of the manuscript, and `iteratedDeriv` is Mathlib's iterated complex
derivative.  The quantifier structure is the genuine **cofinite** one:
`∃ N, ∀ n ≥ N`.

## B. Build

`lake build` from the project root completes successfully (8046 jobs, no errors,
no warnings other than the deliberate `#print axioms` info message).

## C. Axiom audit

`RequestProject/Main.lean` ends with

```lean
#print axioms SparseFock.erdos906_sparse_fock_p32
```

whose output during the build is

```
'SparseFock.erdos906_sparse_fock_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean/Mathlib axioms are used.

## D. Search for `sorry` / `admit` / custom axioms

```
$ rg -n "sorry|admit|^axiom|@\[implemented_by\]|unsafe" RequestProject/
(no matches)
```

There are no `sorry`s, no `admit`s, no `axiom` declarations, no
`@[implemented_by]`, no `unsafe`, and no `native_decide` anywhere in the project.

## E. Dependency chain

```
Support.lean        ν_j = ⌊j^p⌋, monotonicity, two-sided gap bounds
   │
Curvature.lean      Φ_{n,r}(m) = ½log((n+m)!) − log(m!) + m log r, differences d_{n,r}
   │                discrete curvature lower bound
Concavity.lean      telescoping of Φ, antitonicity of the differences,
   │                slope bounds at a crossing radius (left ≥ κ(q−1)/2, right ≤ −κ(q−1)/2)
Radii.lean          crossing radii ρ_j, exact formula, squeeze, monotonicity
   │
Fock.lean           F_p entire, termwise derivative formula F_p^{(n)} = ∑ dcoeff·z^m
   │
Tail.lean           GLOBAL TAIL DOMINATION: both full tails bounded via the two
   │                slope bounds (left tail (m₀+1)e^{−δQ}, right tail geometric)
MinModulus.lean     minimum-modulus zero detection (maximum principle applied to 1/f)
   │
TwoTerm.lean        two-term model A z^{m₀}(1 − e^{qw}) in the logarithmic variable,
   │                localisation of each model zero (exists_zero_near_model)
Aux32.lean          p = 3/2 support arithmetic, elementary exponential estimates
RadialBounds.lean   m_j = O(√n) from ρ_j ≤ b; radial spacing ρ_{j+1} − ρ_j
Crossing.lean       crossing identities and the p = 3/2 curvature/slope bounds
Phase.lean          the q model phases (e^{iθ})^q = −1, angular mesh 2π/q
IndexSelect.lean    selection of the crossing index bracketing a given radius
Numeric.lean        the purely numerical core of all the size comparisons
   │
Covering32.lean     ANNULAR COVERING (η-density of the zero set on {a ≤ |z| ≤ b})
   │
Erdos906.lean       ERDŐS 906 COFINITE THEOREM
```

## F. Correspondence with the manuscript

| Paper | Lean |
| --- | --- |
| `(1.2)` series `F_p`, support `ν_j = ⌊j^p⌋`, gaps `q_j` | `SparseFock.F`, `SparseFock.fcoeff`, `SparseFock.nu`, `SparseFock.qgap` |
| Lemma 2.1 (monotonicity and size of the gaps) | `nu_lt_nu_succ`, `one_le_qgap`, `qgap_le`, `le_qgap`; for `p = 3/2`: `nu32_le`, `le_nu32`, `qgap32_le`, `le_qgap32` |
| Lemma 2.2 (`F_p` is entire) | `F_differentiable`, `iteratedDeriv_F_differentiable` |
| `(2.5)` termwise derivative | `iteratedDeriv_F`, `iteratedDeriv_F_eq_dcoeff` |
| `(2.7)` factorial bounds | `log_factorial_lower`, `log_factorial_upper` |
| `(2.8)`, Lemma 2.3 (discrete curvature) | `dstep_eq`, `dstep_sub_dstep_succ`, `dstep_curvature_lower` |
| `(2.11)`, `(2.14)`, Lemma 2.4 (radial grid) | `log_rho_eq`, `rho_squeeze`, `rho_lt_rho_succ`, `sq_le_of_rho_le` |
| **(A)** active support scale, `m_j = O(√n)` on the annulus | `mOf_add_one_le_of_rho_le`, `le_mOf_add_qgap` |
| **(B)** sparse gap estimates `q_j ≍ n^{1/3}` for `p = 3/2` | `qgap32_le`, `le_qgap32` (used in `annular_covering` with `v = ⁴√j`, `q_j ∈ [v², 2v²]`) |
| **(C)** discrete concavity of the derivative weights | `Phi_sub_Phi`, `dstep_antitone`, `dstep_gap`, `crossing_slope_left`, `crossing_slope_right`, `Phi_le_left`, `Phi_le_right`, `crossing_slopes32` |
| Lemma 3.1 (**(D)** stable/global tail bound, full left and right tails) | `tail_term_left`, `tail_term_right`, `tail_sum_bound`, `norm_sub_two_terms_le` |
| **(E)** two-term model and its zeros `ρ e^{(2ℓ+1)πi/q}` | `exists_phase`, `exists_zero_of_dominant_two_term` |
| Proposition 3.2 (**(F)** Rouché transfer) | `exists_zero_of_norm_lt_on_sphere` (minimum-modulus principle) + `exists_zero_near_model` |
| **(G)** angular covering, mesh `2π/q_j` | `exists_phase` (the `|θ − arg w| ≤ π/q` clause) |
| **(H)** radial covering, spacing of consecutive `ρ_j` | `rho_succ_sub_rho_le`, `exists_crossing_index`, `exists_small_crossing` |
| **(I)** Section 4 annular covering | `annular_covering` |
| **(J)** `(1.1)`/`(eq:cofinite)`, Theorem 1.1 cofinite statement | `erdos906_sparse_fock_p32` |
| `(4.2)` multiplicity at the origin | `origin_multiplicity` |
| `(5.1)`, `(5.2)` majorant estimates | `Ssum_le`, `log_Ssum_le` |

## G. Differences between the formal theorem and the paper theorem

1. **Only `p = 3/2`.**  As requested, the general range `4/3 < p < 2` is not
   formalized.  Nothing in the chain was stated for general `p` unless it was
   needed as a reusable intermediate lemma (`Support.lean`, `Curvature.lean`,
   `Concavity.lean`, `Radii.lean`, `Tail.lean`, `TwoTerm.lean` are `p`-generic;
   the specialisation happens in `Aux32.lean` and downstream).

2. **Rouché is replaced by the minimum-modulus principle.**  Instead of Rouché's
   theorem we use `exists_zero_of_norm_lt_on_sphere`: if `f` is entire,
   `‖f‖ ≥ M` on a circle and `‖f(z₀)‖ < M` at its centre, then `f` has a zero in
   the closed disc.  It is proved in `MinModulus.lean` from Mathlib's maximum
   modulus principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`) applied
   to `1/f`.  This is a genuine complex-analytic argument, not a continuity
   surrogate; it yields *existence* of a zero in each localisation disc (which is
   all the covering theorem needs), but not the *uniqueness/exactly one* clause
   of Proposition 3.2.

3. **The covering rate is stated qualitatively, not as `n^{-1/6}`.**  The formal
   annular covering theorem is

   ```lean
   theorem annular_covering {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
       ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w : ℂ, a ≤ ‖w‖ → ‖w‖ ≤ b →
         ∃ z : ℂ, iteratedDeriv n (F (3/2)) z = 0 ∧ ‖z - w‖ ≤ η
   ```

   i.e. "for every `η > 0` the zero set is eventually `η`-dense on the annulus",
   which is exactly what the cofinite open-set theorem consumes.  **We report
   explicitly that the quantitative form with the explicit rate
   `dist(w, Zer(F^{(n)})) ≤ C n^{-1/6}` has *not* been formally extracted.**  The
   three error contributions appearing in the proof (`2ρ c₀/q_j`, `2πρ/q_j` and
   `ρ_{j+1} − ρ_j`) are the ones that would give it, but the statement as
   formalized only asserts that their sum can be made smaller than any prescribed
   `η` for `n` large.  This is a weakening of item (I) of the task and is
   deliberately not disguised.

4. **Out-of-scope items.**  As instructed, the endpoint `p = 4/3`, the limiting
   zero measure, exact zero counts in sectors, exclusion of additional zeros,
   eventual simplicity, optimisation of constants and any comparison/priority
   discussion are not formalized.

5. **No extra hypotheses.**  `erdos906_sparse_fock_p32` assumes only `IsOpen U`
   and `U.Nonempty`; every intermediate lemma used in its proof is discharged
   from these alone.

## H. Project state used for the successful build

* Lean toolchain: `leanprover/lean4:v4.28.0` (`lean-toolchain`).
* Mathlib: as pinned in `lake-manifest.json`.
* All twenty modules under `RequestProject/` are imported by
  `RequestProject/Main.lean`; the successful `lake build` is the state of the
  repository at the final commit of this session (see `git log -1`).
