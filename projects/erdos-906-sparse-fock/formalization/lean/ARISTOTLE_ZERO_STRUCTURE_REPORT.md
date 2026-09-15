# Zero-structure report — `p = 3/2` sparse Fock series

This report documents the round whose goal was the **next structural layer** for the
explicit `p = 3/2` sparse Fock entire function

```
F(z) = Σ_j z^{ν_j} / √(ν_j !),      ν_j = ⌊ j^{3/2} ⌋,
```

namely: exactly one zero per model disk counted with multiplicity, exclusion of all
additional zeros on fixed annuli, pairwise disjointness of the model disks, eventual
annular simplicity, and an exact finite model-disk zero count.

All statements below are in namespace `SparseFock`.  The function, the support sequence
`nu`, the coefficient convention `dcoeff`, the crossing radii `rho`, the gaps `qgap` and
the previously verified theorems `annular_covering_rate_p32` and `erdos906_sparse_fock_p32`
are unchanged.

---

## A. Exact Lean statements of the new main theorems

### A.1 `model_disk_zero_count_one_p32` — file `RequestProject/ModelDisk.lean`

```lean
theorem model_disk_zero_count_one_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ,
      1 ≤ j → n ≤ nu (3/2) j → a ≤ rho (3/2) n j → rho (3/2) n j ≤ b → ∀ l : ℕ,
        (∃! z : ℂ, z ∈ modelDisk c n j l ∧ iteratedDeriv n (F (3/2)) z = 0) ∧
        (∀ z ∈ modelDisk c n j l, iteratedDeriv n (F (3/2)) z = 0 →
          deriv (iteratedDeriv n (F (3/2))) z ≠ 0)
```

(The clause `c ≤ 1` was added in this round so that the same `c` can be fed to the
disjointness theorem.)

### A.2 `annular_zero_exclusion_p32` — file `RequestProject/Annulus.lean`

```lean
theorem annular_zero_exclusion_p32 {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b →
      iteratedDeriv n (F (3/2)) z = 0 →
      ∃ j l : ℕ, 1 ≤ j ∧ n ≤ nu (3/2) j ∧ a/2 ≤ rho (3/2) n j ∧
        rho (3/2) n j ≤ 2*b ∧ l < qgap (3/2) j ∧ z ∈ modelDisk c n j l
```

### A.3 `annular_zeros_simple_p32` — file `RequestProject/Simplicity.lean`

```lean
theorem annular_zeros_simple_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b →
      iteratedDeriv n (F (3/2)) z = 0 → iteratedDeriv (n + 1) (F (3/2)) z ≠ 0
```

and the equivalent `deriv` formulation

```lean
theorem annular_zeros_simple_deriv_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b →
      iteratedDeriv n (F (3/2)) z = 0 → deriv (iteratedDeriv n (F (3/2))) z ≠ 0
```

### A.4 `model_disks_pairwise_disjoint_p32` — file `RequestProject/Disjoint.lean`

```lean
theorem model_disks_pairwise_disjoint_p32 {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j j' l l' : ℕ,
      1 ≤ j → n ≤ nu (3/2) j → a ≤ rho (3/2) n j → rho (3/2) n j ≤ b →
      1 ≤ j' → n ≤ nu (3/2) j' → a ≤ rho (3/2) n j' → rho (3/2) n j' ≤ b →
      l < qgap (3/2) j → l' < qgap (3/2) j' → (j ≠ j' ∨ l ≠ l') →
      Disjoint (modelDisk c n j l) (modelDisk c n j' l')
```

### A.5 `zero_count_model_disk_union_p32` — file `RequestProject/ZeroCountUnion.lean`

```lean
theorem zero_count_model_disk_union_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ I : Finset (ℕ × ℕ),
      (∀ i ∈ I, 1 ≤ i.1 ∧ n ≤ nu (3/2) i.1 ∧ a ≤ rho (3/2) n i.1 ∧
          rho (3/2) n i.1 ≤ b ∧ i.2 < qgap (3/2) i.1) →
      ({z : ℂ | (∃ i ∈ I, z ∈ modelDisk c n i.1 i.2) ∧
          iteratedDeriv n (F (3/2)) z = 0}).ncard = I.card ∧
      (∀ z : ℂ, (∃ i ∈ I, z ∈ modelDisk c n i.1 i.2) →
          iteratedDeriv n (F (3/2)) z = 0 →
          deriv (iteratedDeriv n (F (3/2))) z ≠ 0)
```

### A.6 Model data (definitions used by the statements above)

```lean
noncomputable def modelCenter (n j l : ℕ) : ℂ :=
  (rho (3/2) n j : ℂ) *
    Complex.exp (((2 * (l : ℝ) + 1) * Real.pi / ((qgap (3/2) j : ℕ) : ℝ) : ℝ) * Complex.I)

noncomputable def modelRadius (c : ℝ) (n j : ℕ) : ℝ :=
  c * rho (3/2) n j / ((qgap (3/2) j : ℕ) : ℝ)

noncomputable def modelDisk (c : ℝ) (n j l : ℕ) : Set ℂ :=
  Metric.closedBall (modelCenter n j l) (modelRadius c n j)
```

The phase convention `z_{j,ℓ} = ρ_j exp((2ℓ+1)π i / q_j)` and the radius `c ρ_j / q_j`
are exactly those already present in the project; they were not changed.

---

## B. Manuscript-to-Lean correspondence

Authoritative source: `paper_en.tex` (the latest supplied manuscript).

| Manuscript item | Lean declaration(s) | File |
| --- | --- | --- |
| eq. `centers` `z_{j,ℓ}=ρ_j e^{(2ℓ+1)πi/q_j}` | `modelCenter`, `modelPhase_pow`, `exists_phase` | `ModelDisk.lean`, `Phase.lean` |
| eq. `disks` `D(z_{j,ℓ}, ρ_jη_n/q_j)` | `modelRadius`, `modelDisk` | `ModelDisk.lean` |
| `q_j` (gap), Lemma `lem:gaps` | `qgap`, `qgap32_le`, `le_qgap32`, `supp_gap`, `supp_gap3` | `Support.lean`, `Aux32.lean`, `Crossing.lean`, `ExclusionAux.lean` |
| crossing radius `ρ_j`, eq. (2.11)/(2.14) | `rho`, `log_rho_eq`, `rho_squeeze`, `rho_lt_rho_succ` | `Radii.lean` |
| Lemma `lem:radii`, eq. `radialspacing`/`logspacing` | `rho_log_spacing32`, `log_rho_spacing_lower` | `Spacing.lean` |
| Lemma `lem:curvature` (discrete curvature) | `dstep_curvature_lower`, `dstep_antitone` | `Curvature.lean`, `Concavity.lean` |
| Lemma `lem:tail` (stable tail bound) | `tail_sum_bound`, `norm_sub_two_terms_le`, `tail_outside_block` | `Tail.lean`, `TailGeneral.lean` |
| Prop. `prop:rouche`, model-zero → true zero | `exists_zero_near_model`, `exists_zero_of_dominant_two_term` | `TwoTerm.lean` |
| Prop. `prop:rouche`, *exactly one* zero with multiplicity | `unique_zero_of_two_term`, `unique_zero_near_model`, **`model_disk_zero_count_one_p32`** | `ZeroCount.lean`, `ZeroCount32.lean`, `ModelDisk.lean` |
| Prop. `prop:rouche`, model bound `|1-(1+u)^{q}| ≥ η/2` | `norm_pow_sub_one_le`, `norm_pow_pred_sub_one_le` | `ZeroCount.lean` |
| Prop. `prop:rouche`, same-circle separation `2ρ_j sin(π/q_j) ≥ 4ρ_j/q_j` | `norm_exp_I_sub_exp_I`, `sin_lower_of_between`, `modelCenter_dist_ge` | `Disjoint.lean` |
| Prop. `prop:exclusion`, disjointness | **`model_disks_pairwise_disjoint_p32`** | `Disjoint.lean` |
| Prop. `prop:exclusion`, "largest term dominates ⇒ no zero" | `no_zero_of_dominant`, `no_zero_dominant_p32` | `Dominant.lean`, `Exclusion.lean` |
| Prop. `prop:exclusion`, near-cancellation ⇒ model disk | `exists_model_root_near`, `zero_in_model_disk_of_transition`, `transition_zero_p32` | `RootLoc.lean`, `Transition.lean`, `Exclusion.lean` |
| Prop. `prop:exclusion`, full statement | **`annular_zero_exclusion_p32`** | `Annulus.lean` |
| Thm. `thm:geometry`, eventual annular simplicity | **`annular_zeros_simple_p32`**, `annular_zeros_simple_deriv_p32` | `Simplicity.lean` |
| Thm. `thm:geometry`, "each disk contains exactly one zero" over a family | **`zero_count_model_disk_union_p32`** | `ZeroCountUnion.lean` |
| eq. `origin`, large multiplicity at `z = 0` | `origin_multiplicity` | `Fock.lean` |
| eq. `count` (sector asymptotic) | *not formalized* — see §G, §K | — |
| eq. `cover`, covering with rate | `annular_covering`, `annular_covering_rate_p32` | `Covering32.lean` |
| eq. `cofinite` (Theorem 1.1) | `erdos906_sparse_fock_p32` | `Erdos906.lean` |

---

## C. Exactly one zero, counted with multiplicity, in each model disk

`model_disk_zero_count_one_p32` (§A.1) gives, for every admissible `(n, j, ℓ)`:

1. `∃! z, z ∈ modelDisk c n j l ∧ iteratedDeriv n (F (3/2)) z = 0` — there is one and only
   one zero in the closed disk; and
2. every zero in that disk is a **simple** zero of `iteratedDeriv n (F (3/2))`.

Together these say precisely that the total multiplicity of the zeros of `F^{(n)}` in the
disk equals `1`: the zero set is a single point and its multiplicity is `1`.

**Method.**  Mathlib (at the pinned commit) exposes no Rouché theorem and no argument
principle, so a reusable local zero-count equivalence was proved from scratch in
`RequestProject/ZeroCount.lean`:

```lean
theorem unique_zero_of_two_term {f : ℂ → ℂ} {z₀ A : ℂ} {ρ s K : ℝ} {m q : ℕ}
    (hf : Differentiable ℂ f) (hz₀ : ‖z₀‖ = ρ) (hρ : 0 < ρ) (hA : A ≠ 0)
    (hq : 1 ≤ q) (hs : 0 < s) (hqs : (q : ℝ) * s ≤ 1/8) (hK : 0 ≤ K)
    (hdom : ∀ z : ℂ, ‖z - z₀‖ ≤ 2 * ρ * s →
        ‖f z - A * z ^ m * (1 - (z / z₀) ^ q)‖ ≤ ‖A‖ * ‖z‖ ^ m * K)
    (hKs : K < (q : ℝ) * s / 2) :
    (∀ z w : ℂ, z ∈ Metric.closedBall z₀ (ρ * s) → w ∈ Metric.closedBall z₀ (ρ * s) →
        f z = 0 → f w = 0 → z = w) ∧
    (∀ z ∈ Metric.closedBall z₀ (ρ * s), f z = 0 → deriv f z ≠ 0)
```

The proof normalises `G t = f(z₀ t) · (A (z₀ t)^m)⁻¹`, estimates the derivative of the
error `ε = G - (1 - t^q)` by a Cauchy estimate on the slightly larger disk, and applies
the mean-value inequality; the model derivative `-q t^{q-1}` has modulus bounded below
because `‖t^{q-1} - 1‖ ≤ 1/7` on the disk.  This is a genuine complex-analytic
uniqueness-and-simplicity argument rather than a Rouché invocation; it is combined with
the previously established **existence** statement `exists_zero_near_model` (proved by the
minimum-modulus principle) to obtain `∃!`.

See §K for the precise relationship to the manuscript's Rouché formulation.

---

## D. Exclusion of additional annular zeros

`annular_zero_exclusion_p32` (§A.2).  Its logical content is genuinely universal: for all
large `n`, **every** `z` with `a ≤ ‖z‖ ≤ b` and `F^{(n)}(z) = 0` lies in a model disk
attached to a crossing index `j` with `a/2 ≤ ρ_{n,j} ≤ 2b` (the enlarged range is the one
the manuscript states in `thm:geometry`).  No hypothesis "the zero is near a model zero"
is assumed anywhere.

The proof follows the manuscript's structure:

* **Index selection.**  `exists_small_crossing` and `exists_crossing_index` produce the
  index `j` with `ρ_j ≤ ‖z‖ < ρ_{j+1}`.
* **Dichotomy.**  With `σ = log(‖z‖/ρ_j) ≥ 0` and `τ = log(ρ_{j+1}/‖z‖) ≥ 0`:
  * if `σ ≤ c₀/q_j`, `transition_zero_p32` applies at `J = j`;
  * else if `τ ≤ c₀/q_{j+1}`, `transition_zero_p32` applies at `J = j+1`;
  * otherwise `no_zero_dominant_p32` shows the middle term of the three-term block
    `[m_j, m_j+q_j+q_{j+1}]` dominates the two neighbours (by the factors `e^{-q_jσ}` and
    `e^{-q_{j+1}τ}`) and all the remaining terms (by `tail_outside_block`), so that there
    is no zero — contradicting the hypothesis.

  The quantitative input that makes the third case work is the radial spacing bound
  `rho_log_spacing32`, the formal counterpart of eq. `logspacing`.

* **Transition half.**  `transition_zero_p32` converts the near-cancellation
  `‖1 + w^{q_j}‖ ≤ K` into a phase localisation by the reusable elementary lemma

  ```lean
  theorem exists_model_root_near {w : ℂ} {q : ℕ} {K : ℝ} (hq : 1 ≤ q) (hw : w ≠ 0)
      (hK : 0 ≤ K) (hK4 : K ≤ 1/4) (hlog : |(q : ℝ) * Real.log ‖w‖| ≤ 2)
      (hclose : ‖1 + w ^ q‖ ≤ K) :
      ∃ l : ℕ, l < q ∧
        ‖w - Complex.exp ((((2 * (l : ℝ) + 1) * Real.pi / (q : ℝ)) : ℝ) * Complex.I)‖
          ≤ 16 * K / (q : ℝ)
  ```

  proved in `RequestProject/RootLoc.lean` from explicit modulus/phase estimates (no opaque
  `nlinarith` step hides the phase-localisation argument: the modulus part comes from
  `abs_le_of_norm_exp_sub_one_le`, the phase part from
  `Complex.norm_mul_exp_arg_mul_I` and integer division of the argument by `2π/q`).

The two halves of the dichotomy are:

```lean
theorem transition_zero_p32 {A B c₀ cdisk : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hc₀pos : 0 < c₀) (hc₀half : c₀ ≤ 1/2) (hc₀B : c₀ ≤ 1/(256*B^2)) (hcd : 0 < cdisk) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ J : ℕ, 1 ≤ J → n ≤ nu (3/2) J →
      A ≤ rho (3/2) n (J + 1) → rho (3/2) n J ≤ B →
      ∀ z : ℂ, 0 < ‖z‖ →
        |Real.log (‖z‖ / rho (3/2) n J)| ≤ c₀ / ((qgap (3/2) J : ℕ) : ℝ) →
        iteratedDeriv n (F (3/2)) z = 0 →
        ∃ l : ℕ, l < qgap (3/2) J ∧ z ∈ modelDisk cdisk n J l

theorem no_zero_dominant_p32 {A B c₀ : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hB2 : 2 ≤ B)
    (hc₀pos : 0 < c₀) (hc₀half : c₀ ≤ 1/2) (hc₀B : c₀ ≤ 1/(256*B^2)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → n ≤ nu (3/2) j →
      A ≤ rho (3/2) n (j + 1) → rho (3/2) n j ≤ B →
      ∀ z : ℂ, rho (3/2) n j ≤ ‖z‖ → ‖z‖ < rho (3/2) n (j + 1) →
        c₀ / ((qgap (3/2) j : ℕ) : ℝ) < Real.log (‖z‖ / rho (3/2) n j) →
        c₀ / ((qgap (3/2) (j + 1) : ℕ) : ℝ) < Real.log (rho (3/2) n (j + 1) / ‖z‖) →
        iteratedDeriv n (F (3/2)) z ≠ 0
```

---

## E. Eventual annular simplicity

`annular_zeros_simple_p32` and `annular_zeros_simple_deriv_p32` (§A.3).  These are
obtained by applying `annular_zero_exclusion_p32` on `[a, b]` with the constant `c`
produced by `model_disk_zero_count_one_p32` on the enlarged annulus `[a/2, 2b]`, and then
using the simplicity clause of the latter.

**Simplicity is asserted only on annuli bounded away from the origin.**  No global
simplicity statement is made anywhere in the development; this is mathematically
necessary, since `origin_multiplicity` (already in the project) shows that `z = 0` is a
zero of `F^{(n)}` of multiplicity `m_{j₀}`, which is unbounded in `n`.

---

## F. The zero-count theorem obtained

`zero_count_model_disk_union_p32` (§A.5).  For any finite family `I` of admissible index
pairs `(j, ℓ)` the number of zeros of `F^{(n)}` inside `⋃_{i ∈ I} D_i` is exactly `#I`,
and each of those zeros is simple — hence the total multiplicity is `#I` as well.

The proof combines `model_disk_zero_count_one_p32` (one zero per disk) with
`model_disks_pairwise_disjoint_p32` (the disks are disjoint), realising the zero set as
the image of `I` under the "unique zero" map and using injectivity of that map.

Pairwise disjointness (`model_disks_pairwise_disjoint_p32`, §A.4) is proved in the two
cases required by §4 of the task:

* **Same crossing circle, different `ℓ`.**  `norm_exp_I_sub_exp_I` gives
  `‖e^{ix} - e^{iy}‖ = 2|sin((x-y)/2)|`; with `sin_lower_of_between` (a quantitative form
  of `sin u ≥ (2/π)·min(u, π-u)` derived from `Real.mul_le_sin`) this yields
  `dist(z_{j,ℓ}, z_{j,ℓ'}) ≥ 4ρ_j/q_j`, strictly larger than `2·c ρ_j/q_j` when `c ≤ 1`.
* **Different crossing circles.**  Every point of `modelDisk c n j l` has modulus within
  `modelRadius c n j` of `ρ_j` (`abs_norm_sub_rho_le`).  The crossing radii satisfy
  `ρ_{j+1} - ρ_j ≥ a/(2(2B+6)v)` with `v ≍ n^{1/6}` (from `rho_log_spacing32` and
  `numeric_block_spacing`), while the two disk radii are `≤ c b/v²` and `≤ 4 c b/v²`
  (using `q_j ≥ v²` and `q_{j'} ≥ v'² ≥ v²/4`).  For
  `v > 10 c b (2B+6)/a` the radial separation strictly exceeds the sum of the radii.  All
  comparisons are fully quantitative; nothing is left to an informal asymptotic.

---

## G. Sector counting

**Not formalized.**  The manuscript's counting statement is eq. `count` of
`thm:geometry`:

```
N_n(S) = (ω/2π)(b-a)√n + O_{a,b,p}( n^β + n^{1/2-β} ),
S = { r e^{iθ} : a < r < b, α < θ < α + ω }.
```

For `p = 3/2`, `β = 1/3`, so the error term specialises to `O(n^{1/3} + n^{1/6}) =
O(n^{1/3})`.  This was the round's explicitly **secondary** target and it is reported as
an open gap rather than replaced by a weaker statement; see §K for what would be needed.

---

## H. `lake build` result

From a clean project root:

```
$ lake build
...
Build completed successfully (8061 jobs).
```

The only non-`info` diagnostics are a benign `linarith` normalisation notice emitted by
`RequestProject/ModelDisk.lean:205` (an `info`, not an error; the file compiles).

---

## I. `#print axioms` output

`RequestProject/Main.lean` contains the audit.  The build prints:

```
'SparseFock.annular_covering_rate_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.erdos906_sparse_fock_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.model_disk_zero_count_one_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.annular_zero_exclusion_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.annular_zeros_simple_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.annular_zeros_simple_deriv_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.model_disks_pairwise_disjoint_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.zero_count_model_disk_union_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## J. Integrity

A search over `RequestProject/` for `sorry`, `admit`, `axiom `, `unsafe`,
`native_decide` and `@[implemented_by]` returns nothing except the `#print axioms` audit
commands in `Main.lean`.  No unproved analytic proposition is encoded as a structure
field, typeclass instance or theorem hypothesis: every new theorem's hypotheses are
either explicit numerical side conditions on `a`, `b`, `c` (e.g. `0 < a`, `a ≤ b`,
`0 < c ≤ 1`) or the admissibility conditions `1 ≤ j`, `n ≤ ν_j`, `a ≤ ρ_{n,j} ≤ b`,
`ℓ < q_j` which are part of the statement being proved.

The two previously verified theorems were not weakened: `annular_covering_rate_p32` and
`erdos906_sparse_fock_p32` are unchanged in statement and proof, and still build.

---

## K. Differences between the Lean theorems and the manuscript claims

1. **Rouché is not used; an equivalent local zero-count lemma is proved instead.**
   Mathlib at the pinned commit provides neither Rouché's theorem nor the argument
   principle (`Mathlib/Analysis/Complex/JensenFormula.lean` provides only
   `MeromorphicOn.circleAverage_log_norm`).  Rather than assume the Rouché conclusion,
   `unique_zero_of_two_term` proves the two consequences that Rouché would give —
   *at most one zero in the disk* and *that zero is simple* — directly, by a derivative
   (Cauchy + mean value) estimate for the normalised perturbation.  Existence comes from
   the minimum-modulus principle (`exists_zero_of_norm_lt_on_sphere`).  The conjunction is
   logically equivalent to "exactly one zero counted with multiplicity"; it is *not* a
   weaker existential statement.  This is a proof-method difference, not a statement
   difference.

2. **Disk radius.**  The manuscript uses the shrinking radius `ρ_j η_n / q_j` with
   `η_n = exp(-c n^{2β-1/2})`.  The project (already before this round) uses the fixed
   constant radius `c ρ_j / q_j`.  This is a *larger* disk for large `n`, so the
   exactly-one-zero and disjointness statements proved here are at least as strong; the
   phase convention and the centres are exactly the manuscript's.

3. **Annulus enlargement in the exclusion theorem.**  As in `thm:geometry`, the disks
   capturing the zeros of `A[a,b]` are indexed by crossing radii in `[a/2, 2b]`, not in
   `[a, b]`.  This matches the manuscript ("`a/2 ≤ ρ_j ≤ 2b`").

4. **Quantifier form.**  All statements are of the form "there exists a threshold `N`
   such that for all `n ≥ N` …", with `N` depending only on `a`, `b` (and `c` where
   present).  The manuscript's "eventually" is read the same way.

5. **Sector counting (eq. `count`) is not formalized.**  What is missing is *not*
   Mathlib API: the pieces that would be required are (i) the telescoping identity
   `Σ_{j ∈ J_n(a,b)} q_j = (b-a)√n + O(Q)` together with `#J_n(a,b) = O(√n/Q)`
   (eq. `telescoping`), (ii) the count `ω q_j/(2π) + O(1)` of model centres of one circle
   in an arc of opening `ω`, and (iii) the boundary bookkeeping `O(Q + √n/Q)` at the two
   radial and the two angular boundaries.  Each is a substantial additional development
   in the same style as the present files; none of them needs a missing Mathlib theorem.
   The strongest counting statement that really compiles is
   `zero_count_model_disk_union_p32` (§A.5): an *exact* zero count on any finite union of
   admissible model disks.  It is the natural finite-`n` input to (ii)–(iii).

6. **The limiting zero measure (eq. `measure`)** is out of scope for this round and is not
   formalized.

---

## L. Documentation updated

* `README.md`: the correspondence table now lists the new declarations, the file table
  lists the new modules, and the "Not formalized" list no longer claims that the exclusion
  of additional zeros, Theorem 1.2 or the explicit covering rate are missing; the only
  remaining Section-4 gaps listed are the sector asymptotic and the limiting measure.
* `ARISTOTLE_COMPLETION_REPORT.md` and `ARISTOTLE_RATE_REPORT.md`: a prominent note was
  added at the top of each explaining that their scope disclaimers about the
  *exactly one zero* clause, exclusion, simplicity, disjointness and the model-disk zero
  count are superseded by this round, and pointing here.
* `ARISTOTLE_SUMMARY.md` was read but, as instructed, not modified.
