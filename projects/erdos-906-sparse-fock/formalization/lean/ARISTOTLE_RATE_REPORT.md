# Rate report — explicit `n^(-1/6)` annular covering for `p = 3/2`

> **Note (superseded in part).** The scope disclaimers of this report describing
> the *exactly one zero* clause, the exclusion of additional zeros, eventual
> annular simplicity, disjointness of the model disks and the model-disk zero
> count as not formalized are **no longer accurate**.  All of these are now
> proved; see `ARISTOTLE_ZERO_STRUCTURE_REPORT.md`.  The remaining genuine gap
> is the sector zero-counting asymptotic of Section 4.

## 1. Exact statement of `annular_covering_rate_p32`

File: `RequestProject/Covering32.lean`.

```lean
theorem annular_covering_rate_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w : ℂ, a ≤ ‖w‖ → ‖w‖ ≤ b →
        ∃ z : ℂ, iteratedDeriv n (F (3/2)) z = 0 ∧
          ‖z - w‖ ≤ C / ((n : ℝ) ^ ((1 : ℝ) / 6))
```

The exponent `(1 : ℝ) / 6` is a `Real.rpow` exponent, so `(n : ℝ) ^ ((1:ℝ)/6)` is the
genuine real sixth root of `n`; the bound is the division form of `C · n^(-1/6)`.
This is the requested quantitative statement, not an `η`-density statement.

## 2. The constant

The witness produced by the proof is the explicit

```
C = b * (2 + 2 * Real.pi + 12 / a)
```

(no optimisation attempted; the true sum of the three errors is bounded by
`b * (1 + 2π + 12/a) / v`, and the extra `b/v` of slack is what makes the final
`linarith` step robust). Positivity of `C` is proved from `0 < a ≤ b` and `0 < π`.

## 3. Threshold dependencies

The threshold is `N = max (max N₁ N₂) 1`, where

* `N₁` comes from `exists_small_crossing ha` (for `n ≥ N₁` some crossing radius lies
  below `a`, so the bracketing index exists);
* `N₂ = exists_threshold_pow_six (V + (4*b+8) + b + 12/a)`, which converts `n ≤ v^6`
  into the largeness `V + (4b+8) + b + 12/a ≤ v`;
* `V` is the largeness threshold returned by the existing `numeric_core`, invoked
  here with the **fixed** value `η = 1` (`numeric_core ha hab (η := 1) one_pos …`);
  its fifth (qualitative) conclusion is discarded (`obtain ⟨hnum1, hnum2, hnum3, hnum4, -⟩`).
  Hence no `η` enters either `C` or `N`, and the statement is not circular;
* the extra `max … 1` only guarantees `n ≥ 1`, i.e. `(n : ℝ) > 0`, so that the sixth
  root is positive.

`N` depends only on `a` and `b`.

## 4. The three component error bounds

With `v = ⁴√j` for the selected crossing index `j` (so `n ≤ v^6`, `q_j ≥ v²`,
`ρ_j ≤ b`, `v ≥ 3`, and `c₀ ≤ 1/2`), the existing proof supplies:

1. localisation: `‖z − ρ_j e^{iθ}‖ ≤ 2 b c₀ / q_j`  (hypothesis `hterm1`);
2. angular:      `‖ρ_j e^{iθ} − ρ_j e^{i arg w}‖ ≤ 2π b / v²`  (`hterm2`);
3. radial:       `‖ρ_j e^{i arg w} − w‖ ≤ 12 b / (a v)`  (`hterm3`);

and the triangle inequality `htri`. These are unchanged from the already verified
development (they use `exists_zero_near_model`, `qgap32_le`, `le_qgap32`,
`rho_succ_sub_rho_le`, `exists_crossing_index`, `exists_small_crossing`).

The new combination lemma is

```lean
theorem covering_rate_final {a b c₀ q v X : ℝ} {n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc₀ : 0 < c₀) (hc₀half : c₀ ≤ 1/2) (hv3 : 3 ≤ v) (hq : v^2 ≤ q) (hn : 0 < (n:ℝ))
    (hnv : (n:ℝ) ≤ v^6)
    (hX : X ≤ 2*b*(c₀/q) + 2*Real.pi*b/v^2 + 12*b/(a*v)) :
    X ≤ (b * (2 + 2*Real.pi + 12/a)) / ((n:ℝ) ^ ((1:ℝ)/6))
```

which internally shows `2 b c₀ / q ≤ b/v`, `2π b / v² ≤ 2π b / v`, so that the total
is at most `b(1 + 2π + 12/a)/v ≤ C/v`, and then converts `1/v` to `1/n^{1/6}`.

## 5. The sixth-root lemmas

```lean
theorem rpow_one_sixth_pow_six {x : ℝ} (hx : 0 ≤ x) : (x ^ 6) ^ ((1:ℝ)/6) = x

theorem inv_le_inv_sixthRoot_of_le_pow_six {x v : ℝ} (hx : 0 < x) (hv : 0 < v)
    (h : x ≤ v^6) : 1 / v ≤ 1 / (x ^ ((1:ℝ)/6))
```

Both are in `RequestProject/Covering32.lean` and are proved from standard Mathlib
`Real.rpow` lemmas (`Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow`,
`Real.rpow_pos_of_pos`, `one_div_le_one_div_of_le`); neither is `sorry`-ed nor uses
any unproved algebraic simplification. Applied with `x = n` and the existing
`hnv6 : (n : ℝ) ≤ v ^ 6`, they give `n^{1/6} ≤ v` and hence `1/v ≤ 1/n^{1/6}`.

## 6. Optional corollary

The previously existing qualitative theorem

```lean
theorem annular_covering {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w : ℂ, a ≤ ‖w‖ → ‖w‖ ≤ b →
      ∃ z : ℂ, iteratedDeriv n (F (3/2)) z = 0 ∧ ‖z - w‖ ≤ η
```

keeps exactly its former statement but is now **derived** from
`annular_covering_rate_p32` by taking `N' = max N (⌈(C/η)^6⌉₊ + 1)`. Consequently
`SparseFock.erdos906_sparse_fock_p32` is unchanged and still compiles verbatim.

## 7. `lake build`

`lake build` from the project root: **success**, 8046 jobs, no errors, no warnings
other than the deliberate `#print axioms` info messages.

## 8. `#print axioms` output

`RequestProject/Main.lean` ends with

```lean
#print axioms SparseFock.annular_covering_rate_p32
#print axioms SparseFock.erdos906_sparse_fock_p32
```

Build output:

```
'SparseFock.annular_covering_rate_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'SparseFock.erdos906_sparse_fock_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 9. Zero `sorry` / `admit` / custom axioms

A search over `RequestProject/` for `sorry`, `admit`, `axiom`, `unsafe` and
`native_decide` returns nothing except the two `#print axioms` audit commands in
`Main.lean`. No `@[implemented_by]` is present either.

## 10. Differences from the manuscript's `O(n^(-1/6))` statement

* The constant is the explicit, unoptimised `C = b(2 + 2π + 12/a)`; the manuscript
  states only the order of magnitude.
* The statement is existence of a zero within `C n^{-1/6}` of each annulus point;
  it does not assert uniqueness/simplicity of that zero, zero counts, the limiting
  zero distribution, or the exclusion of extra zeros. As before, the Rouché step is
  replaced by a minimum-modulus argument giving existence only.
* Only `p = 3/2` is covered; `p = 4/3` and general `p` remain out of scope.
