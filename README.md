# Lean 4 Math Showcase

This repository collects several Lean 4 / mathlib formalization projects. Each project records the mathematical statement being formalized, the boundary between machine-checked arguments and external mathematical input, and the exact build environment.

## Projects

| Project | Mathematical content | Location |
| --- | --- | --- |
| Top-level examples | Elementary analysis and inequalities, including the extremal problem for $5\cos x-\cos(5x)$ | `Lean4MathShowcase/` |
| Affine--Prym formalization | Linear-algebraic part of an Affine--Prym argument, with external topological and algebro-geometric inputs stated separately | [`projects/affine-prym-formalization`](projects/affine-prym-formalization) |
| Erdős Problem #906 | Sparse Fock construction, paper, and a Lean formalization of the $p=3/2$ case | [`projects/erdos-906-sparse-fock`](projects/erdos-906-sparse-fock) |

## Top-level examples

| File | Content | Representative theorem |
| --- | --- | --- |
| `Lean4MathShowcase/TrigonometricExtrema.lean` | Extremal estimates for $5\cos x-\cos(5x)$ | `trig_maximum_on_Icc`, `cosine_interval_witness`, `least_phase_shift_upper_bound` |
| `Lean4MathShowcase/LogExtrema.lean` | Critical points and tangent-line calculations for logarithmic functions | `part1`, `two_extrema_sum_bounds` |
| `Lean4MathShowcase/RootFunctionBounds.lean` | Monotonicity and two-sided bounds for a root function | `a8_increasing_on_Ioc`, `a8_decreasing_on_Ici`, `root_function_gt_one`, `root_function_lt_two` |

The top-level project is imported by

~~~lean
import Lean4MathShowcase
~~~

## Affine--Prym formalization

This subproject preserves the linear-algebraic formalization of an earlier Affine--Prym argument. It explicitly separates the Lean-checked part from topological, representation-theoretic, and algebro-geometric results used as external input.

It uses Lean/mathlib `v4.28.0` and should be built from the subproject directory:

~~~bash
cd projects/affine-prym-formalization
lake build RequestProject.Main
~~~

## Erdős Problem #906

This project studies a fixed explicit sparse Fock series and the quantitative geometry of the zeros of its higher derivatives on a fixed annulus. The main paper treats $p=3/2$. Broader exploratory material is kept separately under `research/` and is not part of the formalized theorem.

Build the Lean project with

~~~bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
~~~

## Root project build

~~~bash
lake update
lake build
~~~

The exact Lean and mathlib versions are specified by the `lean-toolchain` and Lake configuration files in the relevant project directories.
