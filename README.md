# Lean 4 Math Showcase

这里放一些用 Lean 4 / mathlib 整理的数学证明示例。目标很简单：每个文件尽量独立，打开后能看出数学内容，也能用 `lake build` 直接检查。

目前仓库分成两部分：

- 顶层 `Lean4MathShowcase`：三个偏初等分析和不等式的 Lean 证明示例。
- `projects/affine-prym-aristotle`：Affine-Prym 论文相关的独立形式化项目。它使用不同的 Lean/mathlib 版本，所以单独保留为一个 Lake project。

## Contents

### Top-level examples

| 文件 | 内容 | 可检查的定理示例 |
| --- | --- | --- |
| `Lean4MathShowcase/TrigonometricExtrema.lean` | `5 cos x - cos (5x)` 的极值与上界 | `trig_maximum_on_Icc`, `cosine_interval_witness`, `least_phase_shift_upper_bound` |
| `Lean4MathShowcase/LogExtrema.lean` | 对数函数极值点与切线计算 | `part1`, `two_extrema_sum_bounds` |
| `Lean4MathShowcase/RootFunctionBounds.lean` | 根式函数的单调性和双边估计 | `a8_increasing_on_Ioc`, `a8_decreasing_on_Ici`, `root_function_gt_one`, `root_function_lt_two` |

统一入口是：

```lean
import Lean4MathShowcase
```

例如：

```lean
#check Lean4MathShowcase.TrigonometricExtrema.trig_maximum_on_Icc
#check Lean4MathShowcase.LogExtrema.two_extrema_sum_bounds
#check Lean4MathShowcase.RootFunctionBounds.root_function_lt_two
```

### Affine-Prym formalization subproject

独立子项目在 [`projects/affine-prym-aristotle`](projects/affine-prym-aristotle)。它对应论文 *A Rank (2g-1) Affine-Prym Construction and Its Scalar Two-Block Optimality*，主要形式化 lower-bound 证明链中的线性代数骨架，并把 Looijenga、Westwick 等结果作为命名外部输入记录下来。

因为该子项目使用 Lean/mathlib `v4.28.0`，而顶层 showcase 使用另一套版本，所以请从子项目目录单独构建。

## Build

顶层项目：

```bash
lake update
lake build
```

Affine-Prym 子项目：

```bash
cd projects/affine-prym-aristotle
lake build RequestProject.Main
```

## Repository layout

```text
.
├─ Lean4MathShowcase.lean
├─ Lean4MathShowcase/
│  ├─ TrigonometricExtrema.lean
│  ├─ LogExtrema.lean
│  └─ RootFunctionBounds.lean
├─ projects/
│  └─ affine-prym-aristotle/
├─ lakefile.lean
├─ lean-toolchain
└─ README.md
```

## Notes

这个仓库不是大型定理库，更像是一个可持续整理的小型证明集。
顶层项目基于 Lean 4 与 mathlib4；具体版本以各自目录中的 `lean-toolchain` 和 Lake 配置为准。
