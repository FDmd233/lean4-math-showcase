# Lean 4 Math Showcase

这里放一些用 Lean 4 / mathlib 整理的数学证明示例。目标很简单：每个文件尽量独立，打开后能看出数学内容，也能用 `lake build` 直接检查。

目前仓库分成三部分：

- 顶层 `Lean4MathShowcase`：三个偏初等分析和不等式的 Lean 证明示例。
- `projects/affine-prym-aristotle`：Affine-Prym 论文相关的独立形式化项目。它使用不同的 Lean/mathlib 版本，所以单独保留为一个 Lake project。
- `projects/erdos-906-sparse-fock`：Erdős Problem #906 的显式稀疏 Fock 构造、英文研究稿、文献/优先权边界，以及当前 Aristotle/Lean 形式化状态。

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

### Erdős Problem #906 sparse-Fock project

项目入口在 [`projects/erdos-906-sparse-fock`](projects/erdos-906-sparse-fock)。公开内容包括英文研究稿源码、优先权与文献边界、证明形式化依赖图和最新 Aristotle Round 4 的形式化状态说明。

该项目**不主张首次解决** Erdős #906；重点是显式确定性稀疏 Fock 构造以及额外的高阶导数零点几何。中文本科毕业论文与答辩材料没有放入公开目录。

目前最新 Aristotle Round 4 的原始 Lean archive 仍保存在项目资料中，但 ChatGPT 当前 GitHub 连接器无法导出该 Project-file 的原始字节，因此仓库中的状态文档明确区分“已审计的形式化结果”和“尚未同步到 GitHub 的 Lean 源码”，没有用占位代码冒充形式化工程。

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
│  ├─ affine-prym-aristotle/
│  └─ erdos-906-sparse-fock/
├─ lakefile.lean
├─ lean-toolchain
└─ README.md
```

## Notes

这个仓库不是大型定理库，更像是一个可持续整理的小型证明集。
顶层项目基于 Lean 4 与 mathlib4；具体版本以各自目录中的 `lean-toolchain` 和 Lake 配置为准。
