# Lean 4 Math Showcase

这里主要放我正在整理的 Lean 4 / mathlib 证明。这个仓库不追求做成大型定理库；我更在意每个子项目的数学内容、依赖边界和可检查性都尽量清楚。

目前有三部分：

- 顶层 `Lean4MathShowcase`：三个相对独立的初等分析/不等式例子。
- [`projects/affine-prym-formalization`](projects/affine-prym-formalization)：Affine-Prym 论文的线性代数形式化子项目。
- [`projects/erdos-906-sparse-fock`](projects/erdos-906-sparse-fock)：Erdős Problem #906 的显式稀疏 Fock 构造、英文论文和 `p=3/2` Lean 形式化。

## Top-level examples

| 文件 | 内容 | 定理示例 |
| --- | --- | --- |
| `Lean4MathShowcase/TrigonometricExtrema.lean` | `5 cos x - cos (5x)` 的极值与上界 | `trig_maximum_on_Icc`, `cosine_interval_witness`, `least_phase_shift_upper_bound` |
| `Lean4MathShowcase/LogExtrema.lean` | 对数函数极值点与切线计算 | `part1`, `two_extrema_sum_bounds` |
| `Lean4MathShowcase/RootFunctionBounds.lean` | 根式函数的单调性和双边估计 | `a8_increasing_on_Ioc`, `a8_decreasing_on_Ici`, `root_function_gt_one`, `root_function_lt_two` |

统一入口：

```lean
import Lean4MathShowcase
```

## Affine-Prym

这个子项目对应 *A Rank (2g-1) Affine-Prym Construction and Its Scalar Two-Block Optimality*。我把它看成一份 Lean 依赖审计：线性代数核心在 Lean 中展开，Looijenga、Westwick 以及尚未形式化的拓扑输入则明确留在外部假设一侧。

它使用 Lean/mathlib `v4.28.0`，应从自己的目录构建：

```bash
cd projects/affine-prym-formalization
lake build RequestProject.Main
```

## Erdős Problem #906

这个项目给出显式的稀疏 Fock 系列，并研究高阶导数零点在固定环带上的几何。公开目录包含英文论文、优先权说明以及 `p=3/2` 的 Lean 源码。项目不主张首次解决 #906；我更关心的是显式构造和可量化的零点定位。

Lean 子项目单独构建：

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

中文本科毕业论文和答辩材料不在这个公开仓库中。

## Root project build

```bash
lake update
lake build
```

具体 Lean/mathlib 版本以各目录中的 `lean-toolchain` 和 Lake 配置为准。
