# Lean 4 Math Showcase

本仓库收录若干 Lean 4 / mathlib 形式化项目，重点记录各项目的数学内容、依赖边界和可检查性。

目前包括三部分：

- 顶层 `Lean4MathShowcase`：三个相对独立的初等分析与不等式例子。
- [`projects/affine-prym-formalization`](projects/affine-prym-formalization)：一个 Affine-Prym 论证的线性代数形式化与依赖边界记录。
- [`projects/erdos-906-sparse-fock`](projects/erdos-906-sparse-fock)：Erdős Problem #906 的显式稀疏 Fock 构造、英文论文与 `p=3/2` Lean 形式化。

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

## Affine-Prym formalization

该子项目保留一个较早 Affine-Prym 论证的线性代数形式化。它明确区分 Lean 中已经证明的部分与仍作为外部输入的拓扑、表示论和代数几何结果。

它使用 Lean/mathlib `v4.28.0`，应从子项目目录构建：

```bash
cd projects/affine-prym-formalization
lake build RequestProject.Main
```

## Erdős Problem #906

该项目研究一个固定的显式稀疏 Fock 级数及其高阶导数零点在固定环带上的定量几何。主论文固定 `p=3/2`；更一般的研究方向单独保存在 `research/`，不计入当前形式化结论。

Lean 子项目单独构建：

```bash
cd projects/erdos-906-sparse-fock/formalization/lean
lake build RequestProject.Main
```

## Root project build

```bash
lake update
lake build
```

具体 Lean/mathlib 版本以各目录中的 `lean-toolchain` 和 Lake 配置为准。
