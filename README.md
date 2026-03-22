# Lean4 数学证明展示

一个面向公开展示的 Lean4 / mathlib 小型项目，收录 3 个主题明确、可直接阅读的数学证明示例。

项目目标是形成一个：

- 结构简洁
- 命名统一
- 中文说明清晰
- 适合直接发布到 GitHub

的 Lean4 数学证明 showcase 仓库。

## 项目定位

这个仓库不是大型定理库，而是一个轻量级的 **Lean4 数学证明展示项目**。整体组织方式尽量向 Lean 社区常见公开项目靠拢，例如：

- [`leanprover/lean4`](https://github.com/leanprover/lean4)
- [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)

因此本项目采用了比较标准的展示方式：

- 使用 `lakefile.lean` 管理项目
- 使用统一入口 `LeanShowcase.lean` 汇总导出模块
- 每个 `.lean` 文件只承载一个相对独立的数学主题
- 在文件顶部给出中文背景说明，在文件末尾保留便于展示的定理别名

## 目录结构

```text
.
├─ LeanShowcase.lean
├─ LeanShowcase
│  ├─ TrigonometricExtrema.lean
│  ├─ LogExtrema.lean
│  └─ RootFunctionBounds.lean
├─ lakefile.lean
├─ lean-toolchain
├─ .gitignore
└─ README.md
```

## 模块简介

### 1. 三角函数极值示例
文件：`LeanShowcase/TrigonometricExtrema.lean`

围绕表达式 `5 cos x - cos (5x)`，证明了以下几类结论：

- 在区间 `[0, π/4]` 上的极大值
- 给定角度与区间时，满足余弦上界的点存在性
- 带相位偏移时，全局上界的最小值

可展示定理：

- `LeanShowcase.TrigonometricExtrema.trig_maximum_on_Icc`
- `LeanShowcase.TrigonometricExtrema.cosine_interval_witness`
- `LeanShowcase.TrigonometricExtrema.least_phase_shift_upper_bound`

### 2. 对数函数极值示例
文件：`LeanShowcase/LogExtrema.lean`

研究函数

```text
f(x) = (a + 1)x - (x + 1) log x
```

包含两类内容：

- `a = 0` 时切线方程的验证
- 当函数存在两个极值点时，极值点之和的双边估计

可展示定理：

- `LeanShowcase.LogExtrema.part1`
- `LeanShowcase.LogExtrema.two_extrema_sum_bounds`

### 3. 根式函数的单调性与估计
文件：`LeanShowcase/RootFunctionBounds.lean`

研究函数

```text
f(a, x) = 1 / sqrt(1 + x) + 1 / sqrt(1 + a) + sqrt((a * x) / (a * x + 8))
```

主要证明：

- 当 `a = 8` 时的分段单调性
- 一般情形下的双边估计 `1 < f(a, x) < 2`

可展示定理：

- `LeanShowcase.RootFunctionBounds.a8_increasing_on_Ioc`
- `LeanShowcase.RootFunctionBounds.a8_decreasing_on_Ici`
- `LeanShowcase.RootFunctionBounds.root_function_gt_one`
- `LeanShowcase.RootFunctionBounds.root_function_lt_two`

## 快速开始

### 构建项目

```bash
lake update
lake build
```

### 统一导入

```lean
import LeanShowcase

#check LeanShowcase.TrigonometricExtrema.trig_maximum_on_Icc
#check LeanShowcase.LogExtrema.two_extrema_sum_bounds
#check LeanShowcase.RootFunctionBounds.root_function_lt_two
```

## 适用场景

这个仓库适合：

- 作为个人 Lean4 / mathlib 学习展示项目
- 作为 GitHub 公开作品集中的数学证明示例
- 作为后续继续扩展的小型 Lean4 证明仓库

如果后续继续加入新题目，建议保持当前风格：

- 一个文件一个主题
- 主题名尽量直接反映数学内容
- 顶部用简洁中文说明背景
- 末尾保留便于外部引用的公开定理名

## 致谢

本项目基于 **Lean 4** 与 **mathlib4** 生态构建。

在项目组织方式与公开呈现风格上，参考了 Lean 社区中成熟且广泛使用的资料与仓库，尤其包括：

- `leanprover/lean4`
- `leanprover-community/mathlib4`
- *Mathematics in Lean*
- *Theorem Proving in Lean 4*

它们为 Lean 项目的模块划分、文档表达和社区规范提供了非常好的对照标准。