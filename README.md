# Lean4 数学证明精选

## 项目简介

一个简洁的 Lean4 数学证明展示仓库，收录了两份结构完整、适合公开展示的证明示例。

## 目录结构

```text
.
├─ LeanShowcase.lean
├─ LeanShowcase
│  ├─ TrigonometricExtrema.lean
│  └─ LogExtrema.lean
├─ lakefile.lean
├─ lean-toolchain
└─ README.md
```

## 收录证明简介

- `LeanShowcase/TrigonometricExtrema.lean`：讨论 `5 cos x - cos (5x)` 的区间极值、区间存在性结论与带相位偏移时的最小上界。
- `LeanShowcase/LogExtrema.lean`：研究函数 `(a + 1)x - (x + 1) log x` 的切线性质，以及两个极值点位置所满足的和式估计。

## 使用方法

```bash
lake update
lake env lean LeanShowcase.lean
```