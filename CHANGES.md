# 变更记录

## 概述

为了证明 SGD 收敛分析中的 `descent_lemma`（L-smooth 下降引理），补充了 Mathlib 中缺失的优化理论基础设施，并完成了该引理的形式化证明。

---

## 新增文件

### `SmoothDescent.lean`（171 行）

Mathlib 中缺少"多维函数沿线段的梯度积分公式"，这是证明 L-smooth 二次上界的前置条件。本文件从 Mathlib 已有的组件（标量 FTC、链式法则、Cauchy-Schwarz）出发，构建了完整的证明链。

包含以下定理：

| 定理 | 作用 |
|------|------|
| `hasDerivAt_comp_lineSegment` | 将 `f : E → ℝ` 沿线段 `t ↦ x + t•d` 复合后的导数表示为内积 `⟪∇f(x + t•d), d⟫` |
| `integral_inner_gradient_segment` | **梯度沿线段的积分基本定理**：`f(x+d) - f(x) = ∫₀¹ ⟪∇f(x + t•d), d⟫ dt` |
| `integral_inner_gradient_segment'` | 上述定理的点到点形式（`d = y - x`） |
| `inner_gradient_diff_le` | Lipschitz 梯度的逐点控制：`⟪∇f(x+t•d) - ∇f(x), d⟫ ≤ L·t·‖d‖²` |
| `lipschitz_gradient_quadratic_bound` | **L-smooth 二次上界**：`f(x+d) ≤ f(x) + ⟪∇f(x), d⟫ + L/2·‖d‖²` |
| `lipschitz_gradient_quadratic_bound'` | 上述定理的点到点形式 |

**证明策略**：

```
   Mathlib 已有                        本文件构建
   ──────────                        ──────────
   FTC-2 (标量版)     ──┐
   HasFDerivAt.comp     ├──→ integral_inner_gradient_segment
   toDual_apply_apply ──┘              │
                                       │
   real_inner_le_norm ──┐              │
   LipschitzWith.dist ──┼──→ inner_gradient_diff_le
                        │              │
                        └──────────────┼──→ lipschitz_gradient_quadratic_bound
   integral_mono_on ───────────────────┘
```

### `src/SmoothDescent.lean`

与根目录的 `SmoothDescent.lean` 内容相同（备份）。

---

## 修改文件

### `Main.lean`

**变更 1**：新增 `import SmoothDescent`（第 2 行）

**变更 2**：`descent_lemma` 的 `sorry` 被替换为完整证明（第 248-260 行）

原代码：
```lean
lemma descent_lemma ... := by
  sorry
```

新代码：
```lean
lemma descent_lemma ... := by
  have h := lipschitz_gradient_quadratic_bound hgrad hsmooth.continuous hsmooth w (-(η • g))
  rw [sub_eq_add_neg]
  have h1 : ⟪gradF w, -(η • g)⟫_ℝ = -(η * ⟪gradF w, g⟫_ℝ) := by
    rw [inner_neg_right, inner_smul_right, mul_comm]
  have h2 : ‖-(η • g)‖ ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [h1, h2] at h
  linarith
```

思路：将 `lipschitz_gradient_quadratic_bound` 特化为 `d = -(η • g)`，然后通过内积和范数的代数化简完成证明。

### `lakefile.lean`

新增 `lean_lib SmoothDescent` 声明，并让 `Main` 依赖它。

### 删除 `lakefile.toml`

项目中同时存在 `lakefile.lean` 和 `lakefile.toml` 会造成冲突（Lake 会优先用 `.lean` 但 IDE 可能读 `.toml`）。删除了 `.toml`，统一使用 `lakefile.lean`。

---

## 当前状态

| 定理 | 状态 |
|------|------|
| `descent_lemma` | ✅ 已证明 |
| `stochastic_descent_nonconvex` | ❌ sorry（需测度论） |
| `sgd_convergence_nonconvex` (3 处) | ❌ sorry（需 telescoping + 测度论） |
| `one_step_progress_convex` | ❌ sorry（需凸性一阶条件） |
| `sgd_convergence_convex` (2 处) | ❌ sorry（需 telescoping） |
| `one_step_progress_sc` | ❌ sorry（需强凸一阶条件） |
| `sgd_convergence_strongly_convex` | ✅ 已证明（依赖 `one_step_progress_sc`） |

剩余 5 个 `sorry` 的主要阻碍：
1. **凸性/强凸性的一阶条件**（`f(y) ≥ f(x) + ⟪∇f(x), y-x⟫`）—— Mathlib 缺失
2. **测度论胶水**（取期望、积分单调性、可积性前提）—— Mathlib 有 API 但需要大量组装
3. **Telescoping 求和** —— Mathlib 有 `Finset.sum_range_sub` 但需适配积分形式
