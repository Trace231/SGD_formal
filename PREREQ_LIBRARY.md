# 随机优化前提库：卡片目录与构建方法论

本文档记录了从 SGD 形式化证明中提炼出的数学基础设施，
以及基于"算法驱动的缺口发现"方法论构建随机优化前提库的完整计划。

---

## 一、缺口分类体系

在 Lean 4 / Mathlib 环境下，形式化证明卡住时，原因有且仅有三种：


| 类型               | 真正原因                          | 常见误判        |
| ---------------- | ----------------------------- | ----------- |
| **Level 1：完全缺失** | Mathlib 在该领域根本没有相关结论          | 以为是自己不会搜索   |
| **Level 2：组合缺失** | Mathlib 有 A、有 B，但没有 A→B 的桥接引理 | 以为需要一个全新定理  |
| **Level 3：形式错配** | Mathlib 有该结论，但维度/类型/curry形式不对 | 以为是 Level 1 |


**检测协议（Stub-Probe 方法）**：

1. 对每个数学步骤，只写 Lean 类型签名，用 `sorry` 占位（验证类型正确性）
2. 对每个 `sorry` 依次尝试：`exact?` → `apply?` → `simp?` → 手动 Mathlib 搜索
3. 根据探针结果分类：

```
exact? 匹配     → 无缺口，直接用
apply? 有方向   → Level 2，需要组合桥接
三探针全失败    → 进入 Level 1 vs Level 3 诊断：
    搜索到"差不多"的结论 → Level 3（形式变换）
    完全搜索不到          → Level 1（从头证明）
```

---

## 二、现有基础设施卡片目录

### 📦 文件：`SmoothDescent.lean`

**定位**：Level 3 缺口 — Mathlib 有标量 FTC，但没有 Hilbert 空间梯度形式的版本

  $$ f(x + d) \leq f(x) + \langle \nabla f(x),\, d \rangle + \frac{L}{2} \|d\|^2 $$

---

#### 卡片 SD-1：`hasDerivAt_comp_lineSegment`

**缺口类型**: Level 3（形式错配）

**数学含义**:
若 `f : E → ℝ` 在每点有梯度 `∇f(w)`，则沿线段参数化的复合函数
`φ(t) = f(x + t·d)` 的导数是 `⟪∇f(x + t·d), d⟫`。

**Mathlib 已有**:

- `HasGradientAt f (gradF w) w`：梯度定义
- `HasDerivAt.comp`：链式法则（标量导数版本）
- `hasDerivAt_id`、`.smul_const`、`.const_add`：线段参数化的导数

**缺失/错配原因**:
梯度（`HasGradientAt`）和标量导数（`HasDerivAt`）之间没有组合引理，
需要通过 `HasGradientAt → HasFDerivAt → HasDerivAt（内积形式）` 的链来连接。

**核心证明技巧**: **梯度-导数转换**

```
HasGradientAt f (gradF w) w
  → HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradF w)) w
  → 与线段参数化的 HasDerivAt 做 chain rule
  → 用 InnerProductSpace.toDual_apply_apply 还原为内积
```

**证明链**:

```
hgrad w → .hasFDerivAt → .comp_hasDerivAt (hline) → simp/rwa toDual_apply_apply
```

**触发算法**: SGD 非凸收敛定理（`descent_lemma` 的准备工作）

**典型调用模式**:

```lean
-- 在 integral_inner_gradient_segment 中作为 HasDerivAt 的来源
have hderiv : ∀ t, HasDerivAt (fun t => f (x + t • d)) (⟪gradF (x+t•d), d⟫) t :=
  fun t _ => hasDerivAt_comp_lineSegment hgrad x d t
```

---

#### 卡片 SD-2：`integral_inner_gradient_segment`

**缺口类型**: Level 3（形式错配）

**数学含义**:
Hilbert 空间梯度形式的微积分基本定理：
$$\int_0^1 \langle \nabla f(x + t \cdot d), d \rangle  dt = f(x+d) - f(x)$$

**Mathlib 已有**:

- `intervalIntegral.integral_eq_sub_of_hasDerivAt`：标量 FTC
- `ContinuousOn.intervalIntegrable`：连续函数可积

**缺失/错配原因**:
标量 FTC 工作在 `ℝ → ℝ`，而优化证明需要 `f : E → ℝ` 版本，
被积函数是内积 `⟪∇f(x+t·d), d⟫`（一个实值函数），
需要 SD-1 提供 `HasDerivAt`，再代入标量 FTC。

**核心证明技巧**: **降维后直接代入**

```
用 hasDerivAt_comp_lineSegment 把 Hilbert 空间问题化为标量问题
→ 直接代入 intervalIntegral.integral_eq_sub_of_hasDerivAt
→ simp 化简边界条件（t=0,1 时的表达式）
```

**触发算法**: SGD（`lipschitz_gradient_quadratic_bound` 的核心依赖）

---

#### 卡片 SD-3：`lipschitz_gradient_quadratic_bound`

**缺口类型**: Level 3（形式错配）

**数学含义**:
L-光滑函数的二次上界（优化中最基础的解析工具之一）：
$$f(x+d) \leq f(x) + \langle \nabla f(x), d \rangle + \frac{L}{2}d^2$$

**Mathlib 已有**:

- `LipschitzWith L gradF`：梯度 Lipschitz 条件
- `real_inner_le_norm`：Cauchy-Schwarz（内积 ≤ 范数乘积形式）
- `intervalIntegral.integral_mono_on`：积分的单调性

**缺失/错配原因**:
该结论在 Mathlib 中没有现成版本。
需要通过 FTC（SD-2）+ Lipschitz 估计 + 积分计算拼装。

**核心证明技巧**: **FTC + Lipschitz 积分估计**

```
f(x+d) - f(x)
  = ∫₀¹ ⟪∇f(x+t·d), d⟫ dt               [SD-2, FTC]
  = ∫₀¹ ⟪∇f(x), d⟫ + ⟪∇f(x+t·d)-∇f(x), d⟫ dt  [拆分基准项]
  ≤ ⟪∇f(x), d⟫ + ∫₀¹ L·t·‖d‖² dt         [Cauchy-Schwarz + Lipschitz]
  = ⟪∇f(x), d⟫ + L/2·‖d‖²                 [∫₀¹ t dt = 1/2]
```

**触发算法**: SGD（`descent_lemma` 直接调用此结论）

**典型调用模式**:

```lean
have h := lipschitz_gradient_quadratic_bound hgrad hsmooth.continuous hsmooth w (-(η • g))
-- 再通过 h1, h2 做代数变形得到 descent_lemma
```

---

### 📦 文件：`ConvexGradient.lean`

**定位**：Level 1 缺口 — 多维凸/强凸一阶条件在 Mathlib 中完全缺失

$$\text{凸情形：} \quad f(y) \geq f(x) + \langle \nabla f(x),\, y-x \rangle$$

$$\text{强凸情形：} \quad f(y) \geq f(x) + \langle \nabla f(x),\, y-x \rangle + \frac{\mu}{2}\|y-x\|^2$$

---

#### 卡片 CG-1：`convex_first_order_condition`

**缺口类型**: Level 1（完全缺失）

**数学含义**:
凸可微函数的一阶最优性条件（多维版本）：
$$f \text{ 凸} + \text{可微} \Rightarrow f(y) \geq f(x) + \langle \nabla f(x), y-x \rangle$$

**Mathlib 已有**:

- `ConvexOn.le_slope_of_hasDerivAt`：**标量**切线不等式（`f : ℝ → ℝ`）
- `ConvexOn.comp_affineMap`：凸函数与仿射映射复合保持凸性
- `AffineMap.lineMap`：线段仿射映射

**缺失原因**:
Mathlib 的凸分析库在多维情形缺乏与 `HasGradientAt` 接轨的 FOC。
标量版本（`ℝ → ℝ`）存在，但 Hilbert 空间版本不存在。

**核心证明技巧**: **线段降维到标量**

```
定义 g(t) = f(x + t·(y-x))
→ 通过 ConvexOn.comp_affineMap 得到 g 是凸函数（ℝ → ℝ）
→ 用 hasDerivAt_comp_lineSegment 得到 g'(0) = ⟪∇f(x), y-x⟫
→ 应用标量 le_slope_of_hasDerivAt：g'(0) ≤ (g(1)-g(0))/(1-0)
→ 化简得到结论
```

**触发算法**: SGD 凸收敛定理（`one_step_progress_convex` 的 FOC 步骤）

---

#### 卡片 CG-2：`strong_convex_first_order_condition`

**缺口类型**: Level 1（完全缺失）

**数学含义**:
强凸函数的一阶最优性条件（多维版本）：
$$f \text{ μ-强凸} + \text{可微} \Rightarrow f(y) \geq f(x) + \langle \nabla f(x), y-x \rangle + \frac{\mu}{2}y-x^2$$

**Mathlib 已有**:

- `strongConvexOn_iff_convex`：强凸 ⟺ `f(·) - μ/2·‖·‖²` 是普通凸函数
- `hasStrictFDerivAt_norm_sq`：`‖·‖²` 的导数
- CG-1（凸 FOC）

**缺失原因**: 同 CG-1，Mathlib 缺乏 Hilbert 空间的强凸 FOC。

**核心证明技巧**: **强凸→普通凸转化 + 代数恒等式**

```
令 h(w) = f(w) - μ/2·‖w‖²
→ strongConvexOn_iff_convex 给出 h 是凸函数
→ 计算 ∇h(w) = ∇f(w) - μ·w（用 hasStrictFDerivAt_norm_sq）
→ 对 h 应用 CG-1：h(y) ≥ h(x) + ⟪∇h(x), y-x⟫
→ 展开 h 定义，用 norm_sub_sq_real 和 real_inner_self_eq_norm_sq 整理
→ linarith 完成
```

**触发算法**: SGD 强凸收敛定理（`one_step_progress_sc` 的 FOC 步骤）

---

#### 卡片 CG-3：`convex_inner_lower_bound`

**缺口类型**: Level 1 的推论

**数学含义**:
$$\langle \nabla f(w), w - w^* \rangle \geq f(w) - f(w^*)$$

**证明**: 直接从 CG-1 取 `y = w`*，移项整理。

**触发算法**: SGD 凸收敛定理（`one_step_progress_convex` Step 4）

---

#### 卡片 CG-4：`strong_convex_inner_lower_bound`

**缺口类型**: Level 1 的推论

**数学含义**:  
$$ \langle \nabla f(w), w - w^* \rangle \geq \frac{\mu}{2}w - w^*^2 $$

**证明**: 从 CG-2 取 `y = w`*，用 `hmin w`（w* 是极小值点故 f(w) ≥ f(w*)），移项。

**触发算法**: SGD 强凸收敛定理（`one_step_progress_sc` Step 4，产生压缩系数 `(1-ημ)`）

---

### 📦 文件：`IndepExpect.lean`

**定位**：Level 2 缺口 — Mathlib 有 `IndepFun`、有 Fubini，但没有连接二者的实用组合

**结论1（有界方差搬运）**：

$$w_t \perp \xi_t,\quad \mathbb{E}*\nu[\|\nabla L(w, \xi)\|^2] \leq \sigma^2 \quad \Rightarrow \quad \mathbb{E}_P[\|\nabla L(w_t, \xi_t)\|^2] \leq \sigma^2$$*

**结论2（无偏性的期望形式）**：

$$w_t \perp \xi_t,\quad \mathbb{E}*\nu[\nabla L(w, \xi)] = \nabla f(w) \quad \Rightarrow \quad \mathbb{E}_P[\langle h(w_t), \nabla L(w_t, \xi_t)\rangle] = \mathbb{E}_P[\langle h(w_t), \nabla f(w_t)\rangle]$$*

---

#### 卡片 IE-1：`expectation_norm_sq_gradL_bound`

**缺口类型**: Level 2（组合缺失）

**数学含义**:
有界方差从样本分布 ν 搬运到概率空间 P 上：
$$(\forall w,\ \mathbb{E}_\nu[\nabla L(w,\cdot)^2] \leq \sigma^2)
\ +\ w_t \perp \xi_t
\ \Rightarrow\ \mathbb{E}_P[\nabla L(w_t, \xi_t)^2] \leq \sigma^2$$

**Mathlib 已有**:

- `indepFun_iff_map_prod_eq_prod_map_map`：独立性 ↔ 联合分布 = 边际乘积
- `integral_prod`：Fubini（乘积测度上的迭代积分）
- `integral_map`：推前测度下的积分换元
- `integrable_map_measure`：可积性在推前测度下的搬运
- `integral_mono`：积分的单调性

**组合缺失原因**:
上述每个工具单独存在，但 Mathlib 没有封装"当 X⊥Y 时，
E_P[f(X,Y)] = E_X[E_Y[f(x,Y)]]"这条完整路径。
每次使用需要手动完成 5 步连接且各步可积性类型必须精确匹配。

**核心证明技巧**: **独立性→乘积测度→Fubini→逐点估计**

```
∫_P ‖gradL(wt,ξt)‖²
  =[integral_map]         ∫_{P.map(wt,ξt)} ‖gradL p.1 p.2‖²
  =[IndepFun→prod_eq]     ∫_{(P.map wt)⊗ν} ‖gradL p.1 p.2‖²
  =[integral_prod/Fubini]  ∫_{P.map wt} (∫_ν ‖gradL w s‖²)
  ≤[hvar 逐点]             ∫_{P.map wt} σ²
  =[integral_const]        σ²
```

**关键辅助步骤**:

- `h_prod_eq`：`P.map(wt,ξt) = (P.map wt).prod ν`（由 IndepFun + h_dist 得到）
- `h_int_prod`：在乘积测度上的可积性（通过 `integrable_map_measure` 搬运）
- `IsProbabilityMeasure ν`：由 `h_dist ▸ isProbabilityMeasure_map` 推出

**触发算法**: SGD 三个收敛定理均使用（Step 5：有界方差步骤）

---

#### 卡片 IE-2：`expectation_inner_gradL_eq`

**缺口类型**: Level 2（组合缺失）

**数学含义**:
无偏梯度假设的期望形式：当 `wt ⊥ ξt` 且 `E_ν[∇L(w,·)] = ∇f(w)` 时，
$$\mathbb{E}_P[\langle h(w_t), \nabla L(w_t, \xi_t) \rangle]
= \mathbb{E}_P[\langle h(w_t), \nabla f(w_t) \rangle]$$

**Mathlib 已有**:

- IE-1 的所有工具（同样的乘积测度路径）
- `integral_inner`：Bochner 积分与内积的交换（`∫⟪v, f⟫ = ⟪v, ∫f⟫`）

**组合缺失原因**:
在 IE-1 的路径上，Fubini 之后内层积分是 `∫ s, ⟪h(w), gradL w s⟫ ∂ν`，
需要额外的 `integral_inner` 把 `h(w)` 拉出内积，再用无偏性，
这个组合在 Mathlib 中没有封装。

**核心证明技巧**: **乘积测度 + Fubini + 内积线性 + 无偏性**

```
∫_P ⟪h(wt), gradL(wt,ξt)⟫
  =[integral_map]         ∫_{P.map(wt,ξt)} ⟪h p.1, gradL p.1 p.2⟫
  =[IndepFun→prod_eq]     ∫_{(P.map wt)⊗ν} ⟪h p.1, gradL p.1 p.2⟫
  =[integral_prod/Fubini]  ∫_{P.map wt} (∫_ν ⟪h w, gradL w s⟫)
  =[integral_inner]        ∫_{P.map wt} ⟪h w, ∫_ν gradL w s⟫
  =[hunb 无偏性]           ∫_{P.map wt} ⟪h w, gradF w⟫
  =[integral_map 反向]     ∫_P ⟪h(wt), gradF(wt)⟫
```

**设计亮点**:
`h : E → E` 是自由参数，使得这个引理同时覆盖：

- 非凸情形：`h = gradF`，证明 `E[⟪∇f, g⟫] = E[‖∇f‖²]`
- 凸情形：`h = fun w => w - wStar`，证明 `E[⟪wt-w*, g⟫] = E[⟪wt-w*, ∇f⟫]`

**触发算法**: SGD 三个收敛定理均使用（Step 4：无偏性步骤）

---

### 📦 文件：`Main.lean` Section 5b

**定位**：Level 2 缺口 — 从 IID 结构推导出当前步骤的独立性

---

#### 卡片 MN-1：`sgdProcess_indepFun_xi`

**缺口类型**: Level 2（组合缺失）

**数学含义**:
SGD 过程在步骤 t 时与当前采样 ξt 独立：
$$w_t \perp \xi_t$$

**Mathlib 已有**:

- `iIndepFun`：无穷族随机变量的独立性
- `indep_iSup_of_disjoint`：不相交指标集的 σ-代数之间的独立性
- `Filtration`、`Adapted`：滤子和适应性

**组合缺失原因**:
Mathlib 有从 `iIndepFun ξ P` 提取子集独立性的工具，
但没有连接"自然滤子 ℱt = σ(ξ₀,...,ξt₋₁)"与"ξt 独立于 ℱt"的组合引理。

**核心证明技巧**: **σ-代数格分解 + 不相交集合独立性**

```
process t 适应于 ℱt = ⨆_{j<t} comap(ξj)
→ comap(process t) ≤ ℱt
→ {j | j < t} ∩ {t} = ∅（不相交）
→ indep_iSup_of_disjoint：ℱt ⊥ comap(ξt)
→ indep_of_indep_of_le_left：comap(process t) ⊥ comap(ξt)
→ 即 IndepFun (process t) (ξt) P
```

**触发算法**: SGD 三个收敛定理（在每个一步引理中是 IE-1/IE-2 的前提）

---

## 三、依赖关系图

```
SmoothDescent.lean
  SD-1 hasDerivAt_comp_lineSegment
   └─→ SD-2 integral_inner_gradient_segment
        └─→ SD-3 lipschitz_gradient_quadratic_bound
                  └─→ Main.lean: descent_lemma

ConvexGradient.lean（依赖 SD-1）
  CG-1 convex_first_order_condition
   ├─→ CG-3 convex_inner_lower_bound
   └─→ CG-2 strong_convex_first_order_condition（依赖 CG-1）
        └─→ CG-4 strong_convex_inner_lower_bound

IndepExpect.lean（独立）
  IE-1 expectation_norm_sq_gradL_bound
  IE-2 expectation_inner_gradL_eq

Main.lean Section 5b（依赖 Filtration/Adapted）
  MN-1 sgdProcess_indepFun_xi

Main.lean 收敛定理
  sgd_convergence_nonconvex
    ← SD-3, IE-1, IE-2, MN-1
  sgd_convergence_convex
    ← CG-3, IE-1, IE-2, MN-1
  sgd_convergence_strongly_convex
    ← CG-4, IE-1, IE-2, MN-1
```

---

## 四、构建方法论

### 核心工作流

```
选择探针算法
  ↓
查找数学收敛证明（教材/论文）
  ↓
翻译为 Lean Stub Checklist（全部 sorry，仅验证类型）
  ↓
对每个 Stub 运行 Stub-Probe：
  exact? → apply? → simp? → 手动搜索
  ↓
识别缺口类型（Level 1 / 2 / 3）
  ↓
按对应技巧填补胶水引理
  ↓
为每个新引理写卡片（上述格式）
  ↓
判断：提交 Mathlib PR？还是留在本库？
```

### 算法探针选择原则

选探针算法的目标是**最大化覆盖新类型的缺口**：


| 探针算法               | 预计新揭示的缺口        | 难度  |
| ------------------ | --------------- | --- |
| SGD（已完成）           | L-光滑、凸FOC、独立期望  | —   |
| Projected GD       | 投影算子非扩张性、约束版FOC | 低   |
| Subgradient Method | 次梯度、非光滑下降       | 中   |
| SVRG               | 双层采样的独立性结构      | 中   |
| AdaGrad            | 自适应步长、鞅方法       | 高   |


### 引理的 Mathlib PR 判断标准

提交给 Mathlib 的条件（需全部满足）：

- 结论足够通用，不含随机优化特定概念
- 证明不依赖本库的其他非 Mathlib 内容
- 有明确的使用场景（能举例在哪个 Mathlib 定理的证明中会用到）
- 满足 Mathlib 的风格规范（`@[simp]` 标注、`omit` 策略等）

---

## 五、下一步工作计划

### 阶段 0（已完成）：SGD 三种收敛的完整形式化

产出的 9 个引理构成本库的初始卡片集（见第二节）。

### 阶段 1（下一步）：Projected Gradient Descent 探针

**选择原因**：

- 数学上是 SGD 的自然扩展（只加一个投影步骤）
- 预计揭示 2 个新缺口（投影算子形式、约束 FOC），不会导致卡死
- 可以复用 IndepExpect 的全部基础设施

**预计 Stub Checklist**：

```
步骤 1：定义投影更新
  w_{t+1} = Proj_C(w_t - η·∇f(w_t))
  → 障碍：Proj_C 的 Lean 表达（Mathlib: nearest_point / proj_on?）
  → 预测：Level 3

步骤 2：投影的非扩张性
  ‖Proj_C(x) - Proj_C(y)‖ ≤ ‖x - y‖
  → 搜索：nonexpansive, NearestPtOn, proj_norm
  → 预测：Level 2（有分量，需要组合）

步骤 3：变分不等式（约束 FOC）
  ⟪∇f(w*), w - w*⟫ ≥ 0  对所有 w ∈ C
  → 搜索：variational_inequality, 无...
  → 预测：Level 1

步骤 4：距离递推
  ‖w_{t+1} - w*‖² ≤ ‖w_t - η·∇f(w_t) - w*‖²  [非扩张性]
  → 复用 norm_sub_sq_real 展开，同 SGD
  → 预测：无缺口

步骤 5：取期望
  复用 IE-1, IE-2, MN-1（IID 结构完全相同）
  → 预测：无缺口
```

### 阶段 2：提取跨算法通用模式

当两个以上的探针算法都用到同一个引理时，
将其提升为库的"核心引理"（而非某个具体算法的辅助引理）。

当前已满足此条件的候选：

- IE-1, IE-2：三个 SGD 定理全用，PGD 也会用 → **核心引理**
- MN-1：同上 → **核心引理**
- `norm_sub_sq_real` 展开模式：凸和强凸情形都用 → 提取为 **范式（pattern）**

---

*本文档随证明工作持续更新。每次完成新的引理，在第二节添加对应卡片；
每次完成新的探针算法，在第五节更新阶段状态。*