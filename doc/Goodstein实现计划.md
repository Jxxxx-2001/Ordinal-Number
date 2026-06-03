# Goodstein 定理形式化实现计划

> 目标：依据 `doc/集合论-古德斯坦.pdf` 的证明思路，在本项目（Coq 8.20 + MK 集合论）中完成
> `Goodstein.v` 的形式化。核心手段是用 **MKT128（超限递归定理）** 定义古德斯坦序列相关的递归函数，
> 并最终证明：从任意自然数出发的古德斯坦序列必然在有限步内归零。
>
> 本文档供后续实现时持续参照、逐项勾选。约定：序数乘法记 `⋅`、幂记 `^`、后继 `PlusOne`、
> 小于 `≺`（即 `∈`）、小等于 `≼`，`Φ` 为 0，`ω` 为最小无穷序数，`R` 为全体序数类。

---

## 1. 证明思路总览（来自 PDF）

古德斯坦定理的形式化分三层，每层依赖前一层：

1. **底-n 分解**（地基）：对底数 `n ≥ 2` 与数值 `m ≥ n`，存在唯一分解
   `m = n^t ⋅ k + b`，其中 `t = MaxinExp n m`（最大指数）、`1 ≤ k < n`（首项系数）、
   `b < n^t`（余项）、`t ≥ 1`。这是后续所有递归函数的展开依据。

2. **三个递归函数**（用 MKT128 / 强递归定义）：
   - `Sₙ(m)`：**换底算子**，把 m 的底-n 完全展开表示中的底 n 整体替换为 n+1。
     `Sₙ(m) = m`（当 `m < n`）；否则 `Sₙ(m) = (n+1)^{Sₙ(t)} ⋅ k + Sₙ(b)`。
   - `fₙ(m)`：**序数化算子**，把底 n 替换为 ω，落入真正的序数。
     `fₙ(m) = m`（当 `m < n`）；否则 `fₙ(m) = ω^{fₙ(t)} ⋅ k + fₙ(b)`。
   - `gₙ(m)`：**古德斯坦序列**，对下标 n 递归。`g` 起始于底 2：`g₂(m)=m`，
     `g_{n+1}(m) = Sₙ(gₙ(m)) − 1`（非零自然数减一 = 取前驱 `∪x`）。

3. **核心引理与下降论证**：
   - 引理 4.5.5(1)：`fₙ` 严格单调递增（`m < m' ⟹ fₙ(m) < fₙ(m')`）。
   - 引理 4.5.5(2)：`f_{n+1}(Sₙ(m)) = fₙ(m)`（换底后再序数化 = 直接序数化）。
   - 推论 4.5.7：序列 `⟨f_{n+1}(gₙ(m))⟩` 在序数中严格递减；序数无无穷下降链，
     故必有某步 `gₙ(m) = 0`，即古德斯坦序列归零。

---

## 2. 可行性结论

**方案可行，MKT128 是正确的工具。**

关键判断：`Sₙ(m)`/`fₙ(m)` 的递归调用是 `Sₙ(t)` 与 `Sₙ(b)`，其中 `t = MaxinExp n m` 且
`b`（余项）都严格小于 `m`。这是 **值递归 / 强递归（course-of-values recursion）**，而非简单前驱递归。
MKT128 给出的方程

```
∀ x, Ordinal_Number x -> h[x] = g[ h|(x) ]
```

中，步进函数 `g` 拿到的是 `h` 在 **所有** 前驱上的限制 `h|(x)`（其 `dom = x`），因此可在 `g` 内部
查 `h[t]`、`h[b]`（因为 `t, b ∈ x = m`）。这正是值递归所需的能力。

**已有可复用的模板：** [Cantor_Normal_Form.v:104](../Cantor_Normal_Form.v#L104) 的 `CNF_f`
已完整示范「用 MKT128 在 ω 上递归、用辅助函数 `G` 处理 `dom∉ω → μ` 边界」的写法
（配套 `Add_μ`、`G'`、`G''` 三个引理）。`Sₙ`/`fₙ` 的定义与递归方程推导可沿用这套模式。

**基础设施盘点：**

| 需要的工具 | 项目现状 | 位置 |
|---|---|---|
| 超限递归 MKT128 | ✅ 已封装 | [Sum_Function.v:3](../Sum_Function.v#L3)、[Cantor_Normal_Form.v:3](../Cantor_Normal_Form.v#L3) |
| 序数强归纳 | ✅ `R_Transfinite_Induction` | [Induction.v:6](../Induction.v#L6) |
| ω 上强归纳 | ✅ `ω_Transfinite_Induction` | [Induction.v:51](../Induction.v#L51) |
| 三分律 / 传递性 / 良序 | ✅ `Ord_Num_tri`、`trans_Ord_Num`、`Φ_is_First_Ord` | [Ordinal_Number.v](../Ordinal_Number.v) |
| 加/乘/幂及其序关系引理 | ✅ 较完整 | `R_Operation_{Add,Mult,Exp}.v` |
| 商余提取（除法的替代） | ✅ `Mult_R_PrOrder_c` | [R_Operation_Mult.v:765](../R_Operation_Mult.v#L765) |
| 最大指数 `MaxinExp` 及性质 | ✅ `MaxinExp`、`CNF_1`、`MiEisO` | [Cantor_Normal_Form.v:14](../Cantor_Normal_Form.v#L14) |
| 求和算子 `Sum` | ✅ `Sum` + `Sum_Lemma1..4` | [Sum_Function.v:223](../Sum_Function.v#L223) |
| 序数减法 / 前驱 | ❌ 无独立算子 | 用 `∪x`（后继前驱）+ Add 抵消引理临时处理 |
| 序数除法 | ❌ 无独立算子 | 用 `Mult_R_PrOrder_c` 提取 `First c`/`Second c` |
| 无穷下降链不存在 | ❌ 需新建 | 由良序性 `Φ_is_First_Ord` + 取像极小元导出 |

`Mult_R_PrOrder_c` 的精确签名（提取商与余数的关键工具）：

```coq
Theorem Mult_R_PrOrder_c : ∀ a b,
  Ordinal_Number a -> Ordinal_Number b -> PlusOne Φ ≼ a -> a ≺ b ->
   exists! c, c ∈ (R × R) /\ Second c ≺ a /\ b = a ⋅ (First c) + (Second c).
```

即对 `a ≺ b` 唯一存在 `c=[商,余]`，满足 `b = a⋅(First c) + (Second c)` 且 `Second c < a`。
底-n 分解正是以 `a := n^t`、`b := m` 调用它来获得 `k=First c`、`b余=Second c`。

---

## 3. 当前 `Goodstein.v` 状态评估

现有内容（约 37 行）：

- `cnf_m`（[Goodstein.v:8](../Goodstein.v#L8)）：底-n 分解的 **存在唯一性** 引理陈述，目前 `Admitted`。
  这是整个证明的地基，**必须先填**。
- `get_k` / `get_b`（[Goodstein.v:16](../Goodstein.v#L16)、[:23](../Goodstein.v#L23)）：试图用集合
  推导式从 `cnf_m` 中提取系数 k 与余数 b。**当前定义是坏的**——集合约束体最后是 `k = k`（恒真），
  根本没有按值约束 k/b，等同占位符。需要重写。
- `Sn_f`（[Goodstein.v:30](../Goodstein.v#L30)）：换底算子 `Sₙ` 的 `Fixpoint` 草稿，被注释掉。
  Coq 的 `Fixpoint` 无法直接表达「在 `t<m`、`b<m` 上递归」的值递归（不是结构递归），
  **这条路走不通，必须改用 MKT128**。

**结论：** 现有脚手架除 `cnf_m` 的陈述可用外，`get_k`/`get_b`/`Sn_f` 都需重做。

---

## 4. 难点分析（按严重程度排序）

### 难点 1（最硬）：引理 4.5.5(1) `fₙ` 严格单调递增
PDF 用对 `m` 的强归纳 + 三路分情况：比较两数的 `(指数 t, 系数 k, 余项 b)` 三元组字典序。
形式化要点：
- 必须建立「`ω^t⋅k + b`（`b<ω^t`, `1≤k<ω`）形式之间的序比较 = 对 `(t,k,b)` 的字典序比较」，
  本质是 CNF 顶项比较律。
- 严重依赖大量序数算术序引理（`ω^a⋅k` 与 `ω^c⋅j` 的比较、`Add` 的吸收律）。
  引理散落在 `R_Operation_{Mult,Exp}.v`，拼装工作量大。

### 难点 2：底-n 分解 `cnf_m`（当前 Admitted，必须先填）
对 `n≥2, m≥n`，分解 `m = n^t⋅k + b`（`1≤k<n`, `b<n^t`, `t=MaxinExp n m ≥1`）。
- **存在性 + 特征性质** 可仿 CNF 主定理用 `Mult_R_PrOrder_c` 提取商（参考
  [Cantor_Normal_Form.v:196](../Cantor_Normal_Form.v#L196) 提取 `First x` 的写法）。
  不必依赖完整 CNF 唯一性。
- `t = MaxinExp n m ≥ 1` 与 `n^t ≼ m` 由 `CNF_1`（[Cantor_Normal_Form.v:56](../Cantor_Normal_Form.v#L56)）
  和 `MiEisO` 给出。
- 项目 **无序数除法/减法算子**，全靠 `Mult` 序引理临时提取。

### 难点 3：`Sₙ`/`fₙ` 递归方程推导
用 MKT128 定义后得到抽象方程 `h[x]=g[h|(x)]`，要化简成可用递归等式：
`Sₙ(m)=m`（`m<n`）；`Sₙ(m)=(n+1)^{Sₙ(t)}⋅k+Sₙ(b)`（`m≥n`）。需展开步进函数 `G`、
证 `dom(h|(m))=m`、`(h|(m))[t]=h[t]` 等——即 `G'`/`G''`/`CNF_f` 那种繁琐 MK 证明。
要做 `Sₙ`、`fₙ` **两套**，且比 `CNF_f` 更难（值递归需查 `h[t]`、`h[b]` 两个非前驱点）。
每个约 100–200 行。

### 难点 4：引理 4.5.5(2) `f_{n+1}(Sₙ(m)) = fₙ(m)`
对 `m` 强归纳。归纳步用 `Sₙ` 保持分解结构（系数 k 不变、仅换底），并需 **辅助界引理**：
`b < n^t ⟹ Sₙ(b) < (n+1)^{Sₙ(t)}`，否则换底后「余项 < 底^指数」约束不成立。界引理需单独证。

### 难点 5：下降论证「序数无无穷下降链」
需一条项目当前 **没有** 的引理：不存在严格 ∈-递减的 `ω→R` 序列。可由良序性 / `Φ_is_First_Ord`
（取像集极小元导出矛盾）推出。另外 4.5.7 下标有 `+1/+2` 错位，须先证
`gₙ(m)>0 ⟹ S_{n+1}(gₙ(m))>0` 才能保证「−1」严格下降，易错。

### 难点 6：类型簿记（ω vs R）与「−1」
- `Sₙ`、`gₙ` 须证落在 ω 内；`fₙ` 一般落到真正序数（≥ω）。全程维护「哪个落 ω、哪个落 R」。
- `g_{n+1}(m)=S_{n+1}(gₙ(m))−1`：非零自然数「−1」即后继前驱 `∪x`，须处处保证非零。
  `gₙ` 对下标 n 是简单递归，比 `Sₙ`/`fₙ` 容易。

---

## 5. 分阶段实现计划（带依赖顺序与验证点）

每个阶段结束都以 `make -C /home/jxxxx/OrdinalNum Goodstein.vo` 编译通过为验证点，
且不引入新的 `Admitted`（除非该阶段明确标注为临时占位）。

### 阶段 0：准备与脚手架修正 ✅ 已完成
- [x] 清理 `Goodstein.v` 中坏掉的 `get_k`/`get_b`/`Sn_f`（已删除）。
- [x] 审视并调整 `cnf_m` 陈述：**乘法顺序由 `k ⋅ n^t` 改为 `n^t ⋅ k`**（底在左、系数在右）。
      理由：序数乘法不交换；此顺序与项目 CNF 约定 `α^γ ⋅ δ`、与 `Mult_R_PrOrder_c` 的产出
      `b = a ⋅ (First c) + (Second c)`、以及 `fₙ(m)=ω^{fₙ(t)}⋅k+fₙ(b)` 全部一致。
      **此约定后续所有阶段沿用。**
- **验证**：✅ `make Goodstein.vo` 通过（`cnf_m` 仍 `Admitted`）。

### 阶段 1：填 `cnf_m` —— 底-n 分解（地基）
- [ ] 证明 `n^t ≼ m`（`t=MaxinExp n m`）：用 `CNF_1` / `MiEisO`。
- [ ] 证明 `t ≥ 1`（因 `m ≥ n` 故 `n^1=n ≼ m`，`MaxinExp` 至少为 1）。
- [ ] 用 `Mult_R_PrOrder_c` 以 `a:=n^t, b:=m` 提取 `c=[k, b余]`：得
      `m = n^t⋅k + b余` 且 `b余 < n^t`。
- [ ] 证明 `1 ≤ k`（否则 `k=0 ⟹ m=b余<n^t≼m` 矛盾）与 `k < n`
      （否则 `k≥n ⟹ n^t⋅k ≥ n^{t+1} > m`，与 `t` 最大矛盾，用 `MaxinExp` 定义）。
- [ ] 组装为 `cnf_m`（存在唯一；唯一性可由 `Mult_R_PrOrder_c` 的 `exists!` 直接给出）。
- **验证**：`cnf_m` 不再 `Admitted`，编译通过。

### 阶段 2：定义系数/指数/余项提取算子
- [x] 基于阶段 1 的唯一 `c`，定义 `get_t n m := MaxinExp n m`（已有）、
      `get_k n m := First c`、`get_b n m := Second c`（用 `∩\{...\}` 取出）。重写当前坏定义。
- [x] 证明它们满足分解方程（`cnf_spec` 引理：`m = n^{get_t}⋅get_k + get_b` 及各约束）。
- **验证**：能 `rewrite` 出分解方程；`Print Assumptions cnf_spec` 仅标准公理。

### 阶段 3：定义换底算子 `Sₙ` 并证递归方程 ✅ 已完成
- [x] 仿 `G`/`CNF_f` 定义步进函数 `G_Sn n`，处理三情形：
      `dom∉ω→μ`；`m<n→dom(u)`；`m≥n→(n+1)^{u[get_t]}⋅get_k + u[get_b]`。
- [x] 用 MKT128 定义 `Sn n m`（仿 `Sum` 的 `∩\{...\}` 取值式定义，而非提取整个 `h`）。
- [x] 导出递归方程：`G_Sn'`（`m<n` 时 `h[m]=m`）与 `G_Sn''`（`m≥n`），
      并由 `Sn_spec` 落到 `Sn`：`Sn n m = m`（`m<n`）、
      `Sn n m = (n+1)^{Sn n t}⋅k + Sn n b`（`n≼m`）。
- [x] 证 `Sₙ(m) ∈ ω`（强归纳 `Sn_aux`，换底保持自然数性）。
- **验证**：✅ `make Goodstein.vo` 通过；`Print Assumptions Sn_spec` 仅标准公理，
      全文件 0 个 `Admitted`、17 个 `Qed`。

### 阶段 4：定义序数化算子 `fₙ` 并证递归方程 ✅ 已完成
- [x] 步进函数 `G_fn n` 把底换成 `ω`：`m≥n→ω^{u[get_t]}⋅get_k + u[get_b]`。
- [x] MKT128 取值式定义 `fn n m`，导出递归方程（`G_fn'`：`m<n→h[m]=m`；
      `G_fn''`：`n≼m→h[m]=ω^{h[t]}⋅k+h[b]`，局部前提 `h[t],h[b]∈R`）。
- [x] 证 `fₙ(m) ∈ R`（强归纳 `fn_aux`，落入真正序数）。
- **验证**：✅ `make` 通过；`Print Assumptions fn_spec` 仅标准公理，
      全文件 0 个 `Admitted`、22 个 `Qed`。

### 阶段 5：核心引理 4.5.5 ✅ 已完成
- [x] **界引理** `Sn_bound`：`b<n^t ⟹ Sₙ(b)<(n+1)^{Sₙ(t)}`（难点 4 前置）。
      由 `Sn_mono` + `Sn_pow` 走「单调路线」一步得出。
- [x] **4.5.5(2)** `fn_Sn`：`f_{n+1}(Sₙ(m)) = fₙ(m)`，对 m 强归纳。
- [x] **4.5.5(1)** `fn_mono`：`m<m' ⟹ fₙ(m)<fₙ(m')`，对 m' 强归纳 + 三元组字典序（难点 1）。
      先证了通用「顶项比较律」`top_term_lt`（base 参数化）作辅助。
- **验证**：✅ `make` 通过；`Print Assumptions fn_mono/fn_Sn/Sn_bound` 仅标准公理，
      全文件 0 个 `Admitted`、39 个 `Qed`。

### 阶段 6：古德斯坦序列 `gₙ` 与下降论证
- [ ] 定义 `gₙ`：对下标 n 递归（从底 2 起），`g_{n+1}(m)=S_{n+1}(gₙ(m))−1`（`−1`=`∪`）。
      可用 MKT128 在 ω 上、或直接用项目已有的 ω-递归封装。
- [ ] 证 `gₙ(m)∈ω`、以及 `gₙ(m)>0 ⟹ S_{n+1}(gₙ(m))>0`（保证 −1 有意义且严格下降）。
- [ ] **无穷下降链引理** `no_inf_descent`：不存在严格 ∈-递减 `ω→R` 序列（难点 5）。
- [ ] **下降步** `goodstein_descent`：当 `gₙ(m)>0` 时 `f_{n+2}(g_{n+1}(m)) < f_{n+1}(gₙ(m))`，
      由 4.5.5(2) + 4.5.5(1) + `−1` 严格性组合。
- **验证**：编译通过。

### 阶段 7：主定理 `Goodstein`
- [ ] 陈述：`∀ m ∈ ω, ∃ n ∈ ω, gₙ(m) = Φ`。
- [ ] 证明：反设恒 `>0`，则 `⟨f_{n+1}(gₙ(m))⟩` 是无穷下降链，与 `no_inf_descent` 矛盾。
- **验证**：`Goodstein` 定理无 `Admitted`，全项目 `make` 通过。

---

## 6. 依赖关系图

```
阶段1 cnf_m (底-n分解)
   │
   ├──> 阶段2 get_t/get_k/get_b 提取算子 + 分解方程
   │        │
   │        ├──> 阶段3 Sₙ 换底 (MKT128 + 递归方程 + ∈ω)
   │        │        │
   │        │        ├──────────────┐
   │        │        │              │
   │        └──> 阶段4 fₙ 序数化    │
   │                 │              │
   │                 ▼              ▼
   │            阶段5 ─ 4.5.5(2) fn_Sn  ← 依赖 Sₙ, fₙ, 界引理 Sn_bound
   │            阶段5 ─ 4.5.5(1) fn_mono ← 依赖 fₙ + 顶项比较律
   │                              │
   ▼                              ▼
阶段6 gₙ 序列 + no_inf_descent + goodstein_descent
                                 │
                                 ▼
                    阶段7 主定理 Goodstein
```

## 7. 风险与备选

- **工作量**：与整个 CNF 开发（约 2700 行）同量级。难点 1（单增）与难点 3（递归方程）
  是主要时间消耗。
- **若 `fn_mono` 过难**：可考虑改走「`fₙ(m)` 等于 m 的底-n CNF 的 ω-CNF 解释」路线，
  借用已证的 CNF 主定理 / `Sum` 性质，把单调性归约到 `Sum` 与 CNF 顶项比较。需评估改写成本。
- **唯一性依赖**：`cnf_m` 的唯一性若证明困难，先用存在性 + 显式定义的提取算子推进
  （`get_k`/`get_b` 以 `Mult_R_PrOrder_c` 的 `exists!` 见证为准），唯一性留到不影响主线时补。
- **`−1` 处理**：始终以「非零自然数 = 某后继 `PlusOne p`，其前驱 `∪(PlusOne p)=p`」的形式操作，
  避免引入独立减法算子。

## 8. 编译与提交约定

- 单文件编译：`make -C /home/jxxxx/OrdinalNum Goodstein.vo`
- 全量编译：`make -C /home/jxxxx/OrdinalNum`
- 修改 `_CoqProject` 文件列表后须重跑 `coq_makefile -f _CoqProject -o Makefile`。
- 每阶段完成、编译通过后提交一次（项目已绑定 `git@github.com:Jxxxx-2001/Ordinal-Number.git`）。
- 源文件风格：中文注释 + 英文代码；复用项目既有策略（`appA2H`/`appA2G`/`deand`/`TF`/`emf`/`New` 等）。

---

## 9. 实施记录

> 每阶段完成后在此追加：做了什么、关键决策、遇到的问题、验证结果。

### 阶段 0（准备与脚手架修正）— 完成
- **删除** `Goodstein.v` 中坏掉的 `get_k`/`get_b`（集合约束体恒为 `k=k`，未真正约束取值，
  等同占位符）与走不通的 `Sn_f` `Fixpoint` 草稿（值递归无法用结构递归 `Fixpoint` 表达）。
  事前已用 `grep` 确认无其它文件引用这些符号。
- **修正 `cnf_m` 陈述的乘法顺序**：`k ⋅ n^t` → `n^t ⋅ k`（底在左、系数在右）。
  关键决策：序数乘法不交换，此顺序同时匹配 ① 项目 CNF 约定 `α^γ ⋅ δ`；
  ② `Mult_R_PrOrder_c` 产出的 `b = a ⋅ (First c) + (Second c)`；③ `fₙ(m)=ω^{fₙ(t)}⋅k+fₙ(b)`。
  此约定后续所有阶段沿用。
- **保留** `cnf_m` 陈述（暂 `Admitted`）并补充说明注释；`One`/`Two`/`natural_num`/`get_t` 记号无冲突。
- **验证**：`make Goodstein.vo` 通过，无新增 `Admitted`（仅保留 `cnf_m` 这一处既有占位）。

### 阶段 1（填 `cnf_m` 底-n 分解）— 完成
**目标**：对 `n≥2, m≥n`，存在唯一 `c=[k,b]∈ω×ω`，使
`m = n^t·k + b`（`t=MaxinExp n m`），且 `1≤k`、`k<n`、`b<n^t`、`t≥1`。

**新增辅助引理**（均已 `Qed`，仅依赖 `classic`+`MK_Axiom`）：
- `nat_Ord : a ∈ ω -> Ordinal_Number a` —— ω 元素是序数（经 `ω⊂R`）。
- `Two_le_One_lt : a∈ω -> Two ≼ a -> One ≺ a` —— 由 `2≤n` 得 `1<n`。
- `MaxinExp_in_ω`：`t = MaxinExp n m ∈ ω`（先证 `n^t≼m<ω`，再用 Integer 遗传 `MKT132`）。
- `MaxinExp_maximal`：极大性 `m ≺ n^(t+1)`（仿 CNF 主证内联论证，反证 + `Exp_R_PrOrder_a`）。
- `MaxinExp_ge_One`：`t ≥ 1`（由 `n≤m` 得 `n^1=n≼m`，故 `1 ∈ {v:n^v≼m}`，取并集 ≥1）。
- `cnf_decomp_unique`：**分解唯一性核心**。`a·k+b = a·k'+b'` 且 `b,b'<a ⟹ k=k' ∧ b=b'`。
  证法：三分律比较 `k,k'`，`k≺k'` 时用 `Mult_Union'` 得 `a·k+b ≺ a·k'≼a·k'+b'` 矛盾；
  `k=k'` 后用 `Add_R_Cancellation` 消去得 `b=b'`。

**`cnf_m` 主证结构**：
1. 前置事实：`n,m` 序数化、`1<n`、`1≤m`、`CNF_1` 给出 `1≤n^t≼m`、`t∈ω`、极大性、`t≥1`、
   `n^t∈ω`（`ω_Exp_in_ω`）。
2. 先证存在性引理 `Hexists`（`∃ k b, ... `），按 `n^t≼m` 三分两路：
   - **`n^t ≺ m`**：用 `Mult_R_PrOrder_c (n^t) m` 提取商余对 `c`，展开为 `[u,v]`：
     - `v∈ω`（`v≺n^t∈ω`，`MKT132`）；`u∈ω`（`u≼n^t·u≼m`，`R_Mult_2`+`MKT132`）；
     - `1≤u`（否则 `u=0 ⟹ m=v<n^t≼m` 矛盾，`R_Add_1`）；
     - `u<n`（**极大性反证**：`n≼u ⟹ n^t·n=n^(t+1)≼n^t·u≼m`，与 `m<n^(t+1)` 矛盾）。
   - **`n^t = m`**：取 `k=1,b=0`，`m=n^t·1+0`（`Mult_R_PlusOneΦ`+`Add_R_Φ_r`）。
3. 组装 `exists! c`：取 `c=[k,b]`，满足性用 `MKT54a/b` 归约 `First/Second`；
   唯一性把任意 `c'=[k',b']` 经 `cnf_decomp_unique` 归约到 `k=k',b=b'`。

**遇到的坑（已解决）**：
- `rewrite Hmeq in Hlt`（`Hmeq:m=v`）会穿透 `let t:=MaxinExp n m` 把 `t` 里的 `m` 也改写，
  污染 `t`。改为反向 `rewrite <- Hmeq in Hb_lt`。
- `rdeHex` 的 `deand` 会把待用的合取假设 `Hc'props` 拆散导致 "No such hypothesis"。
  改为手动 `apply AxiomII in ... as [...]` 解构积成员，避免触碰 props。
- `New (...)` 自动命名不可预测，凡需引用结果处一律改 `pose proof ... as 显式名`；
  `False` 目标下用 `elim (MKT101 x)` 而非 `eapply MKT101`。

**验证**：`make Goodstein.vo` 通过；`Print Assumptions cnf_m` 仅显示
`classic / MK_Axiom / Class / In / Classifier`，**无 `admit` 泄漏**。全文件 0 个 `Admitted`。

### 阶段 2（提取算子 `get_k`/`get_b` 与分解方程）— 完成
**目标**：从 `cnf_m` 的唯一见证 `c` 中确定性地取出系数 `k`、余项 `b`，
得到可直接 `rewrite` 的分解方程。

**新增定义**：
- `cnf_wit n m := ∩ \{ λ c, <cnf_m 谓词矩阵逐字一致> \}` —— 确定描述
  （definite description）。`cnf_m` 保证该类是单点集 `[c0]`，`∩` 取回 `c0`。
  惯用法照搬 `Sum`（`Sum_Function.v`）的 `∩\{...\}` + `MKT44`。
- `get_k n m := First (cnf_wit n m)`、`get_b n m := Second (cnf_wit n m)`。
  （`get_t n m := MaxinExp n m` 阶段 0 已有，不变。）

**新增引理**（均 `Qed`，仅依赖标准公理）：
- `cnf_wit_eq`：`cnf_wit n m` 等于 `cnf_m` 的唯一见证 `c0` 且 `c0` 满足全部性质。
  证法：取 `cnf_m` 的 `c0` 与唯一性 `Huniq`，证 `\{...\}=[c0]`（正向用 `Huniq`
  得 `z=c0`，反向回填），再 `MKT44` 由 `∩[c0]=c0` 收尾。
  关键技巧：谓词类体量大，`rewrite` 无法语法匹配，先 `match goal with |- ∩ ?S => set (P:=S)`
  把它命名再 `eqext`。
- `cnf_spec`（**阶段 2 主结论**）：把分解方程与各约束直接落到 `get_k/get_b/get_t` 上——
  `m = n^(get_t)·(get_k) + (get_b)`、`1≤get_k`、`get_k<n`、`get_b<n^(get_t)`、
  `1≤get_t`、`get_k∈ω`、`get_b∈ω`。证法：`cnf_wit_eq` 取 `c0` 并 `rewrite Hwit`，
  解构 `c0∈ω×ω` 为 `c0=[u,v]`，用 `MKT54a/b` 把 `First/Second` 归约到 `u,v`。

**遇到的坑（已解决）**：
- 解构 `c0 ∈ ω×ω` 后 `subst c0` 会用 `Hwit : cnf_wit n m = c0` 反向把 `cnf_wit n m`
  还原，**撤销**上一步 `rewrite Hwit`，导致目标里 `First/Second` 匹配失败。
  改为不 `subst`，而用积成员等式 `Hcpair : c0 = [u,v]` 做 `rewrite`。
- `ω×ω` 成员经 `AxiomII` 解构出的合取顺序为 `[c0=[u,v]; u∈ω; v∈ω]`（等式在首位），
  起初按 `cnf_m` 里 `[u∈ω; v∈ω; 等式]` 的顺序命名导致错位；用临时文件 `Show.` 核对后修正。

**验证**：`make Goodstein.vo` 通过；`Print Assumptions cnf_spec` 仅显示
`classic / MK_Axiom / Class / In / Classifier`，**无 `admit` 泄漏**。
全文件仍 0 个 `Admitted`，9 个 `Qed`。全项目 `make` 干净通过。

### 阶段 3（换底算子 `Sₙ` 的定义与递归方程）— 完成
**目标**：定义换底算子 `Sn n m`，证其落在 ω 内并满足两条递归方程。

**新增定义**：
- `G_Sn n := \{\ λ u v, (dom(u)∉ω /\ v=μ) \/ (dom(u)∈ω /\ dom(u)≺n /\ v=dom(u))
  \/ (dom(u)∈ω /\ n≼dom(u) /\ v=(n+1)^{u[get_t n (dom u)]}·get_k n (dom u)+u[get_b n (dom u)]) \}\`
  —— 步进函数，三路结构仿 `Sum_Function.v` 的 `G f`。
- `Sn n m := ∩ \{ λ u, ∀ h, <h 满足 MKT128 方程> -> u = h[m] \}` —— **取值式**定义。
  关键决策：**不**像 `Sum`/`cnf_wit` 那样提取整个函数 `h`（MKT128 给的 `h` 其
  `dom` 是 `Ordinal`，可能是 `R`、非集合，`∩` 提取会失败），而是仿 `Sum f n` 提取
  单个值 `h[m]`（对 `m∈ω` 由 `Sn_aux` 保证 `h[m]∈ω` 故 `Ensemble`）。

**新增引理**（均 `Qed`，仅依赖标准公理）：
- `G_Sn_fun`：`G_Sn n` 是函数。三路两两冲突（`m<n` vs `n≼m`）用三分律+传递律排除。
- `G_Sn'`：MKT128 方程下 `m≺n ⟹ h[m]=m`。构造 `[h|(m),m]∈G_Sn n`（第二路）+`Property_Fun`。
- `G_Sn''`：MKT128 方程下 `n≼m ⟹ h[m]=(n+1)^{h[t]}·k+h[b]`。
  **前提改为局部** `h[get_t n m]∈ω`、`h[get_b n m]∈ω`（而非全局 `ran(h)⊂ω`——后者不成立，
  `h` 在非 ω 序数上取 `μ`），正好匹配强归纳。用 `MKT126c`（`(h|(m))[t]=h[t]`，仅需 `t∈dom(h|(m))`）
  化简，避免 `Property_res` 要求 `m∈dom(h)` 的循环依赖。
- `Exp_gt_exp`：`t ≺ n^t`（严格，`n≥2`）。ω 数学归纳；归纳步 `PlusOne t ≼ n^t ≺ n^(t+1)`
  分别用 `R_Add_1` 与 `R_Exp_3`。用于证 `get_t n m ≺ m`。
- `cnf_t_lt_m`：`get_t n m ∈ m`（`t ≺ n^t ≼ m`）；`cnf_b_lt_m`：`get_b n m ∈ m`（`b ≺ n^t ≼ m`）。
- `Sn_aux`（**核心强归纳**）：对**任意**满足 MKT128 方程的 `h`，`∀ m∈ω, m∈dom(h) ∧ h[m]∈ω`。
  用 `The_Second_Mathematical_Induction`：强归纳假设给出 `m ⊂ dom(h)` 故 `dom(h|(m))=m`
  （`MKT126b`+`MKT30`），从而 `h|(m)` 是集合（`MKT75`）；直接构造 `[h|(m),value]∈G_Sn n`，
  `value` 由归纳假设（`h[t],h[b]∈ω`，`t,b<m`）+`cnf_spec`（`k∈ω`）保证 `∈ω`，
  `Property_Fun` 得 `h[m]=value∈ω`，再由 `MKT69b'` 反推 `m∈dom(h)`。
- `Sn_spec`（**阶段 3 主结论**）：取 MKT128 见证 `h0`+唯一性，局部引理 `Sn_val: ∀m∈ω, Sn n m=h0[m]`
  （`∩\{...\}=[h0[m]]`，唯一性把任意 sat `h` 归约到 `h0`），由此得
  ① `m∈ω ⟹ Sn n m∈ω`；② `m≺n ⟹ Sn n m=m`（`G_Sn'`）；
  ③ `n≼m ⟹ Sn n m=(n+1)^{Sn n t}·k+Sn n b`（`G_Sn''`+`Sn_val` 对 `t,b∈ω`）。

**遇到的坑（已解决）**：
- `appoA2H H` 展开 `\{\λ u v,P\}\` 成员会**消耗原假设名**，产生 `H:Ensemble[x,y]` 与
  新假设 `H0:P x y`（析取式）；`deand` 不拆析取。正确 destruct 模式为
  `[[Ha Hb]|[[Ha [Hb Hc]]|[Ha [Hb Hc]]]]`，经 `coqtop` 交互逐步核对得出。
- 证 `f[x]=v` 用 `Property_Fun v f x (fun_proof) Hmem`（结论 `v=f[x]`，需 `symmetry`），
  **不能**用 `eqext`（那是集合外延，`f[x]` 是取值）。
- `Ensemble v`（`v` 是序数运算结果）用 `exists ω; auto`（值落 ω）或 `exists R; auto`；
  不能 `apply MKT19`（它是 `iff` 非函数）。
- `G_Sn'` 结论 `h[m]=m` **不含 `n`**，`apply G_Sn'` 无法推断 `n`，须显式 `apply (G_Sn' n h0 m)`。
- MKT128 唯一性 `Hu0` 方向是 `h0 = x'`，归约任意 sat `h` 时需 `symmetry; apply Hu0`。
- `The_Second_Mathematical_Induction` 须显式提供谓词 `P` 并分别给 `P Φ`（用 `Hstep Φ`+空真前提）
  与 step；`P Φ` 中 `j≺Φ` 的矛盾用 `exfalso; apply (@MKT16 j)`（`emf` 对 `≺Φ` 记号不匹配）。

**验证**：`make Goodstein.vo` 通过；`Print Assumptions Sn_spec` 仅显示
`classic / MK_Axiom / Class / In / Classifier`，**无 `admit` 泄漏**。
全文件 0 个 `Admitted`、17 个 `Qed`。全项目 `make` 干净通过。

### 阶段 4（序数化算子 `fₙ` 的定义与递归方程）— 完成
**目标**：定义序数化算子 `fn n m`（把底换成 `ω`，落入真正序数 `R`）。

**与阶段 3 的对称改造**（`Sₙ` → `fₙ`，几乎逐行对应）：
- 步进函数底 `(PlusOne n)` → `ω`：`G_fn n` 第三路 `v = ω^{u[t]}·k + u[b]`。
- 值域 `∈ ω` → `∈ R`：`fₙ(m)` 落真正序数（`m≥n` 时 ≥ω），强归纳 `fn_aux` 证
  `∀m∈ω, m∈dom(h) ∧ h[m]∈R`。
- ω 封闭 `ω_{Add,Mult,Exp}_in_ω` → R 封闭 `R_{Add,Mult,Exp}_in_R`；
  `Ensemble v` 由 `exists ω` 改为 `exists R`。
- `G_fn''` 局部前提 `h[t]∈R`、`h[b]∈R`（替代 `∈ω`），底 `ω` 由 `MKT138`（`ω∈R`）供型；
  `get_k∈ω` 经 `nat_Ord` 升为 `∈R`。

**新增引理/定义**（均 `Qed`，仅标准公理）：
- `G_fn n`、`G_fn_fun`、`G_fn'`、`G_fn''`、`fn_aux`、`fn n m`、`fn_spec`。
- `fn_spec`（**阶段 4 主结论**）：`m∈ω⟹fn n m∈R`；`m≺n⟹fn n m=m`；
  `n≼m⟹fn n m=ω^{fn n t}·k+fn n b`。

**关键复用**：`Exp_gt_exp`、`cnf_t_lt_m`、`cnf_b_lt_m`、`cnf_spec`、`MKT126b/c`、
`The_Second_Mathematical_Induction` 等全部沿用阶段 3 的版本，无需重证。
m<n 分支证 `h[k]∈R` 时由 `nat_Ord`（`k∈ω→k∈R`）替代阶段 3 的 `auto`（`k∈ω`）。

**开发方式**：本阶段首次启用 `rocq-mcp` 工具——把对称改造后的整段代码写入临时文件
`stage4_tmp.v`，用 `rocq_compile_file` **一次性编译通过**（对称改造无误），
再整合进 `Goodstein.v`，`rocq_assumptions` 确认 `fn_spec` 仅依赖标准公理。

**验证**：`make` 全量通过；`Print Assumptions fn_spec` 仅
`classic / MK_Axiom / Class / In / Classifier`，**无 `admit` 泄漏**。
全文件 0 个 `Admitted`、22 个 `Qed`。



### 阶段 5（核心引理 4.5.5）— 完成
**目标**：证 `fₙ` 严格单调（4.5.5(1)）、`f_{n+1}∘Sₙ = fₙ`（4.5.5(2)）及其前置界引理 `Sn_bound`。

**关键架构决策——非循环依赖骨架**：直接对 m 强归纳证 `fn_mono`/`Sn_mono` 时，归纳步的
「t<t'」分支需要余项界 `fₙ(b)<ω^{fₙ t}`，而该界又需单调性，表面循环。破解办法：
把余项界**内联**进同一个强归纳——它由 `IH` 在 `n^t`（满足 `n^t≺m'`）上 + `fn_pow`
（`fₙ(n^t)=ω^{fₙ t}`）当场导出，`fn_pow` 自身不依赖单调性，从而闭环。

**新增引理（17 条，均 `Qed`，仅标准公理）**：
- **通用顶项比较律** `top_term_lt`（**全阶段基石**）：对 `base` 参数化，
  `(e,c,r)` 三元组字典序 ⟹ `base^e·c+r` 的序。`base=ω` 给 `fₙ` 比较，`base=n` 给底-n 比较
  （后者用于反证「错误方向」分支与 `m=m'` 情形）。核心工具 `Mult_Union'`
  （`a·b+c≺a·d ⟸ b≺d,c≺a`）+ `Exp_R_Suc` + 指数/乘法单调。
- **序工具**：`exp_le_imp_le`（`n^a≼n^b⟹a≼b`）、`lt_suc_imp_le`、`le_trans`、
  `one_le_ne`、`le_antisym`。
- **分解识别器** `decomp_recognizer`（**工作引擎**）：若 `M=base^e·k+r` 满足底-base 分解约束，
  则 `get_t/get_k/get_b base M = e,k,r`。证 `get_t=e` 用指数窗口唯一性
  （`base^e≼M≺base^{e+1}` 配 `CNF_1`/`MaxinExp_maximal` 反挤），`get_k/get_b` 用 `cnf_decomp_unique`。
- **幂值** `fn_pow`/`Sn_pow`：`f/S(n^s)=ω/(n+1)^{f/S(s)}`（识别 `n^s=n^s·1+0`）。
- **下界** `fn_ge_one`/`fn_ge_omega`、`Sn_ge_one`/`Sn_ge_succ`：服务于「`m<n` 而 `m'≥n`」分支
  （`fₙm=m<ω≤fₙm'`；`Sₙm=m<n+1≤Sₙm'`）。
- **单调** `fn_mono`/`Sn_mono`：对 `m'` 强归纳，casing `(t,t')×(k,k')×(b,b')` 三层三分律，
  正确方向用 `IH`+`top_term_lt`，错误方向用底-n `top_term_lt` 反推 `m'≺m` 与 `m≺m'` 矛盾。
- **界引理** `Sn_bound`：`Sₙ(b)<Sₙ(n^t)=(n+1)^{Sₙ t}`（`Sn_mono`+`Sn_pow`）。
- **4.5.5(2)** `fn_Sn`：对 m 强归纳，归纳步用 `Sn_bound`+`decomp_recognizer`(base n+1) 把
  `Sₙ(m)=(n+1)^{Sₙt}·k+Sₙb` 识别为底-(n+1) 分解，再套 `f_{n+1}` 递归方程 + `IH`。

**对称复用**：`Sₙ` 版（base 换 `ω`→`PlusOne n`、值域 `R`→`ω`、`R_*_in_R`→`ω_*_in_ω`）与
`fₙ` 版几乎逐行对应；`top_term_lt`、`decomp_recognizer`、所有序工具两套共用。

**开发方式**：全程用 `rocq-mcp` 交互（`rocq_start` 预热导入 + `rocq_check` 逐引理迭代），
最后 `rocq_compile_file` 整体校验线性一致，再整合进 `Goodstein.v`。

**遇到的坑（已解决）**：
- `Less x y := x ∈ y` 是 Definition（非 Notation），但 `assumption`/`auto` 按可转换匹配，
  故 `k∈ω` 可直接充当 `k≺ω`。
- `New (...)` 自动命名随上下文漂移（`H` vs `H0`），凡跨步引用一律改 `pose proof ... as 显式名`。
- `The_Second_Mathematical_Induction` 的基例 `P Φ`：对 `fn_mono`（`P` 含 `∀m∈mp`）用
  `intros;exfalso;MKT16`；对 `fn_Sn`（`P` 是等式、无 product）改用 `apply Hstep` + 空归纳假设。
- `MKT16` 形如 `x∉Φ`，矛盾推导用 `eapply MKT16; eauto`（非 `apply (@MKT16 Φ)`）。

**验证**：`make` 全量通过；`Print Assumptions fn_mono / fn_Sn / Sn_bound` 仅
`classic / MK_Axiom / Class / In / Classifier`，**无 `admit` 泄漏**。
全文件 0 个 `Admitted`、39 个 `Qed`。
