# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 项目概要

这是一个使用 Coq 8.20 形式化序数算术的项目，基于 Morse-Kelley (MK) 公理化集合论。项目从序数的基本性质出发，逐步构建加法、乘法、幂运算，最终到达 Cantor 范式（Cantor Normal Form）和 Goodstein 定理的形式化。

## 构建命令

```bash
# 生成/更新 Makefile（修改 _CoqProject 后需要执行）
coq_makefile -f _CoqProject -o Makefile

# 构建整个项目
make -C /home/jxxxx/OrdinalNum

# 单独编译某个文件
make -C /home/jxxxx/OrdinalNum Cantor_Normal_Form.vo
```

编译产物：`.vo`（编译后的目标文件）、`.glob`（全局引用索引）、`.vos`/`.vok`（校验状态文件）。这些都在 `.gitignore` 之外，无需清理。

## 工作环境

- Coq 8.20，通过 opam switch `coq8.20` 管理
- 依赖 opam 包 `coq-morse-kelley-axiomatic-set-theory` 1.0.0（逻辑路径 `MorseKelley`）
- 使用 `coq_makefile` 构建系统（非 dune），配置由 `_CoqProject` 和 `Makefile.conf` 驱动
- 在 VS Code 中配合 VsRocq 扩展进行交互式证明

## 文件结构与依赖关系

项目文件在 `_CoqProject` 中按严格的线性依赖声明，每个文件 `Require Export` 其前驱：

```
Ordinal_Number.v   ← 序数基本定义、传递性、反对称性、三分律、后继/极限序数、上确界
  ↓
Recursion.v        ← 限制(restriction)推论、超限递归定理 (Recursion)
  ↓
Induction.v        ← 超限归纳法（三种形式）、ω 上归纳法
  ↓
R_Operation_Add.v  ← 序数加法（通过三函数递归定义 G1_A/G2_A/G3_A）
  ↓
R_Operation_Mult.v ← 序数乘法（G1_M/G2_M/G3_M 递归）
  ↓
R_Operation_Exp.v  ← 序数幂运算（G1_E/G2_E/G3_E 递归）
  ↓
Sum_Function.v     ← 超限递归定理 MKT128、求和算子 Sum、G 函数
  ↓
Cantor_Normal_Form.v     ← Cantor 范式：onTo/MaxinExp/Monodc_f/f 的定义与主定理 CNF
  ↓
Cantor_Normal_Form0.v    ← CNF 辅助引理和展开
  ↓
Cantor_Normal_Form1.v    ← CNF 进一步性质
  ↓
Goodstein.v        ← Goodstein 定理（未完成，含 Admitted）
```

另外两个文件处于早期探索阶段：
- `CNF_uni.v` — CNF 唯一性的公理化尝试（大量 Admitted）
- `CNF_uni'.v` — CNF 唯一性的另一路径（大量 Admitted）

`history/` 目录包含旧版本和实验代码，不参与构建。

## 核心约定

### MK 集合论基础

- 一切皆为 **Class**（无集合/真类之分，`Ensemble a` 表示 `a` 是集合）
- `R` 是所有序数构成的类，`μ` 是通用类
- `≺` 是序数间的小于关系（定义为 `∈`），`≼` 是小等于
- `Φ` 是空集/序数 0，`ω` 是最小无穷序数
- `PlusOne x` 是后继，`Suc_Ord`/`Lim_Ord` 分别表示后继序数和极限序数

### 常用证明策略

- `appA2H` / `appA2G` — 将集合定义展开为假设/目标（App to Hypothesis / App to Goal）
- `appoA2H` / `appoA2G` — 有序对的版本
- `deand` — 析取 H 中的 `∧`
- `New` — 引入一个新假设（类似 `pose proof`）
- `TF` — 排中律分析（`TF (P).` 产生 `P \/ ~P` 的分支）
- `emf` — 从 `x ∈ Φ` 推出矛盾
- `eqext` — 集合外延相等（extensionality）
- `rdeHex` — 析取存在量词
- `NSym` — 由自反性 `x ∈ x` 推出矛盾

### 命名约定

- `MKT` 开头的引理来自 MK 集合论标准库（如 `MKT101`、`MKT113a`）
- `Lemma`/`Theorem` 使用描述性名称，如 `Ord_Num_trans`（序数传递性）
- 递归定义采用 "三函数模式"：G1 处理零情况，G2 处理后继情况，G3 处理极限情况
- 加法使用符号 `+`、乘法使用 `⋅`、幂运算使用 `^`（均由相应的 `*Function_R` 定理递归定义）

### 形式化风格

项目采用“经典二值逻辑 + MK 集合论”风格。证明大量使用排中律（`TF`）和反证法（`NNPP`）。`Admitted` 出现在未完成的文件中（`CNF_uni.v`、`CNF_uni'.v`、`Goodstein.v` 部分定义）。

## 注意事项

- 本项目**不是** git 仓库（无版本控制），修改前请确认备份
- Coq 源文件编码为中文注释 + 英文代码
- `_CoqProject` 最后一行是中文注释，编辑时注意保留
- 修改 `_CoqProject` 中的文件列表后必须重新运行 `coq_makefile` 以更新 Makefile
