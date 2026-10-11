# Erdős 问题 #848

[English](README.md) | 中文

**定理** 对每个 $`N\ge1`$，若 $`A\subseteq\{1,\dots,N\}`$，且对所有 $`a,b\in A`$（允许 $`a=b`$），$`ab+1`$ 都不是无平方因子数，则

```math
|A|\le c_7(N)=\#\{n\le N:\ n\equiv7\pmod{25}\}=\Big\lfloor\frac{N+18}{25}\Big\rfloor ,
```

且剩余类 $`7\pmod{25}`$ 取到这个上界  这回答了 [erdosproblems.com](https://www.erdosproblems.com/848) 上的第 848 题（Erdős–Sárközy）

本仓库包含一个证明，以及完整的 Lean 4 形式化：

- **论文**：[`paper/erdos848.pdf`](paper/erdos848.pdf)（源文件 [`paper/erdos848.tex`](paper/erdos848.tex)）；详细的书面证明见 [`supplement/proof.md`](supplement/proof.md)（英文）
- **Lean**：[`Erdos848/`](Erdos848/) 中的 `Erdos848.erdos848 : ∀ N, Statement N`  `#print axioms` 只列出 `propext`、`Classical.choice`、`Quot.sound`  所有计算都由 Lean 内核求值（`decide +kernel`），没有使用 `native_decide`  从全新克隆构建可以通过；用 Lean 自带的 `leanchecker` 逐个重放所有含定义的模块，也全部通过

## 已有工作

Sawhney 证明了 $`N`$ 充分大时定理成立（[note](https://www.math.columbia.edu/~msawhney/Problem_848.pdf)，也见 arXiv:2511.16072 §IV.1），但没有给出显式门槛  **对所有 $`N`$ 的第一个完整证明（含 Lean 形式化）由 Alex Chengyu Li 给出**（[论文](https://ssrn.com/abstract=7230480)，[仓库](https://github.com/crabsatellite/erdos-848-squarefree-product)，2026 年 8 月）  本工作是独立完成的，走的是另一条路线：把 Sawhney 的筛法论证中的每个误差项都显式化

## 证明的划分

| 范围 | 方法 | Lean 中的定理 |
|---|---|---|
| $`N\ge1.6\times10^8`$ | 显式筛法引理（A′、B、C）、区间证书、尾部估计 | `analyticPart` |
| $`986\,747\le N\le1.6\times10^8`$ | 加强后的引理，346 个区间证书 | `statement_low` |
| $`N\le986\,746`$ | 把相容图着色成 $`c_7(N)`$ 个独立集，逐步重放检查 | `statement_small` |

另有一份独立的 C++ 着色，配合单独编写的重放检查程序，覆盖 $`N\le4\times10^8`$（日志见发布页 `logs-4e8`）

## 内容

- `paper/`：论文
- `supplement/proof.md`：详细的书面证明（引理、分情况讨论、证书、计算机验证）
- `Erdos848/`：Lean 4 + Mathlib 项目（见其 README）
- `code/`：精确证书检查程序（`n0_exact.py`、`check_cert.py`、`threshold/cert.c` 等）、着色程序（`incr.cpp`、`replay.cpp`），以及生成 Lean 数据的脚本（`kernel/`）
- `certificates/`：区间证书（Lean 用的是 `exact_lean_*.csv`；`threshold/intervals_lean.txt` 是 Lean 中第 10 节用的 346 个区间）

Lean 证明不需要信任这些程序：它们只产生数据，数据由内核检查

## 复现

```bash
# Lean（约 5 个 CPU 小时；单个模块内存不超过 9.3 GB）
cd Erdos848 && lake exe cache get && lake build

# N >= 1.6e8 的精确证书（约 1 分钟）
cd code
python3 n0_exact.py scan 1.6e8 1e12 1.005 ../certificates/exact_1.csv
python3 n0_exact.py scan 1e12 1e60 1.1 ../certificates/exact_2.csv
python3 n0_exact.py tail
python3 check_cert.py --exact ../certificates/exact_1.csv ../certificates/exact_2.csv

# 第 10 节的精确证书（C + GMP）
cd threshold
gcc -O2 -fopenmp -o cert cert.c -lgmp -lm
./cert ../../certificates/threshold/disc_table_97.txt ../../certificates/threshold/intervals_all.txt
```

## 审阅状态

证明、代码和 Lean 形式化主要由 AI（Claude，Anthropic）在作者的指导下完成：作者设定目标、选择方向，并做了少量人工干预  完整的论证经过了 Lean 内核检查  **数学部分尚未经过人类专家审阅**；也请检查 [`Erdos848/Erdos848/Basic.lean`](Erdos848/Erdos848/Basic.lean) 中的形式化陈述是否就是原题

## 许可证

代码和 Lean 项目以 [Apache License 2.0](LICENSE) 发布  论文（`paper/`）和书面文档（`supplement/` 与各 README）以 [CC BY 4.0](LICENSE-CC-BY-4.0.txt) 发布
