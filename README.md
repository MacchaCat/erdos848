# Erdős Problem #848

English | [中文](README.zh.md)

**Theorem.** For every $`N\ge1`$, if $`A\subseteq\{1,\dots,N\}`$ and $`ab+1`$ is not squarefree for all $`a,b\in A`$ (with $`a=b`$ allowed), then

```math
|A|\le c_7(N)=\#\{n\le N:\ n\equiv7\pmod{25}\}=\Big\lfloor\frac{N+18}{25}\Big\rfloor ,
```

and the residue class $`7\pmod{25}`$ attains the bound. This answers Problem #848 of [erdosproblems.com](https://www.erdosproblems.com/848) (Erdős–Sárközy).

This repository contains a proof and a complete Lean 4 formalisation:

- **Manuscript:** [`paper/erdos848.pdf`](paper/erdos848.pdf) (source [`paper/erdos848.tex`](paper/erdos848.tex)); the detailed written proof is [`supplement/proof.md`](supplement/proof.md).
- **Lean:** `Erdos848.erdos848 : ∀ N, Statement N` in [`Erdos848/`](Erdos848/). `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. Every computation is evaluated by the Lean kernel (`decide +kernel`); no `native_decide` is used. A build from a fresh clone succeeds, and `leanchecker` (shipped with Lean) replays every module that contains declarations without error.

## Prior work

Sawhney proved the theorem for all sufficiently large $`N`$ ([note](https://www.math.columbia.edu/~msawhney/Problem_848.pdf); see also arXiv:2511.16072 §IV.1), without an explicit threshold. **The first complete proof for all $`N`$, with a Lean formalisation, is due to Alex Chengyu Li** ([paper](https://ssrn.com/abstract=7230480), [repository](https://github.com/crabsatellite/erdos-848-squarefree-product), August 2026). The present work was done independently and follows a different route: Sawhney's sieve argument with every error term made explicit.

## How the proof is split

| Range | Method | In Lean |
|---|---|---|
| $`N\ge1.6\times10^8`$ | explicit sieve lemmas (A′, B, C), interval certificates, tail estimate | `analyticPart` |
| $`986\,747\le N\le1.6\times10^8`$ | strengthened lemmas, 346 interval certificates | `statement_low` |
| $`N\le986\,746`$ | a colouring of the compatibility graph into $`c_7(N)`$ independent sets, replayed step by step | `statement_small` |

An independent C++ colouring with a separately written replay checker covers $`N\le4\times10^8`$ (log in release `logs-4e8`).

## Contents

- `paper/`: the manuscript
- `supplement/proof.md`: the detailed written proof (lemmas, case analysis, certificates, computer verification)
- `Erdos848/`: the Lean 4 + Mathlib project (see its README)
- `code/`: the exact certificate checkers (`n0_exact.py`, `check_cert.py`, `threshold/cert.c`, …), the colouring programs (`incr.cpp`, `replay.cpp`), and the generators of the Lean data (`kernel/`)
- `certificates/`: the interval certificates (`exact_lean_*.csv` are the ones used in Lean; `threshold/intervals_lean.txt` are the 346 intervals of Section 10 used in Lean)

None of the programs has to be trusted for the Lean proof: they only produce data, which the kernel checks.

## Reproducing

```bash
# Lean (about 5 CPU hours; at most 9.3 GB of memory per module)
cd Erdos848 && lake exe cache get && lake build

# Exact certificates for N >= 1.6e8 (about 1 minute)
cd code
python3 n0_exact.py scan 1.6e8 1e12 1.005 ../certificates/exact_1.csv
python3 n0_exact.py scan 1e12 1e60 1.1 ../certificates/exact_2.csv
python3 n0_exact.py tail
python3 check_cert.py --exact ../certificates/exact_1.csv ../certificates/exact_2.csv

# Exact certificate of Section 10 (C + GMP)
cd threshold
gcc -O2 -fopenmp -o cert cert.c -lgmp -lm
./cert ../../certificates/threshold/disc_table_97.txt ../../certificates/threshold/intervals_all.txt
```

## Review status

The proof, the code and the Lean formalisation were produced mainly by an AI system (Claude, Anthropic), under the direction of the author, who set the goals and chose the directions, with a small number of manual interventions. The complete argument is checked by the Lean kernel. **The mathematics has not yet been reviewed by human experts**; please also check that the formal statement in [`Erdos848/Erdos848/Basic.lean`](Erdos848/Erdos848/Basic.lean) is the intended one.

## Licence

The code and the Lean project are released under the [Apache License 2.0](LICENSE). The manuscript (`paper/`) and the written documentation (`supplement/` and the README files) are released under [CC BY 4.0](LICENSE-CC-BY-4.0.txt).
