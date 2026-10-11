# Erdős Problem #848: the detailed written proof (supplement to the manuscript)

> Status: 2026-10-11. The analytic part follows Sawhney's framework with every error term made explicit; the small-$`N`$ part is a computer verification.  
> Two rounds of adversarial review by AI sub-agents found no fatal error in the analytic part; the gap they pointed out (the worst case for $`S_b`$ in Lemma C) has been filled. No fatal problem was found in the computational part either. A further AI sub-agent re-implemented all bounds **from this text alone, without reading the code**: on 24 sampled intervals × 5 cases the main coefficients agree with the certificate to a relative error below $`10^{-8}`$, and every other difference makes the certificate more conservative. The four under-specified points it reported have been written into §4, §5 and §6.2. **Review by human experts is still needed.**  
> Code: `code/`; certificates: `certificates/`.  
> **Coverage:** the colouring for $`N\le4\times10^8`$ and two independent replays have passed (§7). Together with the analytic part ($`N\ge1.6\times10^8`$) they overlap on $`[1.6\times10^8,4\times10^8]`$ and cover every $`N`$. The correctness of the proof still awaits review by human experts.  
> **Strengthened version (§10, 2026-10-10):** with strengthened lemmas the analytic part covers all $`N\ge6\times10^5`$, so the computational part is only needed for $`N\le6\times10^5`$.  
> **Lean formalisation (§8):** the whole theorem is formalised, and every computation is evaluated by the Lean kernel (`decide +kernel`). **No `native_decide` is used**; the only axioms are `propext`, `Classical.choice` and `Quot.sound`. In Lean the split is $`N\le986\,746`$ (colouring), $`[986\,747,1.6\times10^8]`$ (Section 10) and $`N\ge1.6\times10^8`$ (Section 6).

## 0. Theorem

**Theorem.** For every positive integer $`N`$, if $`A\subseteq\{1,\dots,N\}`$ and $`ab+1`$ is not squarefree for all $`a,b\in A`$ (with $`a=b`$ allowed), then

```math
|A|\le c_7(N):=\#\{n\le N:\ n\equiv7\pmod{25}\}=\Big\lfloor\frac{N+18}{25}\Big\rfloor .
```

Since $`7\cdot7+1=50`$, the set $`\{n\le N: n\equiv 7\ (25)\}`$ itself satisfies the condition. Hence the maximum is exactly $`c_7(N)`$, which answers the Erdős–Sárközy question in the affirmative.

**Structure of the proof:**
- $`N\le 4\times10^8`$: computer verification (Section 7)
- $`N\ge 1.6\times10^8`$: explicit analytic argument (Sections 1–6)

The two ranges overlap on $`[1.6\times10^8,4\times10^8]`$ and together cover every $`N`$. Section 10 gives a strengthened version: the analytic part covers $`N\ge6\times10^5`$, so the computational part is only needed for $`N\le6\times10^5`$.

---

## 1. Notation and basic facts

$`A`$ is called **admissible** if it satisfies the hypothesis of the theorem. For $`a\in A`$, taking $`b=a`$ shows that $`a^2+1`$ is not squarefree. If $`p^2\mid a^2+1`$, then $`p\ne 2`$ (because $`a^2+1\not\equiv0\pmod 4`$) and $`-1`$ is a quadratic residue mod $`p`$, so $`p\equiv1\pmod4`$.

- $`A_7=A\cap(7+25\mathbb Z)`$, $`A_{18}=A\cap(18+25\mathbb Z)`$, $`A^*=A\setminus(A_7\cup A_{18})`$
- **U1 primes**: primes with $`p\equiv1\ (4)`$ and $`p\ge13`$. Write $`\pm r_p`$ for the two solutions of $`x^2\equiv-1\pmod{p^2}`$, and $`R_p=\{x: x\equiv\pm r_p\ (p^2)\}`$.
- For an integer $`b`$, we say $`a`$ is **compatible** with $`b`$ if $`\mu(ab+1)=0`$.

**(F1)** If $`x\in A^*`$, then $`p^2\mid x^2+1`$ for some U1 prime $`p`$. This is because $`25\mid x^2+1\iff x\equiv\pm7\pmod{25}`$.

**(F2)** If $`a\in A_7\cup A_{18}`$ and $`b\in A^*`$, then $`25\nmid ab+1`$. Indeed, for $`a\equiv7`$ we have $`25\mid 7b+1\iff b\equiv7`$, and for $`a\equiv18`$ we have $`25\mid18b+1\iff b\equiv18`$.

**(F3)** If $`a\in A_7`$ and $`b\in A_{18}`$, then $`25\nmid ab+1`$, because $`7\cdot18+1=127`$.

**(F4)** If $`a,b`$ are both odd, then $`4\mid ab+1\iff a\not\equiv b\pmod 4`$. If $`a`$ or $`b`$ is even, then $`ab+1`$ is odd.

**(F5)** If $`p\nmid b`$, then $`p^2\mid ab+1\iff a\equiv c_p(b):=-b^{-1}\pmod{p^2}`$. If $`p`$ is a U1 prime, then $`c_p(b)\equiv\pm r_p\iff b\equiv\pm r_p`$ (because $`r_p^{-1}\equiv-r_p`$).

**(F6)** $`\rho^*(b):=\max_{(c,b)=1}\#\{s\bmod b: s^2\equiv c\}\le 2^{\omega_{\rm odd}(b)}\cdot\{1,2,4\}`$, where the last factor is $`1,2,4`$ according as $`v_2(b)\le1,\ =2,\ \ge3`$. Write $`\rho_{\max}(N)=\max_{b\le N}\rho^*(b)`$; it can be computed from products of the smallest odd primes.

---

## 2. Lemma A′ (sieving by a single witness, with shared sets)

Fix a **witness** $`1\le b\le N`$ and parameters $`5\le z\le p_c\lt Y`$. Define two sets of integers:

```math
\mathrm{Mid}(b)=\{a\le N:\ \exists p\in(p_c,Y],\ p\nmid b,\ p^2\mid ab+1\},\qquad \mathrm{Ex}(b)=\{a\le N:\ \exists p>Y,\ p^2\mid ab+1\}.
```

**Lemma A′.**
(i) $`|\mathrm{Mid}(b)|\le\sum_{p_c\lt p\le Y}\big(N/p^2+1\big)`$
(ii) $`|\mathrm{Ex}(b)|\le\rho^*(b)\big(2(N+1)/Y+(Nb+1)/Y^2\big)`$
(iii) Suppose every prime factor $`p`$ of $`q`$ satisfies $`p^2\mid q`$, let $`T`$ be a set of residue classes mod $`q`$, and suppose $`p^2\nmid tb+1`$ for every $`t\in T`$ and every $`p\mid q`$. Let $`\mathcal P=\{p\nmid qb\}`$ and $`k=\#\{p\in\mathcal P:p\le z\}`$. Then

```math
\#\{a\le N:\ a\bmod q\in T,\ a\text{ compatible with }b\}\le |T|\Big[\frac Nq\Big(1-\prod_{\substack{p\in\mathcal P\\p\le z}}\Big(1-\frac1{p^2}\Big)\Big)+2^k-1\Big]+\sum_{\substack{z\lt p\le p_c\\ p\in\mathcal P}}|T|\Big(\frac N{qp^2}+1\Big)+\big|\mathrm{Mid}(b)\cap S\big|+\big|\mathrm{Ex}(b)\cap S\big|,
```

where $`S=\{a\le N: a\bmod q\in T\}`$.

**Key point:** when the same $`b`$ is used to sieve several pairwise disjoint parts of $`A`$, the contributions of $`\mathrm{Mid}(b)`$ and $`\mathrm{Ex}(b)`$ over all parts add up to at most $`|\mathrm{Mid}(b)|+|\mathrm{Ex}(b)|`$. So **each witness pays the large-prime error only once**.

**Proof.** If $`a`$ is compatible with $`b`$, take a prime $`p`$ with $`p^2\mid ab+1`$. Then $`p\nmid b`$; and if $`p\mid q`$, then $`ab+1\equiv tb+1\not\equiv0\ (p^2)`$, a contradiction. So $`p\in\mathcal P`$.
- $`p\le z`$: inclusion–exclusion for each $`t`$, with error $`\le 2^k-1`$ (as in the original Lemma A).
- $`z\lt p\le p_c`$: each $`t`$ lies in one class mod $`qp^2`$, which contains $`\le N/(qp^2)+1`$ elements.
- $`p_c\lt p\le Y`$: $`a\in\mathrm{Mid}(b)`$. By (F5) each $`p`$ accounts for at most $`N/p^2+1`$ values of $`a`$, which gives (i).
- $`p>Y`$: $`a\in \mathrm{Ex}(b)`$. Write $`ab+1=p^2m`$. Then $`m\le M=\lfloor (Nb+1)/Y^2\rfloor`$ and $`a`$ is determined by $`(p,m)`$. The congruence $`p^2m\equiv1\ (b)`$ requires $`\gcd(m,b)=1`$ (otherwise it has no solution; such $`m`$ are merely over-counted in the sum below, so the bound still holds), and it puts $`p\bmod b`$ in at most $`\rho^*(b)`$ classes, and $`p\le\sqrt{(Nb+1)/m}`$. So the total is $`\le\rho^*(b)\sum_{m\le M}\big(\sqrt{(Nb+1)/m}/b+1\big)\le\rho^*(b)\big(2(N+1)/Y+(Nb+1)/Y^2\big)`$, which gives (ii). $`\square`$

## 3. Lemma B (counting sets of type $`A^*`$)

(Lemma B involves only U1 primes $`p\ge13`$, which are coprime to every $`q\in\{25,50,100\}`$; so the condition "$`p\mid q\Rightarrow p^2\mid q`$" of Lemma A′ is **not** needed here, and for example $`q=50`$ is allowed.)

For $`q\in\{25,50,100\}`$, a set $`T`$ of residue classes mod $`q`$ ($`\tau=|T|`$), and $`13\le z_B\le p_B\le Y'`$, put $`k=\#\{\text{U1 primes}\le z_B\}`$. Then

```math
\#\{n\le N: n\bmod q\in T,\ \exists\text{ U1 prime }p,\ p^2\mid n^2+1\}\le \tau\Big[\frac Nq\Big(1-\prod_{\text{U1},\,p\le z_B}\Big(1-\frac2{p^2}\Big)\Big)+3^k-1\Big]+\sum_{\text{U1},\,z_B\lt p\le p_B}2\tau\Big(\frac N{qp^2}+1\Big)+\sum_{\text{U1},\,p_B\lt p\le Y'}2\Big(\frac N{p^2}+1\Big)+\Big\lfloor\frac{N^2+1}{Y'^2}\Big\rfloor\Big(\frac{\ln(2N+1)}{2\ln(1+\sqrt2)}+\frac12\Big).
```

**Proof.** Small primes: inclusion–exclusion. For each prime the two classes $`\pm r_p`$ are disjoint, so there are $`3^k-1`$ nonzero terms. Medium primes are counted directly. For $`p>Y'`$, write $`n^2+1=p^2m`$; then $`(n,p)`$ is a positive solution of $`x^2-my^2=-1`$, and there is no solution when $`m`$ is a perfect square. Otherwise every positive solution has the form $`\varepsilon^{2j+1}`$, where $`\varepsilon\ge1+\sqrt2`$ is the fundamental unit of $`\mathbb Z[\sqrt m]`$, and $`\varepsilon^{2j+1}\lt 2N+1`$. $`\square`$

## 4. Lemma C (sieving $`A^*`$ by an even witness)

Let $`b\in A^*`$ be even, and let $`T_{25}`$ be the 23 classes mod 25 other than 7 and 18. For $`x\in A^*`$: either $`x=b`$, or there is an **odd** prime $`p_2\nmid b`$ with $`p_2^2\mid xb+1`$; and by (F1) there is a U1 prime $`p_1`$ with $`x\in R_{p_1}`$. Hence

```math
|A^*|\le |T_{25}\cap U_1^{>z_1}|+\sum_{p_2\le z_2\ \text{odd}}\big|T_{25}\cap U_1^{\le z_1}\cap C_{p_2}\big|+\sum_{z_2\lt p_2\le p_c}\Big(\frac N{p_2^2}+1\Big)+|\mathrm{Mid}(b)\cap A^*|+|\mathrm{Ex}(b)\cap A^*|,
```

where $`C_{p}=\{x\equiv c_p(b)\ (p^2)\}`$, $`U_1^{\le z_1}=\bigcup_{\text{U1},\,p\le z_1}R_p`$, and $`U_1^{>z_1}`$ is defined in the same way. ($`x=b`$ itself lies in some $`C_{p_1}\cap R_{p_1}`$, so it is already counted.)

**Convention.** In the table of Section 5, "Lemma C" denotes the bound above **without** its last two terms $`|\mathrm{Mid}(b)\cap A^*|+|\mathrm{Ex}(b)\cap A^*|`$. Together with the shared-set part of $`A_7\cup A_{18}`$ for the same witness $`b`$, these terms add up to at most $`\Sigma(b)=|\mathrm{Mid}(b)|+|\mathrm{Ex}(b)|`$ (the key point of Lemma A′), which is why the table reads "$`\Sigma(b)+`$ Lemma C" and each witness is charged only once. The code does the same: `lemC` in `n0_exact.py` contains no shared set, and `shared` is called once outside it.

**Explicit bounds for each term.** Write $`\mathcal U=\{\text{U1 primes}\le z_1\}`$, $`k_1=|\mathcal U|`$, $`P=\prod_{q\in\mathcal U}(1-2/q^2)`$ (as in §4.1).

- **First term (large U1 primes):** $`x\in R_{p_1}`$ for some U1 prime $`p_1>z_1`$. For $`p_1\le p_B`$ we count inside each of the 23 classes, for $`p_B\lt p_1\le Y'`$ without restricting the residue class, and for $`p_1>Y'`$ we use the Pell argument of Lemma B:

```math
|T_{25}\cap U_1^{>z_1}|\le\sum_{\text{U1},\,z_1\lt p\le p_B}2\cdot23\Big(\frac N{25p^2}+1\Big)+\sum_{\text{U1},\,p_B\lt p\le Y'}2\Big(\frac N{p^2}+1\Big)+\Big\lfloor\frac{N^2+1}{Y'^2}\Big\rfloor\Big(\frac{\ln(2N+1)}{2\ln(1+\sqrt2)}+\frac12\Big).
```

  This is Lemma B with $`q=25`$, $`\tau=23`$, without the small-prime part and with the lower limit $`z_B`$ replaced by $`z_1`$.
- **$`p_2=5`$:** $`C_5`$ is **one whole class** mod 25, and by (F5) and $`b\not\equiv\pm7`$ it belongs to $`T_{25}`$, so this term must **not** be multiplied by $`23/25`$. Since 5 is not a U1 prime, $`x`$ can enter $`U_1^{\le z_1}`$ only through primes of $`\mathcal U`$. Inclusion–exclusion gives $`\le\frac N{25}(1-P)+3^{k_1}`$.
- **$`p_2`$ an odd prime that is neither 5 nor a U1 prime:** $`\le\frac{23}{25}\frac N{p_2^2}(1-P)+3\cdot3^{k_1}`$, by three inclusion–exclusions ("all classes minus the classes $`\equiv7`$ and $`\equiv18`$"), each with error $`\le3^{k_1}`$.
- **$`p_2`$ a U1 prime with $`b\in R_{p_2}`$:** by (F5), $`C_{p_2}`$ is exactly one class of $`R_{p_2}`$. Counting the whole class (three single-class counts) gives $`\le\frac{23}{25}\frac N{p_2^2}+3`$.
- **$`p_2`$ a U1 prime with $`b\notin R_{p_2}`$:** $`C_{p_2}\cap R_{p_2}=\emptyset`$, so $`x`$ can enter $`U_1^{\le z_1}`$ only through $`\mathcal U\setminus\{p_2\}`$, giving $`\le\frac{23}{25}\frac N{p_2^2}(1-\mathrm{pr}_{p_2})+3\cdot3^{k'_{p_2}}`$ (notation of §4.1).
- **$`z_2\lt p_2\le p_c`$:** we only use $`x\in C_{p_2}`$, giving $`\le N/p_2^2+1`$. The part $`p_2>p_c`$ is already contained in the shared sets $`\mathrm{Mid}(b)\cup\mathrm{Ex}(b)`$.

In the worst case $`\mathcal P`$ consists of all odd primes (prime factors of $`b`$ only make the bound smaller).

### 4.1 The worst case for $`S_b`$

**Notation.** Let $`S_b=\{\text{U1 primes }p:\ b\in R_p\}`$. List all U1 primes in increasing order, $`q_1=13\lt q_2=17\lt q_3=29\lt \cdots`$. Put
- $`\mathcal U=\{q\text{ U1 prime}: q\le z_1\}`$, $`k_1=|\mathcal U|`$, $`P=\prod_{q\in\mathcal U}(1-2/q^2)`$;
- for a U1 prime $`p\le z_2`$, $`\mathrm{pr}_p=\prod_{q\in\mathcal U,\,q\ne p}(1-2/q^2)`$ and $`k'_p=|\mathcal U\setminus\{p\}|`$;
- by the analysis above, the bound for the term of $`p`$ is $`\mathrm{whole}(p)=\tfrac{23}{25}\tfrac N{p^2}+3`$ if $`p\in S_b`$, and $`\mathrm{non}(p)=\tfrac{23}{25}\tfrac N{p^2}(1-\mathrm{pr}_p)+3\cdot3^{k'_p}`$ if $`p\notin S_b`$. Put $`g(p)=\mathrm{whole}(p)-\mathrm{non}(p)`$.

So the middle sum equals $`\sum_{p}\mathrm{non}(p)+\sum_{p\in S_b,\,p\le z_2}g(p)`$.

**Lemma C1 ($`g`$ is strictly decreasing).** For U1 primes $`p\lt p'`$ we have $`g(p)>g(p')`$.

*Proof.* Directly,

```math
g(p)=\begin{cases}\dfrac{23}{25}\cdot\dfrac{N P}{p^2-2}-3^{k_1}+3, & p\le z_1\quad(\text{then }\mathrm{pr}_p=P/(1-2/p^2),\ k'_p=k_1-1),\\[2mm]
\dfrac{23}{25}\cdot\dfrac{N P}{p^2}-3^{k_1+1}+3, & p>z_1\quad(\text{then }\mathrm{pr}_p=P,\ k'_p=k_1).\end{cases}
```

- If $`p\lt p'\le z_1`$: $`p^2-2\lt p'^2-2`$ and the constant terms agree, so $`g(p)>g(p')`$.
- If $`z_1\lt p\lt p'`$: the same argument.
- If $`p\le z_1\lt p'`$ (crossing $`z_1`$): $`p^2-2\lt p^2\lt p'^2`$, so the first term is strictly larger; and $`-3^{k_1}+3>-3^{k_1+1}+3`$. Hence $`g(p)>g(p')`$. $`\square`$

**Lemma C2 (prefix domination).** Let $`L=\max\{\ell:\ q_1q_2\cdots q_\ell\le\sqrt{N^2+1}\}`$. Then for every even $`b\le N`$,

```math
\sum_{p\in S_b,\ p\le z_2}g(p)\ \le\ \sum_{j\le L,\ q_j\le z_2}\max\big(g(q_j),0\big).
```

*Proof.* Write $`S_b=\{s_1\lt \dots\lt s_m\}`$. For $`p\in S_b`$ we have $`p^2\mid b^2+1`$, and these primes are distinct, so $`\prod_j s_j^2\mid b^2+1\le N^2+1`$, i.e. $`\prod_j s_j\le\sqrt{N^2+1}`$. Since $`s_j`$ is the $`j`$-th smallest of $`m`$ distinct U1 primes, $`s_j\ge q_j`$; therefore $`\prod_{j\le m}q_j\le\prod_j s_j\le\sqrt{N^2+1}`$, i.e. $`m\le L`$. By Lemma C1, $`g(s_j)\le g(q_j)`$; and $`s_j\le z_2`$ implies $`q_j\le s_j\le z_2`$. Hence

```math
\sum_{s_j\le z_2}g(s_j)\le\sum_{j\le m,\ q_j\le z_2}g(q_j)\le\sum_{j\le L,\ q_j\le z_2}\max(g(q_j),0).\qquad\square
```

**Use on an interval.** For $`N\in[N_{lo},N_{hi}]`$:
- $`L`$ is computed at $`N_{hi}`$; $`L`$ is nondecreasing in $`N`$, so this is a valid upper bound.
- Each $`g(q)`$ has the form $`\Delta C\cdot N+\Delta E`$ with $`\Delta C=\tfrac{23}{25}\mathrm{pr}_q/q^2>0`$ and $`\Delta E=3-3\cdot3^{k'_q}\le0`$.
  - If $`g(q)`$ is positive at $`N_{lo}`$, it is positive for all $`N\ge N_{lo}`$, and $`\max(g,0)=\Delta C N+\Delta E`$.
  - Otherwise we use $`\max(g,0)\le\Delta C\cdot N`$ (since $`\Delta E\le0`$).
- For $`N\ge10^{60}`$ we take $`L`$ to consist of all U1 primes $`\le z_2`$ (the bound of Lemma C2 remains valid for a larger $`L`$); then every $`g>0`$.

See `lemC` in `n0_exact.py` (exact version) and `n0_v2.py` (floating-point version).

## 5. Case analysis

Write $`\Sigma(b)=|\mathrm{Mid}(b)|+|\mathrm{Ex}(b)|`$. Let $`R(T,q;\text{excl})`$ denote the terms of Lemma A′(iii) other than $`\mathrm{Mid}`$ and $`\mathrm{Ex}`$ (with the worst case for $`\mathcal P`$: all primes except those in excl), and $`B(\tau,q)`$ the bound of Lemma B. In the table, excl is always $`\{2,5\}`$ for $`R(\cdot,100)`$.

| Case | Condition | Upper bound | Main coefficient ×25 |
|---|---|---|---|
| **I.a** | $`A^*=\emptyset`$, $`A_7`$ or $`A_{18}`$ empty | $`\max(c_7,c_{18})=c_7`$ | — |
| **I.b** | $`A^*=\emptyset`$, $`b\in A_7`$, $`b'\in A_{18}`$ | $`R(\{18\},25;\{5\})+\Sigma(b)+R(\{7\},25;\{5\})+\Sigma(b')`$ | 0.741 |
| **II** | $`A^*`$ contains an even $`b`$ | $`R(\{7,18\},25;\{2,5\})+\Sigma(b)+`$ Lemma C | 0.784 ($`\le 0.826`$ as $`N\to\infty`$) |
| **III.1** | $`A^*`$ all odd, containing both $`b_1\equiv1`$ and $`b_3\equiv3\ (4)`$ | $`R(6\text{ classes},100)+\Sigma(b_1)+R(2\text{ classes},100)+\Sigma(b_3)+B(23,50)`$ | 0.632 |
| **III.2.a** | $`A^*\subseteq`$ one class mod 4, $`A_7\cup A_{18}`$ all odd | $`2(N/100+1)+R(2\text{ classes},100)+\Sigma(b)+B(23,100)`$ | 0.739 |
| **III.2.b** | as above, but $`A_7\cup A_{18}`$ contains an even $`b'`$ | $`(N/100+1)+R(3\text{ classes},100)+\Sigma(b)+R(4\text{ classes},100)+\Sigma(b')+B(23,100)`$ | 0.686 |

**Justification of the cases:**
- **III.1**: $`b_1`$ sieves the classes of $`A_7\cup A_{18}`$ that are $`\equiv1\ (4)`$ or even, namely 57, 93, 32, 82, 18, 68 mod 100; $`b_3`$ sieves the classes $`\equiv3`$, namely 7 and 43. By (F4) every one of these classes has $`4\nmid tb+1`$, and by (F2) $`25\nmid tb+1`$, so $`\{2,5\}`$ can be excluded.
- **III.2.a** (say $`A^*\subseteq1\ (4)`$ and $`b\in A^*`$): for the classes 7 and 43 ($`\equiv3`$) the product with $`b`$ plus 1 is divisible by 4, so they cannot be sieved and are counted as whole classes; the classes 57 and 93 are sieved by $`b`$. $`A^*\subseteq\{n\equiv1\ (4)\}`$ is counted with 23 classes mod 100. The case $`A^*\subseteq3\ (4)`$ is symmetric, with the same numbers. This case also covers $`A_7\cup A_{18}=\emptyset`$: the corresponding counts are then 0 and the bound still holds.
- **III.2.b**: say the even $`b'\in A_7`$. In $`A_7`$ the class 7 is counted whole and 32, 57, 82 are sieved by $`b`$; the 4 classes of $`A_{18}`$ are sieved by $`b'`$ ($`tb'+1`$ is odd, and (F3) applies). The case $`b'\in A_{18}`$ is symmetric.
- **II**: $`A_7\cup A_{18}`$ is sieved by the even $`b`$, so $`p=2`$ cannot occur.

These cases exhaust all possibilities: $`A^*=\emptyset`$ (case I); $`A^*`$ contains an even element (II); $`A^*`$ nonempty and all odd (III, subdivided by residues mod 4 and the parity of $`A_7\cup A_{18}`$).

## 6. Explicit verification: all $`N\ge1.6\times10^8`$

### 6.1 How the interval checks cover every integer $`N`$

**Lemma D.** Let a set of parameters $`\theta=(z,p_c,Y,Y'_q,p_{B,q},z_B,z_1,z_2,L)`$, depending only on the interval, be fixed on an interval $`[N_{lo},N_{hi}]`$ (real endpoints). For each case, the lemmas of Sections 2–5 give, for every **integer** $`N\in[N_{lo},N_{hi}]`$ and every admissible $`A\subseteq[1,N]`$ belonging to that case,

```math
|A|\le C_\theta\cdot N+E_\theta(N),
```

where $`C_\theta`$ is a constant and $`E_\theta`$ is an explicit function, nondecreasing in real $`N`$ (its terms are $`\rho_{\max}(N)`$, $`(N+1)/Y`$, $`(N^2+1)/Y^2`$, $`\lfloor(N^2+1)/Y'^2\rfloor\cdot(0.5673\ln(2N+1)+0.5)`$, constants, and the treatment of $`g(q)`$). If

```math
C_\theta\lt \tfrac1{25}\quad\text{and}\quad C_\theta N_{lo}+E_\theta(N_{hi})\lt \frac{N_{lo}-6}{25},
```

then $`|A|\lt \frac{N-6}{25}\le c_7(N)`$ for every integer $`N\in[N_{lo},N_{hi}]`$.

*Proof.* $`|A|\le C_\theta N+E_\theta(N)\le C_\theta N+E_\theta(N_{hi})`$. The function $`N\mapsto\frac{N-6}{25}-C_\theta N`$ has slope $`\frac1{25}-C_\theta>0`$, so its minimum on the interval is at $`N_{lo}`$. Hence $`C_\theta N+E_\theta(N_{hi})\lt \frac{N-6}{25}`$. Finally, $`c_7(N)=\lfloor(N+18)/25\rfloor\ge(N+18-24)/25=(N-6)/25`$. $`\square`$

**Coverage.**
- The intervals of the exact certificates (§6.2) have integer endpoints and are contiguous: the $`N_{lo}`$ of interval $`i+1`$ equals the $`N_{hi}`$ of interval $`i`$.
- `exact_1.csv` starts at $`1.6\times10^8`$ and ends at $`10^{12}`$; `exact_2.csv` starts at $`10^{12}`$ and ends **exactly** at $`10^{60}`$.
- The tail (§6.4) covers every $`N\ge10^{60}`$.
- Hence every integer $`N\ge1.6\times10^8`$ lies in one of the closed intervals or in the tail.

### 6.2 Exact verification (primary certificate)

`code/n0_exact.py` recomputes every bound of Sections 2–5 in **exact rational arithmetic**, so the conclusion does not depend on floating-point rounding:
- Sums of reciprocal squares of primes $`\sum1/p^2`$ are bounded above by integer sums of $`\lceil10^{40}/p^2\rceil/10^{40}`$; beyond the prime table ($`2\times10^7`$) we use $`\sum_{n>P}1/n^2\lt 1/(P-1)`$.
- $`\pi(x)`$ is an exact integer for $`x\le2\times10^7`$; above that we use the Rosser–Schoenfeld bound $`\pi(x)\lt 1.25506\,x/\ln x`$ with a rational **lower** bound for $`\ln x`$.
- $`\ln(2N+1)`$ in the Pell term is replaced by a rational **upper** bound; the coefficient $`0.5673\ge1/(2\ln(1+\sqrt2))`$ is used and $`\lfloor(N^2+1)/Y'^2\rfloor`$ is replaced by $`\lfloor(N^2+1)/Y'^2\rfloor+1`$, both of which only enlarge the bound.
- For $`x>2\times10^7`$, $`\pi_1(x):=\#\{p\le x: p\equiv1\ (4)\}`$ is bounded by $`\pi_1(x)\le\pi(x)`$, and the tail of the reciprocal squares of U1 primes again by $`\sum_{n>P}1/n^2\lt1/(P-1)`$.
- Logarithms are computed with mpmath at 60 digits, with a margin of $`10^{-50}`$ in the safe direction.
- $`\prod(1-c/p^2)`$, floors, $`\rho_{\max}`$, and the prefix condition $`(\prod p)^2\le N^2+1`$ of Lemma C2 are computed exactly.

The parameters $`Y`$, $`p_c`$, and for each $`q\in\{25,50,100\}`$ the values $`Y'_q`$ and $`p_{B,q}=\lfloor\sqrt{N_{hi}(1-\tau/q)/(\tau-1)}\rfloor`$ ($`\tau=23`$), are integers chosen by the floating-point optimiser and are all recorded in the certificate (columns `Y`, `pc`, `YB25/50/100`, `pB25/50/100`). Lemma C uses the values for $`q=25`$. Since every choice of parameters yields a valid upper bound, the parameters themselves need no verification. Every interval must satisfy, for every case, $`C\lt 1/25`$ and $`CN_{lo}+E(N_{hi})\lt (N_{lo}-6)/25`$ (Lemma D).

**Certificates** (`certificates/`):
- `exact_1.csv`: 1753 intervals covering $`[1.6\times10^8,10^{12}]`$, worst ratio 0.978904
- `exact_2.csv`: 1160 intervals covering $`[10^{12},10^{60}]`$, worst ratio 0.821456

Each row records the exact endpoints (numerator and denominator), all parameters, $`\rho_{\max}`$, and the values $`C`$, $`E`$ and an upper bound for the ratio for each of the five cases. `python3 check_cert.py --exact exact_1.csv exact_2.csv` checks that the endpoints are integers, that the intervals are contiguous and run from $`1.6\times10^8`$ exactly to $`10^{60}`$, and that every ratio bound is $`\lt 1`$.

**A version matching the Lean formalisation exactly.** The flag `--lean` additionally replaces the Pell tail of Lemma B by the elementary bound proved in `Erdos848/PellTail.lean`: two solutions satisfy $`x_2\ge3x_1`$ (proved from the integer identities $`a^2-mc^2=1`$ and $`x_2=ax_1+mcy_1`$, without unit groups), so each $`m`$ has at most $`\log_3N+1`$ solutions and the coefficient becomes $`1/\ln3\lt 0.9103`$ instead of $`0.5673`$. The certificates `exact_lean_1.csv` and `exact_lean_2.csv` recomputed with it also pass (worst ratios 0.989149 and 0.824178, tail 0.825181).

**A version using only results available in Mathlib.** With the flag `--cheb`, the Rosser–Schoenfeld bound is replaced by $`\pi(x)\le\sqrt x+2\log4\cdot x/\ln x`$. This follows from Chebyshev's bound $`\theta(x)\le x\log4`$ (`Chebyshev.theta_le_log4_mul_x` in Mathlib), since $`\pi(x)-\pi(\sqrt x)\le\theta(x)/\ln\sqrt x`$. The certificates `exact_cheb_1.csv` and `exact_cheb_2.csv` recomputed with it also cover $`[1.6\times10^8,10^{60}]`$, with worst ratios 0.989149 and 0.823131 and 0.825181 for the tail. The Lean formalisation will use this version.

To reproduce:
- `python3 n0_exact.py scan 1.6e8 1e12 1.005 ../certificates/exact_1.csv`
- `python3 n0_exact.py scan 1e12 1e60 1.1 ../certificates/exact_2.csv`
- `python3 n0_exact.py tail`

### 6.3 Floating-point version (auxiliary)

`code/n0_v2.py` implements the same formulas in floating point; it is used to optimise the parameters and produces `cert_1.csv` and `cert_2.csv`. To absorb rounding errors it adds 1 to every error term and counts the tail beyond $`2\times10^7`$ twice, so its $`E`$ is slightly larger than in the exact version (for example about 5 more per witness); this only makes it more conservative. Its results (worst ratios 0.97891 and 0.82146) agree with the exact version to $`10^{-5}`$. `check_cert.py` re-checks the inequalities recorded in these two files in exact rational arithmetic.

### 6.4 The tail $`N\ge10^{60}`$

- The parameters are fixed: $`p_c=p_B=2000`$, $`Y=Y'=N^{0.7}`$, and $`L`$ is taken maximal (all U1 primes $`\le z_2`$).
- For $`b\le N`$: $`\rho^*(b)\le2^{\omega(b)+1}`$. By Robin's inequality $`\omega(n)\le1.3841\ln n/\ln\ln n`$ ($`n\ge3`$), with $`\ln x/\ln\ln x`$ increasing for $`x\ge e^e`$ and $`\omega(b)\le2`$ directly for $`b\lt 16`$, we get $`\rho^*(b)\le2N^{0.195}`$ for $`N\ge10^{60}`$ (where $`\ln\ln N\ge4.927`$).
- Using $`\lfloor x\rfloor\le x`$, $`\ln(2N+1)\le\ln N+1`$, $`N+1\le2N`$ and $`N^2+1\le2N^2`$, $`E(N)`$ is bounded by a constant plus finitely many terms of the form $`aN^\alpha(\ln N)^\gamma`$ with $`\alpha\le0.8`$. Each term divided by $`N`$ is decreasing once $`\ln N>\gamma/(1-\alpha)`$, so $`E(N)/N`$ is decreasing on $`N\ge10^{60}`$.
- $`C`$ does not depend on $`N`$, because the upper bound for $`\sum1/p^2`$ is constant once $`Y>2\times10^7`$.
- At $`N=10^{60}`$, exact arithmetic (`n0_exact.py tail`, $`Y=\lfloor N^{0.7}\rfloor`$) gives the ratios 0.740806, 0.825181, 0.632401, 0.738655, 0.685796 for the five cases, all $`\lt 1`$. (The floating-point `tail.py` gives the same values.)

**Empirical check of the main terms** (`sanity.cpp`, $`N=2\times10^6`$, 30 random witnesses per type): the ratio of the actual count to the Sawhney-type main term lies between 0.999 and 1.005 in every case; the "whole class is compatible" claims were each verified; the measured density of the Lemma C set is at most 0.0091, against an upper bound of 0.0184.

## 7. Computer verification: all $`N\le 4\times10^8`$

Let $`V=\{n: \mu(n^2+1)=0\}`$ and let $`G`$ be the graph with edges $`\mu(uv+1)=0`$. Admissible sets are exactly the cliques of $`G[V\cap[1,N]]`$.

`incr.cpp` maintains, for increasing $`n`$, a partition of $`V\cap[1,N]`$ into **exactly** $`c_7(N)`$ classes, each of which is an independent set ($`uv+1`$ squarefree for all pairs in the class). A new class is opened only when $`n\equiv7\pmod{25}`$, with $`n`$ as its anchor; every other vertex is placed into an existing class, if necessary after moving the unique conflicting member of a class to another class (one- or two-step chains). Hence for every $`N`$, clique number $`\le`$ chromatic number $`\le c_7(N)`$.

Every operation is written to a log. `replay.cpp` replays the log independently. It:
- recomputes $`V`$ with a different sieve (Tonelli–Shanks plus lifting), cross-checked against complete factorisation on a small range;
- decides squarefreeness by complete factorisation (Miller–Rabin plus Pollard–Brent), a method entirely different from the trial division in `incr.cpp`;
- checks that the vertices traverse exactly $`V`$ in order, that the number of classes equals $`c_7(N)`$, and that no placement or move ever breaks independence.

Tests with deliberately corrupted logs are detected.

| Range | Colouring time | Replay |
|---|---|---|
| $`N\le10^6`$ | 0.4 s | passed |
| $`N\le10^7`$ | 11 s | passed |
| $`N\le10^8`$ | 407 s | passed (231 s) |
| $`N\le4\times10^8`$ | 3761 s | passed (`replay` 1310 s; revised `replay2` 1312 s) |

**Run record for $`N\le4\times10^8`$:**
- `incr`: $`|V\cap[1,4\times10^8]|=42\,063\,559`$, number of classes $`16\,000\,000=c_7(4\times10^8)`$; 5,522,714 one-step repairs, 0 two-step repairs, 0 full scans
- Both replay versions print `REPLAY OK: X=400000000 ops=47586273 classes=16000000 (c7=16000000) tests=48445645`
- Log `log_4e8.bin`: 1,142,070,552 bytes, SHA-256 `6b5d45b4dac3a81092f8c9620563fc8108ac8c0d992191b07596463b165a8c5f`
- zstd-compressed `log_4e8.bin.zst`: 232,593,555 bytes, SHA-256 `d6e5d3c9d6bb02884f577865d8f36bd6fce2db91393b1a85ea3cb9b956fa3603`
- The compressed log is published as an asset of the repository release `logs-4e8`; decompressing it gives `log_4e8.bin`
- The `incr.cpp` and `replay.cpp` used to generate and replay the log are the versions in `code/` (SHA-256 `518201815c22…` and `0a32d5f3a0e7…`)

Two earlier independent verifications also exist: `verify.cpp` (maximum-clique branch and bound, $`N\le10^5`$) and `xcheck.py` (brute-force maximum clique with networkx, $`N\le1500`$).

## 8. Lean formalisation (directory `Erdos848/`)

The whole theorem is formalised in Lean 4 + Mathlib, without `sorry`:

```lean
theorem Erdos848.erdos848 : ∀ N, Statement N
-- Statement N := ∀ A ⊆ Finset.Icc 1 N, Admissible A → A.card ≤ c7 N
```

together with `erdos848_max'` (the maximum is exactly $`c_7(N)`$) and `erdos848_formalConjectures`. `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. Every computation is written as `decide +kernel` and evaluated by the Lean kernel; **no `native_decide` is used**, so neither the Lean compiler nor any external program has to be trusted. The untrusted programs (parameter search, the colouring proposer, …) only produce data; the kernel checks the data, and the soundness of each checker is proved in Lean. The split used in Lean is:
- $`N\le986\,746`$: a guarded dynamic colouring (see the item "Section 7" below);
- $`986\,747\le N\le1.6\times10^8`$: the strengthened argument of Section 10 (see the item "Section 10");
- $`N\ge1.6\times10^8`$: Section 6.

How the Lean proof relates to the text:
- Sections 2–4 are formalised as explicit real bounds (`Sieve.lean`, `LemmaC.lean`, `Cases.lean`), including Lemmas C1 and C2 (the $`j`$-th U1 prime is `Nat.nth`). The inclusion–exclusion is two-sided, which gives the slightly smaller errors $`3(3^{k}-1)`$ in Lemma C; in case III.2.b the even witness sieves one class mod 25 instead of four classes mod 100.
- Section 3 uses the elementary Pell bound (consecutive solutions grow by a factor $`\ge3`$), i.e. the constant $`1/\ln3`$ of the `--lean` certificates.
- Section 6: the Lean checker recomputes every bound itself from the parameters of `exact_lean_*.csv` (exact $`\pi`$ and $`\sum\lceil10^{30}/p^2\rceil`$ below $`2\times10^7`$ from a verified prime table, Chebyshev's bound and $`\sum_{n>P}1/n^2\le1/P`$ above). The tail $`N\ge10^{60}`$ uses $`t=\lfloor N^{1/4}\rfloor`$, $`Y=\lfloor N/t\rfloor`$, $`p_c=p_B=2000`$ and the bound $`\rho(b)^5\cdot(3\cdot5\cdots31)\le1024\cdot32^{10}b`$ valid for all $`b`$, instead of Robin's inequality. The prime table (the 10,998 points needed below $`2\times10^7`$) is verified in the kernel: for $`n\lt4473^2`$, $`n`$ is prime iff $`\gcd(n,\prod_{p\le4472}p)=1`$; the table is split into 79 pieces, each checked by a binary-split segmented sum (`KTab/`). Each of the 2913 certificate rows only looks up the dozen table entries it needs, in a search tree (`KRows/`).
- Section 10: the checker `ErdosComp/Check2.lean` computes, for each of the 346 intervals and each of the 5 cases, an upper bound at $`N=N_{hi}`$ and compares it with $`(N_{lo}-6)/25`$ (`K2/`, one module per interval). Its soundness is proved in `Check2Alg/Comp/Core/Ex/Main.lean`, which connect every term of the checker to the real bounds of `Cases2.lean` (`Bonf.lean`, `Dom.lean`, `ExBound2.lean`, `RootLocal.lean`, `UTail.lean`, `LemmaC2.lean` and `Skeleton2.lean` formalise §10.1–10.6). Monotonicity in $`N`$ is proved from "nonnegative coefficient" conditions that the checker verifies. To make the kernel computation feasible, the certificate is tightened in a few places compared with §10.7:
  - the witness structures only distinguish odd prime factors $`\le23`$;
  - the Lemma E2 table only uses the 268 entries with period $`P\le3000`$, and the $`\beta_P`$ of each entry is verified in the kernel over one period;
  - in Lemma C, non only uses options (a) and (c); the sums over $`p\le z_2`$ are computed in fixed point with scale $`2^{40}`$, rounded in the safe direction, and the threshold $`\tau`$ is the $`n_S`$-th largest gain (Lemma C holds for every $`\tau\ge0`$);
  - the $`Y`$ of each bucket is taken from a fixed geometric grid;
  - in Lemma P the number of admissible $`m`$ is computed from a verified prefix table.

  As a result, the analytic part in Lean starts at $`N=986\,747`$, with worst ratio 0.9306 (case II, first interval).
- Section 7: in Lean the computational part only needs $`N\le986\,746`$ (`ColSound.lean`, `KColW/`).
  - The vertex set $`V`$: for each prime $`p\equiv1\pmod4`$, $`p\le986\,746`$, a root of $`x^2\equiv-1\pmod{p^2}`$ is given. The kernel verifies the roots, and that these $`p`$ are exactly all such primes (primality again via a gcd with a product of small primes).
  - Squarefreeness: for $`n\lt10007^3`$ let $`g=\gcd(n,\prod_{p\le10^4}p)`$. If $`\gcd(g,n/g)=1`$ and $`n/g`$ is not a perfect square $`\gt1`$, then $`n`$ is squarefree.
  - The colouring: an untrusted proposer (`code/kernel/colour/gen_ops.c`: first fit; on failure, an augmenting path moves one element $`\equiv18\pmod{25}`$) emits 117,389 operations (open a class, place a vertex, move a vertex), which the kernel replays one by one. The classes are stored in a binary tree of depth 16, and each step only checks the classes it changes; opening a class checks that the number of classes stays $`\le c_7`$.
  - To bound the kernel's memory, the replay is split into 40 windows. Each window starts from the previous checkpoint (a tree literal) and its final state is compared entry by entry with the next checkpoint.
  - The C++ colouring up to $`4\times10^8`$ of Section 7 is now an independent cross-check; the old `compCheck` ($`N\le1.6\times10^8`$, which needed `native_decide`) is no longer used.

## 9. Remaining work

1. Review by human experts: of the mathematics (Sections 2–6 and Section 10) and of the formal statement (`Admissible`, `c7`, `Statement` in `Erdos848/Erdos848/Basic.lean`).
2. Optional: re-check the whole environment with an independent kernel replay tool (such as `lean4checker`).

## 10. Strengthened version: the analytic part covers all $`N\ge6\times10^5`$

> Status: added 2026-10-10, **formalised in Lean** (§8, with a few tightenings for the kernel computation; in Lean the split is at $`N\ge986\,747`$). The argument of this section was proposed by an AI research sub-agent and then went through one round of review. The review found and fixed an error in Lemma C (§10.8); the corrected certificate passes. **Review by human experts is still needed.**  
> Code: `code/threshold/`; certificates: `certificates/threshold/`

Plugging the strengthened lemmas below into the framework of §2–5 gives $`|A|\lt (N-6)/25\le c_7(N)`$ for every $`6\times10^5\le N\le1.6\times10^8`$ (exact certificate, §10.7). Together with §6 ($`N\ge1.6\times10^8`$), the analytic part covers all $`N\ge6\times10^5`$, so the computational part is only needed for $`N\le6\times10^5`$. The colouring of §7 takes 0.4 s for $`N\le10^6`$.

The notation of §1–5 is kept. Every bound is used only as an upper bound, and every "worst case" choice is the same as in §2–5.

### 10.1 Stronger bounds for the shared sets (Lemmas E, M)

Fix a witness $`b`$ and $`Y\gt p_c`$. Put:
- $`M=\lfloor(Nb+1)/Y^2\rfloor`$;
- $`X_m=\sqrt{(Nb+1)/m}`$;
- $`r_b(m)=\#\{s\bmod b:\ s^2m\equiv1\ (b)\}`$, which is $`0`$ when $`\gcd(m,b)\gt1`$.

**Lemma E.**
- **(E0)** $`|\mathrm{Ex}(b)|\le\sum_{m=1}^{M}r_b(m)\big(\lfloor (X_m-Y)/b\rfloor+1\big)`$.
- **(E1)** $`\sum_{m\le M}\big((X_m-Y)/b+1\big)\le (N+1)/Y+M`$. Hence $`|\mathrm{Ex}(b)|\le\rho^*(b)\big((N+1)/Y+M\big)`$. The old bound was $`\rho^*(b)(2(N+1)/Y+(Nb+1)/Y^2)`$.
- **(E2)** Let:
  - $`e=\min(v_2(b),3)`$;
  - $`Q`$ be a set of odd primes dividing $`b`$, and $`P=2^e\prod Q`$;
  - $`g_P=r_P`$, $`\alpha_P=\varphi(P)/P`$, and $`\beta_P=\max_{0\le R\lt P}\big(\sum_{m\le R}g_P(m)-\alpha_PR\big)`$.

  Then

```math
|\mathrm{Ex}(b)|\le 2^{\omega_{\rm odd}(b)-|Q|}\Big[\alpha_P\Big(\frac{N+1}Y+M\Big)+\beta_P\Big(\frac{\sqrt{Nb+1}}b+1\Big)\Big].
```

*Proof.*
- **(E0).** If $`a\in\mathrm{Ex}(b)`$, then $`ab+1=p^2m`$ with a prime $`p\gt Y`$, so $`m\le M`$ and $`Y\lt p\le X_m`$. The congruence $`p^2m\equiv1\ (b)`$ puts $`p\bmod b`$ into $`r_b(m)`$ classes. The interval $`(Y,X_m]`$ contains at most $`\lfloor(X_m-Y)/b\rfloor+1`$ integers of each class. The map $`a\mapsto(p,m)`$ is injective.
- **(E1).** Put $`K=\sqrt{Nb+1}/Y\ge\sqrt M`$. From $`\sum_{m\le M}m^{-1/2}\le2\sqrt M-1`$,

  ```math
  \sum_{m\le M}(X_m-Y)\le Y(2K\sqrt M-K-M)\le Y(K^2-K)\le(Nb+1)/Y.
  ```

  The middle step is $`(K-\sqrt M)^2\ge0`$. Divide by $`b`$ and use $`(Nb+1)/b\le N+1`$.
- **(E2).**
  - **Factorisation.** By the Chinese remainder theorem, $`r_b=\prod_{\ell^k\Vert b}r_{\ell^k}`$.
    - For an odd prime $`\ell`$, $`r_{\ell^k}(m)\le2`$, and it is nonzero only when $`m`$ is a nonzero quadratic residue mod $`\ell`$. Hence $`r_{\ell^k}\le r_\ell`$.
    - For the prime 2, $`r_{2^k}=r_{2^{\min(k,3)}}`$.

    Therefore $`r_b\le2^{\omega_{\rm odd}(b)-|Q|}g_P`$.
  - **Partial sums.** Write $`G(R)=\sum_{m\le R}g_P(m)`$. The map $`s\mapsto s^{-2}`$ sends the units mod $`P`$ onto the classes of $`m`$, so $`\sum_{m\bmod P}g_P(m)=\varphi(P)`$. Hence $`G(R)-\alpha_PR`$ is periodic with period $`P`$, and $`G(R)\le\alpha_PR+\beta_P`$ for all $`R\ge0`$ (note $`\beta_P\ge0`$).
  - **Abel summation.** Let $`f(m)=\lfloor(X_m-Y)/b\rfloor+1`$, which is positive and nonincreasing. Abel summation gives $`\sum_{m\le M}g_P(m)f(m)\le\alpha_P\sum_{m\le M}f(m)+\beta_Pf(1)`$.
  - **Conclusion.** Finish with (E1) and $`f(1)\le\sqrt{Nb+1}/b+1`$. $`\square`$

**Uniform use over all witnesses.** The **structure** of a witness $`b`$ is the triple $`(e,S,u)`$:
- $`e=\min(v_2(b),3)`$;
- $`S`$ is the set of odd primes $`\le97`$ dividing $`b`$;
- $`u`$ is the number of odd prime factors of $`b`$ that are $`\gt97`$.

Put $`b_{\min}(e,S,u)=2^e\prod S\cdot(\text{product of the }u\text{ smallest primes }\gt97)`$. Then $`\omega_{\rm odd}(b)=|S|+u`$ and $`b\ge b_{\min}`$.

Consider all $`b\le x`$ that satisfy the constraints known in the case at hand (coprime to 5, odd, even). For all of them, $`|\mathrm{Ex}(b)|`$ is at most

```math
\max_{(e,S,u):\ b_{\min}\le x}\ 2^u\min\Big\{C_2(e)2^{|S|}\Big(\frac{N+1}Y+M_x\Big),\ \min_{Q\subseteq S}2^{|S|-|Q|}\Big[\alpha_P\Big(\frac{N+1}Y+M_x\Big)+\beta_P\Big(\frac{\sqrt{Nb_{\min}+1}}{b_{\min}}+1\Big)\Big]\Big\}.
```

Here $`M_x=\lfloor(Nx+1)/Y^2\rfloor`$ and $`C_2=(1,1,2,4)`$. The inner minimum runs only over the pairs $`(e,Q)`$ present in the table. The bound uses that $`M`$ increases with $`b`$, while $`\sqrt{Nb+1}/b`$ decreases with $`b`$.

**Table.** `certificates/threshold/disc_table_97.txt` lists $`P`$, $`\varphi(P)`$ and the integer $`P\beta_P`$ for 33230 pairs $`(e,Q)`$.
- It was generated by `disc.cpp`.
- It was checked independently by `discchk.c`, written during the review. That program recomputes every entry from $`r_P=r_{2^e}\prod_{q\in Q}(1+(\tfrac{\cdot}{q}))`$, and for the 911 entries with $`P\le3000`$ it also counts the solutions $`s`$ directly.
- All 33230 entries are correct.

**Lemma M.** If $`p\gt\sqrt N`$, a residue class mod $`p^2`$ has at most one element in $`[1,N]`$. Hence

```math
|\mathrm{Mid}(b)|\le\sum_{p_c\lt p\le\min(Y,\sqrt N)}\Big(\frac N{p^2}+1\Big)+\#\{p:\ \max(p_c,\sqrt N)\lt p\le Y\}.
```

### 10.2 The U1 tail (Lemmas H, P)

**Lemma H.** For a U1 prime $`p`$, the count $`\#\{n\le N: p^2\mid n^2+1\}`$ is:
- $`\le2(N/p^2+1)`$ in general;
- $`\le2`$ if $`p^2\gt N`$;
- $`\le1`$ if $`p^2\gt2N`$, because the two roots $`r`$ and $`p^2-r`$ add up to $`p^2\gt2N`$, so they cannot both be $`\le N`$.

**Lemma P (Pell tail, counted in a window).** Let $`Y_q\ge5`$ and $`M=\lfloor(N^2+1)/Y_q^2\rfloor`$. Call $`m`$ **admissible** if $`m\bmod 8\in\{1,2,5\}`$ and none of 3, 7, 11, 19, 23 divides $`m`$. Then

```math
\#\{n\le N:\ \exists\text{ prime }p\ge Y_q,\ p^2\mid n^2+1\}\le\sum_{m\le M\text{ admissible}}\Big(1+\Big\lfloor\frac{\ln(N/x_m)}{\ln g_m}\Big\rfloor_{+}\Big),\qquad x_m=\sqrt{mY_q^2-1},\ g_m=\max(3,2\sqrt m).
```

*Proof.* Write $`n^2+1=p^2m`$.
- **Admissibility.** Since $`p`$ is odd, $`p^2\equiv1\ (8)`$, so $`m\equiv n^2+1\in\{1,2,5\}\pmod 8`$. A prime $`\equiv3\ (4)`$ does not divide $`n^2+1`$.
- **Lower bound.** For fixed $`m`$, $`(n,p)`$ solves $`x^2-my^2=-1`$, and $`n\ge x_m`$.
- **Growth.** Let $`x_1\lt x_2`$ be two solutions. Then $`x_2+y_2\sqrt m=(x_1+y_1\sqrt m)(a+c\sqrt m)`$ with $`a^2-mc^2=1`$ and $`a,c\ge1`$; this is `pell_growth` in `PellTail.lean`. Hence:
  - $`x_2\ge ax_1\ge3x_1`$, since $`a\le2`$ forces $`m=3`$, which is not admissible;
  - $`x_2^2\ge(ax_1+my_1)^2\ge4ax_1my_1\gt4mx_1^2`$, using $`(ay_1)^2\ge(m+1)y_1^2\gt x_1^2`$ in the last step.

So the solutions in $`[x_m,N]`$ form a chain with ratio at least $`g_m`$. The number of admissible $`m\le M`$ is computed exactly from the period $`8\cdot3\cdot7\cdot11\cdot19\cdot23=807576`$. $`\square`$

The old bound counted about $`0.91\ln(2N+1)+1`$ solutions for every $`m`$. The new bound counts 0 for about 82% of all $`m`$, and mostly 1 for the rest. So $`Y'`$ can be taken much smaller.

### 10.3 Bonferroni truncation (Lemma Bf)

**Lemma Bf.** Setup:
- Let $`D`$ be a domain such that, for every odd $`Q`$ coprime to $`q`$, the number of elements of $`D`$ in one class mod $`qQ`$ lies in $`[L/(qQ)-\mu,\ L/(qQ)+\mu]`$.
- Let $`p_1,\dots,p_k`$ be distinct primes coprime to $`q`$.
- Let each event $`E_i`$ consist of $`c`$ classes mod $`p_i^2`$, and put $`v_i=c/p_i^2`$.

Then for odd $`d`$, the number of elements of $`D`$ in one class mod $`q`$ that lie in $`\bigcup E_i`$ is

```math
\le\frac Lq\sum_{j=1}^{d}(-1)^{j+1}e_j(v_1,\dots,v_k)+\mu\sum_{j=1}^{d}\binom kjc^j .
```

Moreover, the main term on the right is nondecreasing in the set of primes. So, as in §2–4, "all primes" may be used as the worst case.

*Proof.*
- **The bound.** This is the Bonferroni inequality for counting measure: truncation at an odd depth bounds the union from above. At level $`j`$, each intersection consists of $`c^j`$ classes mod $`q\prod p_i^2`$. The terms with a $`+`$ sign use the upper bound $`L/Q+\mu`$, and the terms with a $`-`$ sign use the lower bound $`L/Q-\mu`$.
- **Monotonicity.** Let $`B_d(S)`$ be the truncated main term. Then

  ```math
  B_d(S\cup\{v\})-B_d(S)=v\sum_{j=0}^{d-1}(-1)^je_j(S)\ge v\prod_{s\in S}(1-s)\ge0,
  ```

  because truncation at an even depth bounds $`\prod(1-s)`$ from above. $`\square`$

**Caution.** The truncated $`B_d`$ is only an **upper** bound. The argument "all classes minus two classes" of §4 needs a **lower** bound for the subtracted part, so it cannot be combined with truncation (see §10.8).

### 10.4 Minimal witnesses (Lemma W)

If a part of $`A`$ lies in $`[m,N]`$, it has at most $`(N-m+1)/Q+1`$ elements in each class mod $`Q`$. So the main terms of Lemmas A′(iii), B and C may use $`L=N-m+1`$ instead of $`N`$.

**Each witness is taken to be the least element of its part.**
- **Buckets.** Split $`[1,N]`$ into buckets $`[x_a,x_b]`$, where $`x_b=\max(x_a+1,\lfloor1.3x_a\rfloor)`$ and the last bucket is cut at $`N`$.
- **Bound per bucket.** For a witness in the bucket $`[x_a,x_b]`$:
  - the main terms use $`L=N-x_a+1`$;
  - $`\Sigma(b)`$ is replaced by the bound $`\mathrm{Sh}(x_b)`$, which holds uniformly for all $`b\le x_b`$ (§10.1).
- **Cut-off.** $`Y`$ may differ from bucket to bucket.

**Re-pairing.** Suppose the witness $`b=\min A_7`$ sieves $`A_{18}`$ and $`b'=\min A_{18}`$ sieves $`A_7`$. Then $`A_7\subseteq[b,N]`$ and $`A_{18}\subseteq[b',N]`$, and

```math
\big[R(N-b'+1)+\Sigma(b)\big]+\big[R(N-b+1)+\Sigma(b')\big]=\big[R(N-b+1)+\Sigma(b)\big]+\big[R(N-b'+1)+\Sigma(b')\big]\le2\max_{\rm buckets}\big[R(N-x_a+1)+\mathrm{Sh}(x_b)\big].
```

The two witnesses $`c,c'`$ in III.2 α are handled in exactly the same way.

### 10.5 Revised Lemma C

**(i) Domains.** The argument of Lemma C only uses two facts:
- $`x\in A^*`$ lies in a domain $`D`$;
- every class mod an odd $`Q`$ has a number of elements of $`D`$ in $`[L_{\rm eff}/Q-\mu,\ L_{\rm eff}/Q+\mu]`$.

The domains used are:
- **$`D=[1,N]`$:** $`L_{\rm eff}=N`$ and $`\mu=1`$.
- **Case II, with $`b`$ the least even element of $`A^*`$:** $`A^*\subseteq\{\text{odd}\le N\}\cup\{\text{even}\in[b,N]\}`$, so $`L_{\rm eff}=N-(b-1)/2`$ and $`\mu=2`$.
- **Lemma C′ (odd witness):** let $`b\in A^*`$ be odd and $`x\in A^*`$ with $`x\equiv b\ (4)`$.
  - Then $`xb+1\equiv2\ (4)`$, so some odd prime $`p_2\nmid b`$ has $`p_2^2\mid xb+1`$. This also holds for $`x=b`$.
  - Hence Lemma C holds on the domain $`(b+4\mathbb Z)\cap[b,N]`$, with $`L_{\rm eff}=(N-b+1)/4`$ and $`\mu=1`$.
  - The term $`p_2=5`$ is still counted as one whole class mod 25.

**(ii) The term of each $`p_2`$.** Notation:
- $`\mathcal U'=\mathcal U\setminus\{p_2\}`$ and $`k'=|\mathcal U'|`$;
- $`B_d`$ and $`E_d=\sum_{j\le d}\binom{k'}j2^j`$ are the truncated main term and the number of error terms at depth $`d`$ over $`\mathcal U'`$ (with $`c=2`$);
- $`1-\mathrm{pr}`$ and $`3^{k'}-1`$ are the corresponding quantities for full inclusion–exclusion.

For an odd prime $`p_2\ne5`$ with $`p_2\le z_2`$, the count $`|T_{25}\cap U_1^{\le z_1}\cap C_{p_2}\cap D|`$ is at most the smallest of the following three bounds; call it $`\mathrm{non}(p_2)`$:
- **(a)** truncated inclusion–exclusion on $`C_{p_2}`$, without the restriction mod 25: $`\frac{L_{\rm eff}}{p_2^2}B_d+\mu E_d`$;
- **(b)** full inclusion–exclusion, as "all classes minus the classes 7 and 18": $`\frac{23}{25}\frac{L_{\rm eff}}{p_2^2}(1-\mathrm{pr})+3\mu(3^{k'}-1)`$;
- **(c)** truncated inclusion–exclusion class by class inside $`T_{25}`$: $`\frac{23}{25}\frac{L_{\rm eff}}{p_2^2}B_d+23\mu E_d`$.

The remaining terms:
- **$`p_2=5`$:** $`C_5`$ is one whole class mod 25, and the bound is $`\frac{L_{\rm eff}}{25}B_d+\mu E_d`$.
- **$`p_2`$ a U1 prime with $`b\in R_{p_2}`$:** the bound is $`\mathrm{whole}(p_2)=\frac{23}{25}\frac{L_{\rm eff}}{p_2^2}+3\mu`$.
- **The first term (U1 primes $`z_1\lt p_1\le p_B`$, 23 classes each) and the terms $`z_2\lt p_2\le p_c`$:** as in §4, with $`N`$ replaced by $`L_{\rm eff}`$ and $`+1`$ by $`+\mu`$.

**(iii) Lemma C2′ (no monotonicity needed).** Let the witness satisfy $`b\le x`$. Put:
- $`n_S=\max\{\ell:\ q_1\cdots q_\ell\le\sqrt{x^2+1},\ q_\ell\le z_2\}`$;
- $`g(p)=\max(\mathrm{whole}(p)-\mathrm{non}(p),0)`$.

Then

```math
\sum_{p\in S_b,\ p\le z_2}\big(\mathrm{whole}(p)-\mathrm{non}(p)\big)\le\big(\text{sum of the }n_S\text{ largest values of }g(p)\text{ over U1 primes }p\le z_2\big).
```

This holds because $`|S_b\cap[1,z_2]|\le n_S`$, by the argument of Lemma C2. This step replaces Lemma C1, so $`g`$ need not be monotone.

### 10.6 Case analysis (new)

Notation:
- as in §5;
- $`\mathrm{Sh}(x)`$ is defined in §10.1 and §10.4;
- $`\max_{\rm buckets}`$ runs over the buckets $`[x_a,x_b]`$ of §10.4, with $`L=N-x_a+1`$;
- $`T`$ is the U1 tail from Lemmas H and P, starting at $`p_T`$ and counted once.

| Case | Witnesses | Upper bound |
|---|---|---|
| **I.b** | $`b=\min A_7`$, $`b'=\min A_{18}`$ | $`2\max_{\rm buckets}\big[R(\{\cdot\},25;\{5\};L)+\mathrm{Sh}(x_b)\big]`$ |
| **II** | $`b=`$ the least even element of $`A^*`$ | $`\max_{\rm buckets}\big[R(\{7,18\},25;\{2,5\};N)+\mathrm{Sh}(x_b)+\min(\text{Lemma C on the split domain},\ \text{Lemma C on }[1,N])\big]+T`$ |
| **III.1** | $`b_1=\min(A^*\cap(1+4\mathbb Z))`$, $`b_3=\min(A^*\cap(3+4\mathbb Z))`$ | $`R(6\text{ classes};N)+R(2\text{ classes};N)+2\max_{\rm buckets}\big[\mathcal A(L,x_b)+\mathrm{Sh}(x_b)\big]+T`$ |
| **III.2 β** | $`b=\min A^*`$; $`F_{18}=\emptyset`$ or $`F_7=\emptyset`$ | $`(N/100+1)+R(4\text{ classes};N)+\max_{\rm buckets}\big[\mathcal A+\mathrm{Sh}\big]+T`$ |
| **III.2 α** | $`b=\min A^*`$, $`c=\min F_7`$, $`c'=\min F_{18}`$ | the smaller of the two bounds below |

Here $`\mathcal A(L,x_b)=\min\big(B(23,100;L),\ \text{Lemma C′}\big)`$ bounds the part of $`A^*`$ that lies in one class mod 4 and in $`[b,N]`$, without the tail. For $`R(\cdot,100)`$, excl is always $`\{2,5\}`$.

**The split of III.2.** Say $`A^*\subseteq1+4\mathbb Z`$; the case $`A^*\subseteq3+4\mathbb Z`$ is symmetric.
- **What each witness sieves.**
  - $`b\in A^*`$ sieves the classes 57, 93, 32, 82, 18, 68 mod 100.
  - $`b`$ cannot sieve the classes 7 and 43: they are $`\equiv3\ (4)`$, so their product with $`b`$, plus 1, is divisible by 4.
  - Class 7 is sieved by any element of $`F_{18}=A_{18}\cap\{18,68,43\}`$: $`tc'+1`$ is odd or $`\equiv2\ (4)`$, and (F3) applies.
  - Class 43 is sieved by any element of $`F_7=A_7\cap\{7,32,82\}`$.
- **β ($`F_{18}=\emptyset`$).** Then the classes 18, 68 and 43 are empty. Class 7 is counted as a whole class, and 57, 32, 82, 93 are sieved by $`b`$. The case $`F_7=\emptyset`$ is symmetric.
- **α, three witnesses.** The bound is

  ```math
  R(2\text{ classes};N)+[\mathcal A+\mathrm{Sh}(b)]+2\max_{\rm buckets}[R(3\text{ classes};L)+\mathrm{Sh}(x_b)]+T .
  ```

  This holds because:
  - $`A_7\cap\{7,32,82\}\subseteq[c,N]`$: 32 and 82 are sieved by $`b`$, and 7 by $`c'`$;
  - $`A_{18}\cap\{18,68,43\}\subseteq[c',N]`$: 18 and 68 are sieved by $`b`$, and 43 by $`c`$;
  - the terms are then re-paired as in §10.4.
- **α, two witnesses.** The bound is

  ```math
  (N/100+1)+R(6\text{ classes};N)+[\mathcal A+\mathrm{Sh}(b)]+\max_{\rm buckets}[R(1\text{ class};N)+\mathrm{Sh}(x_b)]+T .
  ```

  Class 7 is counted as a whole class, and 43 is sieved by $`c`$.
- **$`A^*\subseteq3+4\mathbb Z`$.** The classes that $`b`$ cannot sieve are 57 and 93. They are sieved by elements of $`A_{18}\cap\{18,68,93\}`$ and $`A_7\cap\{32,82,57\}`$ respectively, with the same counts.

β and α together cover all of III.2, and I.a is as in §5. Every condition mod 4 and mod 25 used here follows from (F2)–(F4); `check_classes` in `bruteforce.py` checks them class by class.

### 10.7 Exact certificate

- **Parameters.**
  - The parameters of each interval ($`z,d_A,z_B,d_B,z_1,z_2,d_C,p_c,p_B`$) come from the floating-point optimiser, run at 32 geometric anchors (`anchors.json`, `scan.py anchors`).
  - The program chooses $`Y`$ for each bucket and $`Y'`$ for the tail by a floating-point search.
  - Every choice of parameters gives a valid upper bound, so these choices need no verification.
- **Monotonicity.** For fixed parameters, the bound of every case is nondecreasing in $`N`$:
  - $`L`$, $`M_x`$, $`(N+1)/Y`$ and $`\sqrt{Nb_{\min}+1}`$ all increase with $`N`$;
  - the buckets are built at $`N_{hi}`$ and cover every $`b\le N`$;
  - in Lemmas M and H, when the thresholds $`\sqrt N`$ and $`\sqrt{2N}`$ move, no prime's contribution decreases ($`1\to N/p^2+1`$, $`1\to2`$);
  - the count of Lemma P increases with $`N`$;
  - $`\mathrm{whole}-\mathrm{non}`$ increases with $`L_{\rm eff}`$ (its coefficient is positive), and so does the sum of its $`n_S`$ largest values;
  - $`\min`$ and $`\max`$ preserve monotonicity.

  So it is enough to check $`\mathrm{bound}(N_{hi})\lt(N_{lo}-6)/25`$.
- **Program.** `code/threshold/cert.c` (C + GMP + OpenMP) computes the bound for every interval and case in exact rational arithmetic and compares it with $`(N_{lo}-6)/25`$.
  - **Floating point** is used only for three things:
    - choosing $`Y`$ and $`Y'`$;
    - Pareto pruning of the table choices (dropping some valid bounds still leaves a valid upper bound);
    - a pre-selection inside the maximum over structures: structures whose float value is below $`(1-10^{-6})\cdot`$max are not evaluated exactly.
  - **Why the pre-selection is safe.** The float values come from a few operations on positive numbers, so their relative error is $`\lt10^{-12}`$. Hence a skipped structure has exact value below the exact value of the structure attaining the float maximum, and that structure is evaluated exactly.
  - **Prime data**, as in §6.2:
    - $`\sum1/p^2`$ is bounded above by integer sums of $`\lceil10^{36}/p^2\rceil`$;
    - $`\pi`$ is exact up to $`2\times10^7`$;
    - if the exact part ever goes beyond that range, the program switches to a valid crude upper bound and prints a warning. This did not happen in this run.
- **Result** (`certificates/threshold/cert_c_all.txt`).
  - 396 intervals with integer endpoints, each starting where the previous one ends, covering exactly $`[6\times10^5,1.6\times10^8]`$.
  - All pass, and there are no gaps.
  - The worst ratio is 0.959393, in case II on the interval $`[600000,606000]`$.
  - The run took 3 min 45 s with 10 threads on a Linux workstation.
- **Cross-check.** `exact.py` + `review_fix.py` implement the same formulas in Python `Fraction`s, with a different floating-point search for $`Y`$.
  - With fixed parameters, 8 sampled intervals agree with the C version digit for digit.
  - A full recomputation of all 396 intervals passes; it differs from the C version by $`\lt10^{-5}`$, with the same worst ratio (0.959393). The difference comes from the choice of $`Y`$.

To reproduce:

```
cd code/threshold
gcc -O2 -fopenmp -o cert cert.c -lgmp -lm
python3 to_intervals.py ../../certificates/threshold/cert_best_lo.csv ../../certificates/threshold/cert_best_hi.csv intervals.txt
./cert ../../certificates/threshold/disc_table_97.txt intervals.txt
```

### 10.8 Checks and review record

**Brute-force checks.** `bruteforce.py` counts directly for small $`N`$ and compares with the bound; every ratio is $`\le1`$.

| Check | Worst actual/bound |
|---|---|
| table, $`G(R)\le\alpha_PR+\beta_P`$ for $`R\le3P`$ (911 tables) | no violation |
| Lemma P, $`N\le10^6`$, six values of $`Y'`$ | 0.11 |
| Lemma H | $`\le1`$ per prime |
| (E0) against E2 | 0.990 |
| Lemma A′ + Bonferroni on $`[x,N]`$ | 0.998 |
| Lemma B + Bonferroni, per class, on $`[x,N]`$ | 0.935 |
| Lemma C, even witness, split domain | 0.40 |
| Lemma C′, odd witness | 0.18 |
| all $`b\le10^5`$: $`\max|\mathrm{Ex}(b)|`$ in a bucket against the bucket bound (`ex_all.cpp`) | 0.33 |

The values close to 1 for E0 and A′ show that the tests are sharp.

**An error found and fixed in review.**
- **The error.** The research sub-agent's first implementation charged each $`p_2\ne5`$ with $`\frac{23}{25}\frac{L_{\rm eff}}{p_2^2}B_d+3\mu E_d`$, mixing truncated inclusion–exclusion with "all classes minus two classes".
- **Why it is invalid.** $`B_d`$ is an upper bound, but the two subtracted classes need lower bounds.
- **The fix.** §10.5(ii) now takes the smallest of the three valid bounds (a), (b), (c), and Lemma C2′ replaces the monotonicity of Lemma C1.
- **Effect.** The error term becomes smaller, so the certificate actually gains slack: the worst ratio moves from the invalid 0.9917 to 0.9594.

**Other review findings.** No problem was found in the following, each checked step by step:
- Lemmas E0–E2, including the Abel summation, the local root-count bounds and the power of 2;
- Lemmas M, H, P;
- Lemma Bf, including monotonicity;
- Lemma W, including re-pairing;
- Lemma C′;
- the split of III.2 and its symmetric case;
- the enumeration of structures and $`b_{\min}`$;
- the monotonicity behind the interval certificate.

The table was checked in full by an independent program.

**Still to do.**
- Review by human experts.
- Lean formalisation. §10.1–10.6 are all elementary. Of the table, only the part the certificate actually uses is needed: about 631 entries, with total period about $`2.3\times10^6`$.
