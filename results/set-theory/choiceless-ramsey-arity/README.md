# Finite Ramsey homogeneity lowers arity without choice

Wentao Li · Research draft with OpenAI Codex assistance · November 22, 2026

[Proof (PDF)](choiceless-ramsey-arity.pdf) · [LaTeX source](choiceless-ramsey-arity.tex) · [BibTeX](citation.bib)

Brot, Cao and Fernández-Bretón asked whether their Ramsey-finiteness classes are monotone in arity for arbitrary sets, and whether Boolean Hindman finiteness for two summands implies Ramsey finiteness at higher arity. Both answers are affirmative in ZF. The argument works even when the underlying infinite set has no countably infinite subset. [Original paper, first posted 2019, Questions 5.1(2)–(3)](https://arxiv.org/abs/1910.11025) · [2021 journal version](https://doi.org/10.1016/j.apal.2021.102961)

**Theorem.** Suppose $1\le n<m<\omega$, and every binary coloring of $[X]^m$ has an infinite homogeneous subset. Then for every finite $k\ge1$ every coloring $c:[X]^n\to k$ has an infinite homogeneous subset. Consequently $R_n$-finite implies $R_m$-finite in the authors' two-color convention. No order on $X$ is required.

Color an $m$-element set $s$ by one bit: whether $c$ is constant on $[s]^n$. Let $Y$ be infinite and homogeneous for this test. The negative bit is impossible. By the finite Ramsey theorem there is an integer $N$ such that every $k$-coloring of the $n$-subsets of an $N$-element set admits a monochromatic $m$-element subset. The set $Y$ has an $N$-element subset in ZF. Applying this finite theorem supplies a positive test inside $Y$.

Thus every $m$-element subset of $Y$ passes. Any two $n$-element subsets differing by a one-element exchange have union of size $n+1\le m$, hence extend inside $Y$ to a common $m$-element set and have the same color. Any two $n$-element subsets are joined by finitely many such exchanges, as is seen by matching their two finite set differences. Therefore $c$ is constant on $[Y]^n$. Only finitely many choices from a single set enter this proof.

**Two Boolean summands.** For any coloring of the finite subsets of $X$, if $X$ is $R_2$-infinite, take an infinite $Z$ with constant color on its pairs. Fix $z\in Z$ and use the family $\{\{z,x\}:x\in Z\setminus\{z\}\}$. Its individual members and the symmetric differences of any two distinct members are pairs in $Z$, so they all have the same color. This is the argument of Theorem 3.8 in the source. By contraposition and the arity theorem, every $H_2$-finite set is $R_n$-finite for every $n\ge2$.

**Priority and extent.** The authors' Proposition 2.2 proved monotonicity for linearly orderable sets by removing a minimum. Their ordered hypergraph models already supply separations in the other direction. The contribution proposed here is the unconditional implication, via finite local homogeneity and exchanges. The two-summand answer is its consequence. The distinct question about the number of colors at a *fixed* arity requires a different argument. Provisional significance **52/100** if correct and new. Independent proof and priority review are pending.
