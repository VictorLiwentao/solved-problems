# How wide must a set network be if each interaction sees only k elements?

Wentao Li · Research draft with OpenAI Codex assistance · November 21, 2026

Wagstaff, Fuchs, Engelcke, Osborne and Posner asked how the latent width for universal Janossy pooling depends on set size and interaction order. Syed, Nambiar and Siegel established a lower bound of order $[d(n-k)]^{1/k}$ for fixed $k$ and identified a gap to the $O(nd)$ upper bound. Here the input consists of $n$ points of $[0,1]^d$, the target is scalar and the encoder and decoder can both depend on that target. [Wagstaff et al., §6.1.4, 2022](https://arxiv.org/abs/2107.01959) · [Syed et al., §5, 2026](https://arxiv.org/abs/2605.08377)

**Theorem.** Fix an interaction order $k\geq1$ and $C\geq0$. For $1\leq d\leq n^C$ the minimum universal latent width is $\Theta_{k,C}(nd)$ as $n$ grows. The lower bound applies to both ordered sampling with replacement and summation over ordered tuples of distinct indices. The models here share one continuous interaction map across all tuples. The result leaves the optimal constants, unrestricted joint growth of the parameters, and index-dependent interaction maps open.

**Finite bound.** Reserve $b$ of the $n$ positions for tags and let $\ell=n-b>0$, $D=d\ell$. Choose $g\geq2$ distinct tag values. Whenever
$$
 \binom{b+g-1}{g-1}\geq D,\qquad L=\binom{g+k-2}{k-1},
$$
universality requires $M L\geq D$, where $M$ is the latent width. Indeed, if $ML<D$, there is a single continuous scalar target on unordered inputs whose uniform approximation error is at least $1/\sqrt D$ for every choice of the two maps.

**Proof.** Choose $\ell$ disjoint closed balls in the interior of the input cube, disjoint also from the $g$ tag values. For $u=(u_1,\ldots,u_\ell)\in S^{D-1}$, with each block in $\mathbb R^d$, put $x_j(u)=c_j+\epsilon u_j$ in ball $j$. The unordered collection of these tail points determines $u$ by reading the balls. Tags have multiplicities $m_i\geq0$ with $\sum_i m_i=b$.

Fix any continuous interaction map $\phi:([0,1]^d)^k\to\mathbb R^M$. Expand the sum of its outputs according to which argument positions use tags. If $a_i$ positions use tag $i$, their multiplicity is $\prod_i m_i^{a_i}$ with replacement and $\prod_i (m_i)_{a_i}$ without replacement, where $(m)_a=m(m-1)\cdots(m-a+1)$. Sum the other positions over admissible tail indices. The term involving only tags is independent of $u$. After subtracting that term, the latent sum is a polynomial of degree at most $k-1$ in the tag multiplicities with continuous vector coefficients in $u$. Eliminating $m_g=b-\sum_{i<g}m_i$ leaves at most $L$ monomials. Normalizing the sum by its tuple count simply rescales the coefficients.

Concatenate all coefficients to obtain a continuous map $S^{D-1}\to\mathbb R^{ML}$. When $ML<D$, Borsuk–Ulam gives antipodes $u,-u$ with identical coefficients. Adding back the tag-only terms gives identical latent vectors for these antipodes under **every choice of tag multiplicities**. This is where the shared tuple map matters.

There are enough tag patterns to assign a distinct pattern to each of the $D$ scalar coordinates of $u$. On the slice with pattern $j$ set the target equal to coordinate $j$. Each slice is a continuous embedded copy of the sphere, since the domain is compact and the unordered input space is Hausdorff. The slices are disjoint. Their union is closed in the compact metrizable quotient $([0,1]^d)^n/\mathfrak S_n$, so Tietze extension gives a continuous target on the whole quotient. This target is fixed before $\phi$ is chosen. For the antipodes found above, some coordinate has absolute value at least $1/\sqrt D$. Under that tag pattern, the readout must output the same number for two targets separated by at least $2/\sqrt D$. This proves the finite bound.

Take $b=\lfloor n/2\rfloor$ and choose a fixed integer $g>C+2$. The number of tag patterns grows as a positive constant times $n^{g-1}$ and eventually exceeds $nd$. Now $D\geq nd/2$ and $L$ depends only on $k,C$. The matching upper bound $2nd+1$ is the additive invariant embedding bound cited by Syed et al. A $k$-tuple map can ignore all but its first input and reproduce the additive sum up to a nonzero constant for $n\geq k$. This proves the theorem.

For scalar elements one can take just two tag values and $b=\lfloor n/2\rfloor$. The same argument gives $M\geq\lceil n/2\rceil/k$ even when $k$ varies. In particular, bounded width cannot be universal along any sequence with $k=o(n)$. The proof concerns approximation of arbitrary continuous targets. It does not give the typical width required for a prediction task on a particular distribution.

**Priority and significance.** The antipodal obstruction and additive upper bound have precedents in the cited work. The step advanced here is the polynomial dependence on repeated tag counts, which allows a single collision to handle many more scalar readouts. Provisional significance **64/100** if correct and new. It closes an exponent gap for shared finite-order pooling over a broad range of input dimensions. The bound concerns worst-case continuous universality. Independent proof and priority review are pending.
