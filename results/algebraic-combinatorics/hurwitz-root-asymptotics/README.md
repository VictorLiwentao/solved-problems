# How the roots of deformed monotone Hurwitz polynomials approach their limits

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](hurwitz-root-asymptotics.pdf) · [LaTeX source](hurwitz-root-asymptotics.tex) · [Result catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/algebraic-combinatorics/hurwitz-root-asymptotics/citation.bib)

## Original question

Fix a permutation of $d$ letters. Its cycle lengths form its *profile*. Coulter, Do, and Moskovsky defined a polynomial that counts its transitive monotone factorizations into transpositions. Increasing the genus $g$ by one adds two transpositions to the required length. In Conjecture 3.15 they predicted where the polynomial’s roots converge as $g$ increases and which way they move. [Original paper, §3.3](https://doi.org/10.4153/S0008414X25101168) · [Conjecture 3.15, p. 17](https://arxiv.org/pdf/2308.04015#page=17)

## Result

For every fixed profile of degree $d\ge 2$, all $d-1$ roots are real and simple for sufficiently large $g$. In increasing order, their limits are

$$u_j=1-\frac{d-1}{j},\qquad 1\le j\le d-1.$$

Every root with limit below $-1$ eventually increases strictly to its limit from below. Every root with limit strictly between $-1$ and zero eventually decreases strictly to its limit from above. Zero is always a root, as is $-1$ when $d$ is odd. For every moving root the ratio of its distances to its limit at genera $g+1$ and $g$ tends to

$$\left(\frac{d-2}{d-1}\right)^2.$$

For example, the smallest root for profile $(4,2,1)$ is about $-5.041605$ at genus 10 and $-5.001056$ at genus 20. These values appear in the original paper’s Figure 3. The theorem explains why the root approaches $-5$ from below and why each additional genus eventually leaves about $69.44\%$ of its previous distance.

The alternating order of the negative limits also proves eventual interlacing when one cycle length increases by one. The proof also gives an algorithm to compute a sufficient starting genus for any input profile. For that profile, checking whether the motion already starts at genus zero reduces to finitely many exact polynomial comparisons. A single proof of monotonicity and real-rootedness at every genus for all profiles remains open in this work.

## Proof and prior work

The character formula expresses the generating function in factorization length as a rational function. The largest exponential term gives the limiting polynomial. To find the direction of motion, the proof computes the next term at each limiting root. At this order the connectedness condition subtracts exactly the terms obtained by isolating a fixed point. Consequently, at fixed degree and factorization length, the profile enters that correction only through the number of its fixed points.

The leading limiting polynomial also follows by specializing an earlier large-genus theorem of Accadia, Lewański, and Ruzza. The contribution claimed here is the explicit next term for the connected polynomial and the resulting directions and rates. A literature search found no earlier derivation of this directional formula. Priority and the proof await independent review. [Accadia, Lewański, and Ruzza, Theorem 6](https://arxiv.org/abs/2604.12880)

## Reproducing the checks

Run the following from this directory with Python’s standard library.

```sh
python3 verify.py
```

The checker counts words directly in degree four at genera zero and one, and compares them with the cut-and-join recurrence. It then uses exact arithmetic to check both exponential terms for every profile of degrees three through six at enough parameter values to determine the polynomials. It also gives rational brackets for the two sample values of the smallest root above. The PDF supplies the proof for arbitrary degree. Lean formalization is pending. [Checker](verify.py) · [Verification guide](../../../docs/verification.md)
