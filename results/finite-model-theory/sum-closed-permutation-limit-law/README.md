# A sum-closed permutation class without a logical limit law

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](sum-closed-permutation-limit-law.pdf) · [LaTeX source](sum-closed-permutation-limit-law.tex) · [Research catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/finite-model-theory/sum-closed-permutation-limit-law/citation.bib)

Even when two permutations can always be joined by direct sum, the probability that the first entry is the minimum can fail to converge.

**Original question.** Samuel Braunfeld and Matthew Kukla, 2021, Question 5.3. [Primary source](https://arxiv.org/abs/2111.06307)

## Argument

Start with sparse levels and insert carefully capped peaks using the Pantone–Vatter grid classes. A convolution estimate controls all the extra permutations created by closing under direct sum. Prepending the singleton gives an exact formula for the probability in terms of consecutive level sizes.

## Proof and priority

The PDF gives the full argument. Independent review and Lean formalization are pending.

Braunfeld and Kukla asked separately about general proper classes in Question 5.4. The sum-closed class here has an ordinary exponential growth rate, which rules out using oscillation of that rate as the argument. The construction uses Pantone and Vatter’s 2026 grid estimates. Falgas-Ravry, Markström, Räty and Skerman study limiting probabilities for small classes. [Grid estimates](https://arxiv.org/abs/2610.30369v1) · [Small classes](https://arxiv.org/abs/2610.34328)

A search of the primary literature and follow-up work through November 19, 2026 did not identify an earlier resolution of this specific question. Priority awaits independent confirmation.

**Significance estimate: 65/100.** Separates exponential growth from first-order convergence under direct-sum closure. The obstruction is visible in a sentence using only two variables. A full resolution of the three-dimensional Navier–Stokes existence and smoothness problem sets the benchmark at 100.
