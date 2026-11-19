# An atomic permutation class without a growth rate

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](atomic-oscillating-growth.pdf) · [LaTeX source](atomic-oscillating-growth.tex) · [Research catalogue](../../../README.md) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/2f1a7f8dc8cdf96f6db69be15543c26a52d97d53/citations.bib#L377-L383)

Every pair of patterns in this class occurs together in a third, yet its upper and lower exponential growth rates differ.

**Original question.** Jay Pantone and Vincent Vatter, 2026, Question 2.6. [Primary source](https://arxiv.org/abs/2610.30369v1)

## Argument

Arrange finite permutation blocks in an infinite direct sum. The prefix formed so far can be arbitrarily large. Choose the next sparse length after measuring that prefix, so its cost becomes negligible. High-growth grid blocks then supply the next dense length. Taking the union of two finite occurrences proves joint embedding.

## Proof and priority

The PDF gives the full argument. Independent review and Lean formalization are pending.

Pantone and Vatter prove oscillation for a class with infinitely many maximal elements. Their Proposition 6.6 explains why their example lacks joint embedding. The grid classes and the coefficient estimate in their Proposition 6.3 are inputs here. Their questions about well-quasi-order and finite bases are separate.

A search of the primary literature and follow-up work through November 19, 2026 did not identify an earlier resolution of this specific question. Priority awaits independent confirmation.

**Significance estimate: 70/100.** Settles the joint-embedding version of the growth-rate question. It extends a recent counterexample to a structural hypothesis that the original construction explicitly fails. A full resolution of the three-dimensional Navier–Stokes existence and smoothness problem sets the benchmark at 100.
