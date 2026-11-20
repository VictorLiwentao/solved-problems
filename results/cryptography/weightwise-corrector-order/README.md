# Corrector orders of weightwise almost perfectly balanced Boolean functions

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](weightwise-corrector-order.pdf) · [LaTeX](weightwise-corrector-order.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/weightwise-corrector-order/citation.bib)

For any fixed positive excess, a set of dimensions of natural density one admits weightwise almost perfectly balanced functions whose corrector order exceeds the conjectured bound by exactly that amount.

**Original question.** Martin Grenouilloux, Chunlei Li and Pierrick Méaux, 2026. [Conjecture 1, the nonexistence clause for correctors](https://doi.org/10.1007/978-3-032-27574-5_13)

## Argument

The signed imbalance of each Hamming-weight slice becomes a polynomial coefficient. For each disjoint block of 51 one-bits, a spectral-null polynomial raises the attainable multiplicity by one. The resulting functions realize every intermediate order. Corrector order measures cancellation after summing coefficients of equal weight. The separate question about ordinary resilience remains open here.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The check verifies the compressed exact-multiplicity certificate and compares the moment and Walsh calculations on 96 small balanced slice profiles. [Run the check](verify.py)

**Priority.** Independent priority review is pending. Grenouilloux, Li and Méaux related corrector order to moment equations. Richard Stong supplied the length-2⁵¹ polynomial in Buhler, Golan, Pratt and Wagon. The application gives exact corrector orders and a density-one conclusion. [Original manuscript](https://orbilu.uni.lu/handle/10993/68301) · [Stong’s construction, Theorem 7.1](https://arxiv.org/abs/1912.03491v1)

**Significance · 62/100.** Refutes a universal corrector bound and proves that any fixed excess occurs in almost all dimensions. The seed and the original moment characterization both come from prior work. [Scoring benchmark](../../../docs/scores-and-sources.md)
