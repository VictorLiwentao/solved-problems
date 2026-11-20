# Malicious-verifier statistical zero knowledge for proofs of proximity

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](malicious-verifier-proximity.pdf) · [LaTeX](malicious-verifier-proximity.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/malicious-verifier-proximity/citation.bib)

In the polylogarithmic regime, honest-verifier statistical proofs of proximity admit statistical simulation against arbitrary verifier strategies. The transformation applies to the original graph expansion and bipartiteness promises and keeps verification polynomial in log input length, security parameter and inverse proximity.

**Original question.** Itay Berman, Ron D. Rothblum and Vinod Vaikuntanathan, 2017. [§1.1, footnote 7 in the 2017 preprint (footnote 10 at ITCS 2018)](https://eprint.iacr.org/2017/114)

## Argument

Use the original paper’s reduction to two short oracle circuits with an entropy gap. The public-coin Entropy Difference protocol evaluates each sampler on a specified seed. Its simulator can do the same with oracle access to the large input. The Goldreich–Sahai–Vadhan transformation then handles arbitrary verifier challenges without reading the input table.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending.

**Priority.** Independent priority review is pending. The argument composes Berman–Rothblum–Vaikuntanathan’s Lemma A.1 with existing protocols. Bouland and coauthors explicitly observed that the classical equivalence relativizes. The contribution claimed here is the application with proximity, time and auxiliary-input accounting. [Conference statement](https://doi.org/10.4230/LIPIcs.ITCS.2018.19) · [Goldreich–Vadhan](https://doi.org/10.1109/CCC.1999.766262) · [Goldreich–Sahai–Vadhan](https://people.seas.harvard.edu/~salil/research/dishonest-abs.html) · [Oracle precedent, §2](https://arxiv.org/abs/1609.02888)

**Significance · 65/100.** Upgrades a class of sublinear proof systems and covers both graph promises. The reduction and the simulation methods are classical, and the transformation allows polynomial overhead. [Scoring benchmark](../../../docs/scores-and-sources.md)
