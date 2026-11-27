# Finite universal targets for tuple dicolouring

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](finite-targets-tuple-dicolouring.pdf) · [LaTeX](finite-targets-tuple-dicolouring.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/graph-theory/finite-targets-tuple-dicolouring/citation.bib)

For k-tuple n-dicolouring a finite circular-homomorphism target exists exactly for k in {1, 2, n−1, n}. A finite acyclic-homomorphism target exists exactly for k in {1, n}.

**Original question.** Gil Puig i Surroca, 2026. [Chapter 7, Problem 7.14, thesis defended January 2026](https://www.ub.edu/comb/koljaknauer/Gil_manuscript.pdf)

## Argument

Give each colour its own rational coordinate that increases along arcs. Any finite universal target must contain a representative for each colour type. Forcing cycles and counting colour stars shows that these representatives already form a target of the prescribed kind classified in the thesis.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The finite check independently tests the coordinate constraints on cycles and the counting argument for colour stars. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The classification for a target on the prescribed type set is Puig i Surroca’s Theorem 7.11. His later Problem 7.14 allows arbitrary targets. [Earlier question of Hochstättler, Schröder and Steiner](https://arxiv.org/abs/1812.02420)

**Significance · 67/100.** Classifies arbitrary finite targets for both homomorphism notions and shows that adding auxiliary vertices cannot expand the known list. [Scoring benchmark](../../../docs/scores-and-sources.md)
