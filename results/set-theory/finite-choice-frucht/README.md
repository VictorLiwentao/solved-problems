# Finite choice implies Frucht's theorem

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](finite-choice-frucht.pdf) · [LaTeX](finite-choice-frucht.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/finite-choice-frucht/citation.bib)

Choice for families of nonempty finite sets suffices to realize every group as the automorphism group of a simple graph in ZFA. All five implications in Pinsky’s list follow.

**Original question.** Brian Pinsky, 2023. [Appendix 6.1, five weak-choice implications](https://arxiv.org/abs/2305.11382v1)

## Argument

Choose one member of each finite family of subsets of the label set. A moving automorphism either cycles a finite orbit of singletons or swaps the two halves of an infinite orbit. Both contradict invariance of the selector. The fixed labels then encode the group multiplication table in a graph.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending.

**Priority.** Independent priority review is pending. Pinsky provided the earlier bounds and colored Cayley construction. Chen and Ju subsequently related Frucht’s theorem to embeddings into rigid graphs. [Author’s revision](https://sites.math.rutgers.edu/~bp466/frucht.pdf) · [Chen and Ju](https://arxiv.org/abs/2607.23891v2)

**Significance · 76/100.** Finds one weak-choice hypothesis that settles five stated implications, including the ordering principle. Pinsky had already shown why choosing separately for each fixed family size is insufficient. [Scoring benchmark](../../../docs/scores-and-sources.md)
