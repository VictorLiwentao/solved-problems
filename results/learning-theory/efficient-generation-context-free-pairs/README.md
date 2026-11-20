# Deciding efficient generation for pairs of deterministic context-free languages

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](efficient-generation-context-free-pairs.pdf) · [LaTeX](efficient-generation-context-free-pairs.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/efficient-generation-context-free-pairs/citation.bib)

Even for two deterministic context-free languages with infinite intersection, deciding whether a polynomial-time generator has a finite uniform expected mistake bound is Σ⁰₂-complete. The deterministic zero-mistake question has the same degree.

**Original question.** Xiaoyu Li, Andi Han, Dai Shi, Jiaojiao Jiang and Junbin Gao, 2026. [§5.2, hardness for natural classes and efficient closure generation](https://arxiv.org/abs/2608.05029)

## Argument

Two pushdown automata check alternating steps of the same deterministic computation. They share exactly the histories ending at checkpoints. A computably enumerable set controls the gaps between checkpoints. Infinitely many long gaps force arbitrarily many mistakes because the next safe output is too long to write.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending.

**Priority.** Independent priority review is pending. Li and coauthors pose the natural-class direction after an oracle-query separation. Arenas and coauthors use split computation histories with finite intersection for sample lower bounds. The draft requires infinite intersection throughout and classifies efficient generation in the explicit-string model. [ICML 2026 paper](https://proceedings.mlr.press/v306/arenas26a.html)

**Significance · 65/100.** Gives an exact undecidability classification and a fixed-pair separation for explicit outputs. The lower bound measures running time and uses long shared strings. [Scoring benchmark](../../../docs/scores-and-sources.md)
