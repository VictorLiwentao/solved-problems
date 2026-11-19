# An infinite poset with no infinite chain or antichain in the finite partition model

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](ramsey-finite-partition-model.pdf) · [LaTeX source](ramsey-finite-partition-model.tex) · [Research catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/ramsey-finite-partition-model/citation.bib)

In Bruce’s model, subsets of the atoms modulo finite changes form an infinite poset with no infinite chain or antichain. Comparability gives a two-coloring with no infinite homogeneous set.

**Original question.** Amitayu Banerjee, 2021, order and Ramsey parts of Question 8.1 in v1, later Question 7.1. [Primary source](https://arxiv.org/abs/2109.05914v1)

## Argument

Fix a finite partition supporting an infinite family of equivalence classes. Some representative splits one block into two infinite pieces. Permuting that block produces two comparable classes and two incomparable classes inside the original family.

## Proof and priority

The PDF gives the full argument. Independent mathematical review and Lean formalization are pending.

Banerjee’s 2021 preprint contrasts Bruce’s model with the basic Fraenkel model, where the infinite Ramsey theorem holds. The equivalence relation and the comparability coloring are both defined inside Bruce’s model. [Revised question](https://arxiv.org/abs/2109.05914v4) · [Bruce’s construction](https://scholar.rose-hulman.edu/rhumj/vol17/iss1/4/)

A search through November 19, 2026 found no earlier resolution of the specific assertion claimed here. Priority awaits independent confirmation.

**Significance estimate: 55/100.** One explicit Boolean algebra answers both the order and Ramsey questions in this model. It gives a short explanation of why the choice of supports affects Ramsey behavior. The 100-point benchmark is a full resolution of three-dimensional Navier–Stokes existence and smoothness.
