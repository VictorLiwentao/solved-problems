# Well-orderable unions in the countable partition model

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](well-orderable-unions-partition-model.pdf) · [LaTeX source](well-orderable-unions-partition-model.tex) · [Research catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/well-orderable-unions-partition-model/citation.bib)

A well-orderable family of well-orderable sets has a well-orderable union for every ambient number of atoms in the countable partition model.

**Original question.** Amitayu Banerjee, 2021, Question 8.4 in v1, later Question 7.2; remaining case posed by Brinda Venkataramani in Question 10.2 (2026). [Primary source](https://arxiv.org/abs/2109.05914v1)

## Argument

Refine one support for the indexed family by singling out its countable blocks. Inside each remaining block, construct a permutation with as many transposed pairs and fixed points as there are atoms. Four conjugates generate any desired permutation, with the same four factors working simultaneously across blocks.

## Proof and priority

The PDF gives the full argument. Independent mathematical review is pending.

Bruce treated finite partitions. In the countable partition model Venkataramani proved the union conclusion below $\aleph_{\omega_1}$, and proved failure of the more general choice-function principle above and at that threshold. The open range in Question 10.2 is the contribution here. [Venkataramani, Corollary 7.4 and Question 10.2](https://arxiv.org/abs/2610.29752)

A search through November 19, 2026 found no earlier resolution of the specific assertion claimed here. Priority awaits independent confirmation.

**Significance estimate: 62/100.** Completes the union theorem across all atom cardinalities, including where choice for well-ordered families of arbitrary nonempty sets fails. The 100-point benchmark is a full resolution of three-dimensional Navier–Stokes existence and smoothness.

## Lean formalization

The union of an internally well-orderable family of internally well-orderable sets has an internal well-order, for every uncountable cardinality of the atoms. Countable partition supports apply to the orders themselves. The proof includes singular atom cardinals. [Statement](../../../lean/Statements/WellOrderUnion.lean) · [Proof](../../../lean/SolvedProblems/WellOrderUnion.lean) · [Comparator and source alignment](../../../lean/submissions/well-orderable-unions-partition-model/)
