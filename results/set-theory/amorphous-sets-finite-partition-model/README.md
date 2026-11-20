# Every infinite set splits in the finite partition model

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](amorphous-sets-finite-partition-model.pdf) · [LaTeX source](amorphous-sets-finite-partition-model.tex) · [Research catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/amorphous-sets-finite-partition-model/citation.bib)

At every rank in Bruce’s model, each infinite set splits into two infinite subsets. This rules out amorphous sets even though infinite Dedekind-finite sets exist there.

**Original question.** Benjamin Baker Bruce, 2016, finite partition model, recorded explicitly as open by Brinda Venkataramani in 2026. [Primary source](https://scholar.rose-hulman.edu/rhumj/vol17/iss1/4/)

## Argument

Permutations on half of an infinite block create an infinite orbit. If the orbit were cofinite, a commuting group on the other half would fix both the orbit and its finite complement pointwise. Its conjugates then force the original action to be trivial.

## Proof and priority

The PDF gives the full argument. Independent mathematical review is pending.

Bruce proved that the atoms have no amorphous subset. Venkataramani credits Bruce with the arbitrary-rank question and records it as open in Table 1 and the discussion before Question 10.2. [Later statement](https://arxiv.org/abs/2610.29752)

A search through November 19, 2026 found no earlier resolution of the specific assertion claimed here. Priority awaits independent confirmation.

**Significance estimate: 65/100.** Settles a decade-old question about arbitrary sets in a model without choice. The argument reaches beyond sets of atoms by analyzing group actions on arbitrary model objects. The 100-point benchmark is a full resolution of three-dimensional Navier–Stokes existence and smoothness.

## Lean formalization

Every infinite set in Bruce’s finite partition model has a supported subset such that both it and its complement are infinite. The carrier can have arbitrary rank. Both parts have explicit finite partition supports in the external model. [Statement](../../../lean/Statements/AtomSplit.lean) · [Proof](../../../lean/SolvedProblems/AtomSplit.lean) · [Comparator and source alignment](../../../lean/submissions/amorphous-sets-finite-partition-model/)
