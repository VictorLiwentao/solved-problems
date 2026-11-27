# How many hosts are needed for simultaneous induced saturation of cographs?

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](simultaneous-cograph-saturation.pdf) · [LaTeX](simultaneous-cograph-saturation.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/graph-theory/simultaneous-cograph-saturation/citation.bib)

Countably infinitely many hosts are necessary and sufficient even for connected nontrivial cographs. Two explicit maximal families characterize which targets can share a host with the three-vertex path.

**Original question.** Marthe Bonamy, Carla Groenland, Tom Johnston, Natasha Morrison and Alex Scott, 2025. [§8, simultaneous hosts for finite cographs](https://arxiv.org/abs/2506.08810)

## Argument

Every newly created copy of a forbidden graph must use both endpoints of the edited pair. A larger target with two disjoint induced copies of the smaller target therefore cannot share its host. When the three-vertex path is a target, the host must be a union of cliques, which makes a full compatibility classification possible.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending.

**Priority.** Independent priority review is pending. The individual existence theorem and the simultaneous-host question come from Bonamy and coauthors. Earlier work also studied forbidden families under a different quantifier on which target an edit creates. [Published question](https://doi.org/10.4153/S0008414X26102132) · [Axenovich and Csikós](https://doi.org/10.1016/j.disc.2019.01.006)

**Significance · 46/100.** Answers the common-host question with an infinite incompatibility family and an exact classification around the three-vertex path. The covering lower bound uses an elementary obstruction. [Scoring benchmark](../../../docs/scores-and-sources.md)
