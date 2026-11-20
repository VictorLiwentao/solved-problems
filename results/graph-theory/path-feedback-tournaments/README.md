# Path feedback arc sets in tournaments are NP-complete

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](path-feedback-tournaments.pdf) · [LaTeX](path-feedback-tournaments.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/graph-theory/path-feedback-tournaments/citation.bib)

Deciding whether deleting the arcs of one undirected path makes a tournament acyclic is NP-complete, even given an ordering of backward degree at most two.

**Original question.** Pierre Aboulker, Guillaume Aubian and Raul Lopes, 2024. [2024 path question, numbered Problem 4.4 in the published version](https://arxiv.org/abs/2402.10782v2)

## Argument

The construction encodes a Boolean value by which alternating pairs point backward inside a tournament block. A false clause forces a cycle through its six ports. A satisfying assignment breaks every such cycle and leaves a collection of paths that can be joined into one.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The program enumerates all 120 local orders and checks 72 signed formula and assignment pairs. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The sparse tournament block and the polynomial-time matching algorithm are due to Davot, Isenmann, Roy and Thiébaut. Aboulker, Aubian and Lopes established hardness for forest and tree feedback sets. The reduction here enforces the extra path condition. [Degreewidth paper](https://arxiv.org/abs/2212.06007) · [Published problem](https://doi.org/10.46298/dmtcs.14281)

**Significance · 69/100.** Resolves a specific recognition problem at the boundary between matching and forest feedback sets. Hardness persists when a degree-two ordering is supplied. [Scoring benchmark](../../../docs/scores-and-sources.md)
