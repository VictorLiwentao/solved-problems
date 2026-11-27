# Rigid relations on subsets of ordinal Cantor cubes

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](rigidity-ordinal-cubes.pdf) · [LaTeX](rigidity-ordinal-cubes.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/rigidity-ordinal-cubes/citation.bib)

In ZF every subset of every ordinal-indexed binary cube has a rigid binary relation on its own points. The first Kinna–Wagner principle therefore implies the rigid relation principle.

**Original question.** Paul Howard and Eleftherios Tachtsis, 2016. [§6, Problem 5, following Hamkins’s 2009 question](https://doi.org/10.4064/fm960-12-2015)

## Argument

Split cells using their first distinguishing coordinate. A small directed path on the children lets the graph recover each cell from its maximal proper modules. Induction along the ordinal then forces every point to be fixed.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. An exhaustive test checks every subset of the three-bit cube and every candidate permutation. [Run the check](verify.py)

**Priority.** Independent priority review is pending. Hamkins and Palumbo handled sets of reals and certain products. Howard and Tachtsis proved rigidity for the whole cube. [2009 source](https://mathoverflow.net/questions/6262) · [Hamkins and Palumbo](https://arxiv.org/abs/1106.4635)

**Significance · 76/100.** Extends the theorem for sets of reals to arbitrary ordinal-indexed cubes and derives a global implication between two weak choice principles. [Scoring benchmark](../../../docs/scores-and-sources.md)
