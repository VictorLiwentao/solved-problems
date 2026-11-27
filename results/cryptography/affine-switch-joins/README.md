# How many joins repair a bank of arithmetic switches?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

[Proof (PDF)](affine-switch-joins.pdf) · [LaTeX](affine-switch-joins.tex) · [Reproduce the checks](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/affine-switch-joins/citation.bib)

In David Heath’s EUROCRYPT 2024 switch system, a closed switch copies its input to its output port. An open switch leaves that port unconstrained. Consider a fixed bank of these switches. The circuit must make every existing output port match its input even if a switch opens. A graph $G$ specifies which pairs can open together. Single openings are always allowed, and at most two switches open. How much does a fixed set of affine equality checks cost? Heath measures this cost by adding the bit widths of the joins. [Heath’s paper, §§3.2–3.3](https://doi.org/10.1007/978-3-031-58740-5_1)

**Result.** If each word has width $w$, the exact minimum total join width is $w\lceil\log_2(1+\chi(G))\rceil$, where $\chi(G)$ is the number of colors needed to give adjacent vertices different colors. For example, if any pair among 15 ports may open, four word joins suffice and four are necessary in this model. Heath’s matching-width affine gates attain the bound.

**Proof idea.** Every nonzero subgroup of a finite abelian 2-group contains an element of order two. Applied to a failed equality check, this leaves just one test vector per port. Those vectors must be nonzero at every port and distinct on every allowed pair. They give a proper coloring, and the binary names of the colors supply the coefficients of matching checks.

**Different widths.** Allow arbitrary additive maps between word groups and fix a coloring. At each bit level, count the colors that appear on ports at least that wide. The bits needed to name those colors, summed over the levels and minimized over a single coloring, give the exact cost. A five-port example shows why choosing a new coloring at each level can underestimate it. This extension uses a broader class of gates than Heath’s matching-modulus affine gates.

**Proof status.** The manuscript gives a lower bound, a matching construction, and an evaluation argument for the equal-width circuit. A Python check searches the finite groups directly and recovers the predicted optimum on 1,098 graph/width instances through four ports and four widths of the five-port example. Independent review is pending.

**Priority status.** Heath introduced the switches and join-width measure. We formulated this optimization for a fixed bank and fixed, control-independent checks. Restricted-erasure codes already connect graph colorings with independence of code columns. Priority for the switch application and mixed-width optimum remains unverified. [Gonen, Haviv, Langberg and Sprintson](https://arxiv.org/abs/2005.06947)

**Significance estimate · 54/100.** There is a matching lower bound and construction for every conflict graph, including an exact mixed-width formula. The bound concerns the specified ports and checks. [Scoring benchmark](../../../docs/scores-and-sources.md)
