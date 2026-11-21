# A depth-independent width for stable ReLU graph separation

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Width 2n+2 suffices at every fixed depth on graphs of at most n vertices. The expected output separation has a power-law lower bound in Tree Mover’s Distance.

**Original question.** Does a width depending only on graph size and input dimension make ReLU message passing lower-Hölder in expectation at every depth? [Davidson and Dym, 2024, Section 4.2 (ICLR 2025)](https://arxiv.org/abs/2406.06984)

**Scope and prior work.** The source proves the width-one obstruction and lower bounds on any possible exponent. The parameter distribution, compact node features and graph-size bound are specified. The theorem is pairwise in expectation over initialization.

**Significance estimate.** 68/100. It proves the conjectured width guarantee for a common graph architecture and gives a concrete width independent of depth. The lower-bound exponent can deteriorate with depth.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](wide-relu-graph-separation.pdf) · [LaTeX source](wide-relu-graph-separation.tex) · [BibTeX](citation.bib)

**Reproducible check.** Exhaustive enumeration verifies the hinge-variation identity, the matching bound and the unequal-cardinality signal on 15,876 ordered multiset pairs. [Python script](verify.py)

## Sources

- [Yair Davidson and Nadav Dym (2024), Section 4.2 (ICLR 2025)](https://arxiv.org/abs/2406.06984)
- [Davidson and Dym, ICLR conference version](https://proceedings.iclr.cc/paper_files/paper/2025/hash/89d0d5c2f720921df93bbb8fef514571-Abstract-Conference.html)
