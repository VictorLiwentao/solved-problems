# High-confidence graph reconstruction with maximal independent set queries

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](high-confidence-mis-queries.pdf) · [LaTeX](high-confidence-mis-queries.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/graph-theory/high-confidence-mis-queries/citation.bib)

For inverse-polynomial failure the optimal nonadaptive query count is Θ(min{n², Δ² log n}) across all maximum degrees, ruling out the proposed improved bound.

**Original question.** Lukas Michel and Alex Scott, 2024. [Problem 5.2](https://arxiv.org/abs/2404.03472)

## Argument

Hide a single edge among randomly chosen blockers. When every query containing its endpoints also includes a blocker, two graphs give identical answers. Positive correlation gives a lower bound on how often this happens for any fixed schedule, and averaging handles randomized schedules.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The finite check covers 2,560 paired graph queries and 1,280 exact correlation inequalities. [Run the check](verify.py)

**Priority.** Independent priority review is pending. Konrad, O’Sullivan and Traistaru gave the upper bound and specified the confidence convention. Michel and Scott supplied the sparse lower bound. The new argument gives the matching dense lower bound. Aldridge used a related correlation argument for individual items in group testing. [Group-testing argument](https://arxiv.org/abs/1801.08590) · [ITCS upper bound](https://doi.org/10.4230/LIPIcs.ITCS.2025.66) · [Journal version of the question](https://doi.org/10.1016/j.tcs.2025.115121)

**Significance · 72/100.** Determines the optimal order throughout the degree range at polynomial confidence. The lower bound distinguishes the original high-confidence question from reconstruction with constant success probability. [Scoring benchmark](../../../docs/scores-and-sources.md)
