# The null space of full vertex-deletion constraints in graph networks

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

The surviving dimension is exactly the number of bipartite components for degree-weighted cards. On connected nonbipartite graphs the constrained unit sphere is empty, including for almost every large uniformly random labeled graph.

**Original question.** Can simultaneously projecting onto the constraints from every vertex-deleted card yield a universal graph spectral basis under reconstruction assumptions? [Azizi, Kriege and Bischof, 2023, original full-deck proposal, later arXiv v1 discussion](https://openreview.net/pdf?id=KcRbiPwuNS)

**Scope and prior work.** The early OpenReview paper and the first arXiv version state the original proposal. The later AAAI paper retains degree-weighted constraints and emphasizes sampled cards for link prediction. Both counting-measure and degree-weighted full-deck forms are addressed.

**Significance estimate.** 54/100. It gives an exact obstruction to a specific universality proposal. The later practical algorithm samples a subset of cards and lies outside the disproof.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](vertex-deletion-constraint-rank.pdf) · [LaTeX source](vertex-deletion-constraint-rank.tex) · [BibTeX](citation.bib)

**Reproducible check.** The degree-card rank formula is checked by exact elimination and independent component coloring for all 1,024 simple graphs on five labeled vertices. [Python script](verify.py)

## Sources

- [Niloofar Azizi, Nils M. Kriege and Horst Bischof (2023), original full-deck proposal, later arXiv v1 discussion](https://openreview.net/pdf?id=KcRbiPwuNS)
- [Azizi, Kriege and Bischof, first arXiv version containing the conjecture](https://arxiv.org/abs/2408.12334v1)
- [Azizi, Kriege and Bischof, AAAI 2026 link-prediction paper](https://ojs.aaai.org/index.php/AAAI/article/view/39044)
