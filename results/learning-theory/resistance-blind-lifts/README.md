# Resistance-distance graph transformers can miss bipartiteness

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Two connected graphs have identical resistance-refinement colors at every depth. One is bipartite and the other contains triangles. Shortest-path refinement and their Laplacian spectra both distinguish them.

**Original question.** Can resistance-distance refinement encode graph spectra and distinguish every pair of graphs distinguished by shortest-path refinement? [Zhang, Luo, Wang and He, 2022, Section 6 (ICLR 2023; first posted in 2022)](https://openreview.net/forum?id=r9hNv76KoT3)

**Scope and prior work.** The source gives examples in the reverse direction. Black and coauthors later suggested incomparability from experiments. The proof handles arbitrarily many rounds and even unique initial colors for the corresponding base vertex fibers.

**Significance estimate.** 76/100. It separates widely used graph-transformer encodings and exhibits a basic graph property invisible to resistance refinement at every depth.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](resistance-blind-lifts.pdf) · [LaTeX source](resistance-blind-lifts.tex) · [BibTeX](citation.bib)

**Reproducible check.** Exact grounded-Laplacian inverses certify equality of every paired resistance across two 78-vertex graphs. Independent graph searches check distances, triangle counts and bipartiteness. [Python script](verify.py)

## Sources

- [Bohang Zhang, Shengjie Luo, Liwei Wang and Di He (2022), Section 6 (ICLR 2023; first posted in 2022)](https://openreview.net/forum?id=r9hNv76KoT3)
- [Black, Wan, Mishne, Nayyeri and Wang, Comparing Graph Transformers via Positional Encodings (ICML 2024)](https://proceedings.mlr.press/v235/black24b.html)
- [Zhang et al., original paper, Section 6](https://arxiv.org/abs/2301.09505)
- [Xu, Zhou and Pan, graphs sharing global resistance spectra](https://arxiv.org/abs/2403.06096)
