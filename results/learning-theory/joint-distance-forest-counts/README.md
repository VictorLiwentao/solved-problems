# What shortest paths and resistance can count together

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

The joint graph transformer counts exactly forests. For every cyclic pattern there are two connected diameter-two graphs it cannot distinguish, even though their counts differ.

**Original question.** Which homomorphism counts can distance-based graph networks recover? We study the published joint shortest-path and effective-resistance refinement. [Zhang et al., 2024, Appendix B, other architectures](https://arxiv.org/abs/2401.08514)

**Scope and prior work.** The repository already treated shortest paths alone and a resistance-only counterexample. The new cancellation preserves the two distances jointly. Equal forest counts still do not characterize the transformer.

**Significance estimate.** 74/100. This classifies every finite simple pattern for two widely used positional encodings used together. The proof supplies a different witness for each cyclic pattern.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](joint-distance-forest-counts.pdf) · [LaTeX source](joint-distance-forest-counts.tex) · [BibTeX](citation.bib)

**Reproducible check.** A standard-library Python check solves every column of both grounded Laplacians in exact rational arithmetic, then compares every pair of distance labels and counts the triangles on two 385-vertex graphs. [Python script](verify.py)

## Sources

- [Bohang Zhang, Jingchu Gai, Yiheng Du, Qiwei Ye, Di He and Liwei Wang (2024), Appendix B, other architectures](https://arxiv.org/abs/2401.08514)
- [Zhang et al., joint GD-WL and biconnectivity](https://arxiv.org/abs/2301.09505)
- [Gai et al., spectral-invariant graph models, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/6b7f9d9c1217a748391800871ff7d17d-Abstract-Conference.html)
