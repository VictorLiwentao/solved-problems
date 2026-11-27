# Generic finite witnesses for nonclosed sparse ReLU matrix-product models

Wentao Li · Prepared with assistance from OpenAI Codex · November 21, 2026

For a fixed missing limit matrix, almost every tuple of more inputs than free parameters witnesses nonattainment. A larger generic tuple works for every such matrix at once.

**Original question.** Can the exponential finite grid used to witness a nonclosed set of sparse matrix products be replaced by a smaller training set? [Quoc-Tung Le, Elisa Riccietti and Rémi Gribonval, 2023, Section 3.2, question following Lemma 3.2 and Figure 1](https://arxiv.org/abs/2306.02666)

**Significance estimate.** 60/100. Replaces an exponential grid with a parameter-linear threshold that works for arbitrary depth and fixed supports. It also gives a uniform generic-data statement for all missing matrices.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 21, 2026 found the following related results. Independent priority review is pending.

The original paper provides the matrix-product criterion and the grid construction. The draft applies semialgebraic incidence dimension to the family of coincidence sets.

[Read the proof (PDF)](generic-sparse-network-witnesses.pdf) · [LaTeX source](generic-sparse-network-witnesses.tex) · [BibTeX](citation.bib)

**Reproducible check.** Checks the triangular matrix-product limit and the affine independence of all triples in an explicit eleven-point parabola example. The dimension argument covers general architectures. [Python script](verify.py)

## Sources

- [Quoc-Tung Le, Elisa Riccietti and Rémi Gribonval (2023), Section 3.2, question following Lemma 3.2 and Figure 1](https://arxiv.org/abs/2306.02666)
- [Le, Riccietti and Gribonval, NeurIPS conference paper and appendix](https://proceedings.neurips.cc/paper_files/paper/2023/file/cdda0657a9f32bc7ddd4343686e7371e-Paper-Conference.pdf)
