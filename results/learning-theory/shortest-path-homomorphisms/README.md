# The homomorphism counts determined by shortest-path graph refinement

Wentao Li · Prepared with assistance from OpenAI Codex · November 21, 2026

Shortest-path refinement counts exactly the forests, yet distinguishes connected graphs agreeing on every forest count. No ordinary homomorphism family represents it.

**Original question.** Does stable color refinement always have a representing graph-homomorphism family, and what happens for shortest-path distance refinement? [Bohang Zhang, Jingchu Gai, Yiheng Du, Qiwei Ye, Di He and Liwei Wang, 2024, Appendix B and Definition 3.1](https://arxiv.org/abs/2401.08514)

**Significance estimate.** 68/100. Characterizes all ordinary patterns for a published distance-based architecture and gives a counterexample to the broader existence conjecture. The conclusion also holds on connected hosts.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 21, 2026 found the following related results. Independent priority review is pending.

The forest characterization for ordinary message passing and its maximality are established results. Zhang and coauthors later characterized spectral invariant GNNs. The contribution here concerns shortest-path distance refinement and uses clique joins to transfer every nonforest obstruction.

[Read the proof (PDF)](shortest-path-homomorphisms.pdf) · [LaTeX source](shortest-path-homomorphisms.tex) · [BibTeX](citation.bib)

**Reproducible check.** Computes the distance profiles for both eight-vertex witnesses and compares the join formula with direct homomorphism enumeration on ten small examples. [Python script](verify.py)

## Sources

- [Bohang Zhang, Jingchu Gai, Yiheng Du, Qiwei Ye, Di He and Liwei Wang (2024), Appendix B and Definition 3.1](https://arxiv.org/abs/2401.08514)
- [Zhang et al., Rethinking the Expressive Power of GNNs via Graph Biconnectivity (2023)](https://arxiv.org/abs/2301.09505)
- [Neuen, Homomorphism-Distinguishing Closedness for Graphs of Bounded Tree-Width (2024)](https://arxiv.org/abs/2304.07011)
- [Homomorphism Expressivity of Spectral Invariant Graph Neural Networks (2025)](https://arxiv.org/abs/2503.00485)
