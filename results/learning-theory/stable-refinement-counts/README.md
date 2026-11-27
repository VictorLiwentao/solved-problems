# Stable graph refinement without a homomorphism-count characterization

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

A local update that caps neighbor counts has no such characterization, even on connected graphs. A second counterexample retains all neighbor multiplicities after local triangle initialization.

**Original question.** Does stable local color refinement guarantee expressibility by a family of ordinary graph homomorphism counts? [Zhang et al., 2024, Appendices B and F.1](https://proceedings.iclr.cc/paper_files/paper/2024/hash/ec702dd6e83b2113a43614685a7e2ac6-Abstract-Conference.html)

**Scope and prior work.** The source already gave a graph-level exception and separately conjectured stable refinement would suffice. The first construction uses only messages from neighbors. The second uses a classical homomorphism closure theorem.

**Significance estimate.** 64/100. It refutes a general criterion in GNN expressivity using a local update. Existing positive results for standard 1-WL and its characterized relatives still apply.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](stable-refinement-counts.pdf) · [LaTeX source](stable-refinement-counts.tex) · [BibTeX](citation.bib)

## Sources

- [Bohang Zhang, Jingchu Gai, Yiheng Du, Qiwei Ye, Di He and Liwei Wang (2024), Appendices B and F.1](https://proceedings.iclr.cc/paper_files/paper/2024/hash/ec702dd6e83b2113a43614685a7e2ac6-Abstract-Conference.html)
- [Daniel Neuen, Homomorphism-Distinguishing Closedness for Graphs of Bounded Tree-Width](https://arxiv.org/abs/2304.07011)
- [Jesse Comer, related homomorphism profiles for modal languages](https://arxiv.org/abs/2404.15421)
