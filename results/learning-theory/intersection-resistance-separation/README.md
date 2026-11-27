# Intersection signatures and effective resistance are incomparable

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Cones over one cycle and over two shorter cycles have matching full-radius intersection signatures through every refinement round. Their effective resistances separate them in one round.

**Original question.** Can resistance-distance refinement distinguish a pair missed by every radius of the GIST neighborhood-intersection encoding? [H. A. D. Le et al., 2025, Appendix C, following Theorem C.1(2)](https://openreview.net/forum?id=CyXPiK5JLy)

**Scope and prior work.** The GIST authors supplied the reverse direction. The proof compares theoretical node-pair encodings and graph refinement with no learned parameters.

**Significance estimate.** 60/100. It establishes the missing direction of an explicit expressivity comparison by an infinite construction. The question concerns one structural encoding.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](intersection-resistance-separation.pdf) · [LaTeX source](intersection-resistance-separation.tex) · [BibTeX](citation.bib)

**Reproducible check.** Full two-root distance tables agree and the traces of rational grounded inverses differ on three graph pairs. [Python script](verify.py)

## Sources

- [Hoang Anh Duy Le, Shaochen Zhong, Jerry Xiao, Jiamu Zhang, Yu-Neng Chuang, Li Li, Rui Chen, Shuai Xu, Zirui Liu, Kaixiong Zhou, Ning Xie, Vipin Chaudhary, Xia Hu and Zhaozhuo Xu (2025), Appendix C, following Theorem C.1(2)](https://openreview.net/forum?id=CyXPiK5JLy)
- [Le et al., original conjecture in Appendix C](https://openreview.net/pdf/4f1ece2425a5229a909606118c9c0b881326687c.pdf)
- [Black, Wan, Mishne, Nayyeri and Wang, Comparing Graph Transformers via Positional Encodings (ICML 2024)](https://proceedings.mlr.press/v235/black24b.html)
