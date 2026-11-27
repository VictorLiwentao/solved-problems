# Deciding uniform closedness of sparse ReLU networks

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

A finite real-algebraic procedure decides uniform closedness on a cube at arbitrary depth. A missing limit can be chosen piecewise affine with real algebraic data.

**Original question.** Given the edge mask, can one decide whether the corresponding ReLU function class is closed? [Le, Riccietti and Gribonval, 2023, Section 3.3 and the cube model of Section 4](https://arxiv.org/abs/2306.02666)

**Scope and prior work.** The authors already decide the associated linear-product problem. Lindsey bounds the complexity of piecewise-affine limits. This argument supplies an explicit template for quantifying over continuous missing functions.

**Significance estimate.** 65/100. It answers the decision question for vector outputs and arbitrary fixed sparsity on the source domain. The template can be very large.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](relu-closedness-decision.pdf) · [LaTeX source](relu-closedness-decision.tex) · [BibTeX](citation.bib)

## Sources

- [Quoc-Tung Le, Elisa Riccietti and Rémi Gribonval (2023), Section 3.3 and the cube model of Section 4](https://arxiv.org/abs/2306.02666)
- [Kathryn A. Lindsey, The Geometry of Limits in ReLU Function Spaces](https://arxiv.org/abs/2610.33779)
- [James Renegar, The general decision problem for the first-order theory of the reals](https://doi.org/10.1016/S0747-7171(10)80004-5)
