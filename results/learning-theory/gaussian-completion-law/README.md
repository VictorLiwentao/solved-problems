# The Gaussian initialization law for depth-two diagonal completion

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

A normalized-row Gram formula gives the endpoint limit in arbitrary width under a nonvanishing condition. In width two it gives an explicit continuous law for positive determinant and two equiprobable atoms for negative determinant.

**Original question.** Which random completion does small Gaussian end-to-end initialization select, conditional on the sign of its determinant? [Treviño, 2026, Section 12.3, depth-two endpoint law](https://arxiv.org/abs/2610.05551)

**Scope and prior work.** Previous results describe several deterministic initialization families and nuclear-norm selection. The determinant-conditioned distribution requires a separate calculation.

**Significance estimate.** 55/100. It determines an explicitly requested probability law in a model of implicit bias. The higher-depth Gaussian basin problem remains open.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](gaussian-completion-law.pdf) · [LaTeX source](gaussian-completion-law.tex) · [BibTeX](citation.bib)

**Reproducible check.** A deterministic numerical check compares the exact finite-scale row solution with the limiting angular formula on both determinant components. [Python script](verify.py)

## Sources

- [Rodrigo Treviño (2026), Section 12.3, depth-two endpoint law](https://arxiv.org/abs/2610.05551)
- [Govind Menon, The geometry of the deep linear network](https://arxiv.org/abs/2411.09004)
- [Bai, Zhao and Zhang, Connectivity Shapes Implicit Regularization in Matrix Factorization Models](https://arxiv.org/abs/2405.13721)
- [Shin and Yun, Implicit Bias and Loss of Plasticity in Matrix Completion](https://arxiv.org/abs/2603.04703)
