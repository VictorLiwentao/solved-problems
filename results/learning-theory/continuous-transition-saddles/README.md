# Continuous onset can coexist with other stationary attention states

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

A smooth positive-semidefinite kernel on the circle has a continuous transition and a nonuniform stationary density strictly inside the conjectured uniqueness interval.

**Original question.** For a centered symmetric zonal kernel, does a continuous transition force uniformity to be the only critical point between half the critical coupling and the critical coupling? [Mun and Rosenzweig, 2026, Remark 2.4](https://arxiv.org/abs/2606.05140)

**Scope and prior work.** The construction uses the general kernel assumptions of Section 2. The transition of global minimizers is continuous while an auxiliary harmonic branch supplies a different stationary density.

**Significance estimate.** 58/100. It disproves the general critical-point uniqueness conjecture with a three-frequency kernel. Uniqueness for the single exponential attention kernel is still open.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](continuous-transition-saddles.pdf) · [LaTeX source](continuous-transition-saddles.tex) · [BibTeX](citation.bib)

**Reproducible check.** Exact Fourier-polynomial arithmetic checks the sign of the auxiliary fourth-order coefficient. [Python script](verify.py)

## Sources

- [Kyunghoo Mun and Matthew Rosenzweig (2026), Remark 2.4](https://arxiv.org/abs/2606.05140)
- [Balasubramanian, Banerjee and Rigollet, stationary solutions for noisy transformers](https://arxiv.org/abs/2510.20094)
