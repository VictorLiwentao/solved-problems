# Nonattainment of robust population risk by continuous ReLU predictors

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Two ReLU units approach the exact minimum robust absolute loss. Every continuous predictor misses it, in every dimension and for a range of perturbation radii.

**Original question.** Must unregularized ReLU predictors attain the optimum in bounded-variation-type adversarial training? [Martinet and Bungert, 2026, Section 5, existence for the adversarial objectives of Lunk et al.](https://arxiv.org/abs/2611.09887)

**Scope and prior work.** Lunk et al. formulate the robust absolute-loss objective and its nonlocal variation form. Earlier work gives existence results for measurable decision sets. Here the distribution has a continuous positive density.

**Significance estimate.** 56/100. The obstruction applies at population level to continuous predictors of arbitrary capacity. It uses a particular loss and a simple threshold distribution.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](adversarial-risk-nonattainment.pdf) · [LaTeX source](adversarial-risk-nonattainment.tex) · [BibTeX](citation.bib)

**Reproducible check.** Checks the exact excess risk of 130 rational ramps. [Python script](verify.py)

## Sources

- [Eloi Martinet and Leon Bungert (2026), Section 5, existence for the adversarial objectives of Lunk et al.](https://arxiv.org/abs/2611.09887)
- [Lunk, Krasnopolsky, Garreau and Bungert, equations (3), (5) and (6)](https://arxiv.org/abs/2610.10666)
- [Bungert, García Trillos and Murray, The Geometry of Adversarial Training in Binary Classification](https://arxiv.org/abs/2111.13613)
