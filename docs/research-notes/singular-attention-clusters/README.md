# Cluster residence times for sampled attention with singular score matrices

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Score-separated clouds cluster for exponentially many layers under sampled attention of arbitrary rank. When scores are constant within each pair of groups, the first cross-group sampling time has an exact geometric law.

**Original question.** Can one prove clustering and long residence times when attention scores ignore some token coordinates? [Alcalde, Geshkovski and Ruiz-Balet, 2025, Section 5, singular key–query matrices, first posted 2025 and published at ICML 2026](https://arxiv.org/abs/2508.09628)

**Scope and prior work.** The original work proves clustering and metastability with positive-definite score geometry. Here the process is a single head with independent sampling. The first sampled interaction can precede geometric escape.

**Significance estimate.** 57/100. The argument allows singular and nonsymmetric score matrices and gives an exact escape-clock prefactor for the first sampled cross-group interaction. The assumptions restrict the clouds and update rule.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](singular-attention-clusters.pdf) · [LaTeX source](singular-attention-clusters.tex)

**Reproducible check.** Enumerates a full three-token layer with exact probabilities and checks contraction of the invisible coordinates. [Python script](verify.py)

## Sources

- [Albert Alcalde, Borjan Geshkovski and Domènec Ruiz-Balet (2025), Section 5, singular key–query matrices, first posted 2025 and published at ICML 2026](https://arxiv.org/abs/2508.09628)
- [Alcalde, Geshkovski and Ruiz-Balet, ICML conference version](https://proceedings.mlr.press/v306/alcalde26a.html)
