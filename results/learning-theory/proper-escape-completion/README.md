# Unbounded deep linear completion trajectories escape in norm

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Every unbounded trajectory eventually leaves every bounded set. The result holds in all widths in the original finite-temperature model, so almost every full-rank initialization escapes in norm.

**Original question.** Does the norm tend to infinity for almost every initialization, as opposed to having unbounded excursions? [Treviño, 2026, Section 12.4, question 1](https://arxiv.org/abs/2610.05551)

**Scope and prior work.** Treviño already proves almost-everywhere unboundedness at depth greater than two. The proof lifts the flow to an analytic factor potential that extends across one rank loss.

**Significance estimate.** 57/100. It rules out recurrent returns even near the singular boundary and strengthens a recent almost-everywhere theorem. It concerns one matrix sensing model.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](proper-escape-completion.pdf) · [LaTeX source](proper-escape-completion.tex) · [BibTeX](citation.bib)

## Sources

- [Rodrigo Treviño (2026), Section 12.4, question 1](https://arxiv.org/abs/2610.05551)
- [Govind Menon, The geometry of the deep linear network](https://arxiv.org/abs/2411.09004)
- [Menon and Yu, An entropy formula for the deep linear network](https://arxiv.org/abs/2509.09088)
