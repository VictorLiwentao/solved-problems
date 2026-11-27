# When does an overwide matrix factorization have intrinsic training dynamics?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

A single matrix rank test decides whether training from a fixed initialization admits a product-dependent gradient metric. Failure can already be witnessed with smooth autonomous losses.

**Original question.** For hidden width larger than both matrix dimensions, which full-row-rank initializations admit one local product dynamics for every loss? [Marcotte, Peyré and Gribonval, 2025, following Theorem 3.9 (ICLR 2026)](https://arxiv.org/abs/2508.07370)

**Scope and prior work.** The source treats narrower factorizations and the scalar-output scalar-input exception. The theorem covers smooth loss flows and finite concatenations of ordinary gradient arcs. It makes no convention for arbitrary motion along a nondifferentiability set.

**Significance estimate.** 68/100. It gives an exact and computable answer in the overwide regime, including exceptional initializations. The model has two linear factors.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](overwide-intrinsic-dynamics.pdf) · [LaTeX source](overwide-intrinsic-dynamics.tex) · [BibTeX](citation.bib)

**Reproducible check.** Exact rational rank calculations test isotropic, anisotropic and scalar cases and a change of frame. [Python script](verify.py)

## Sources

- [Sibylle Marcotte, Gabriel Peyré and Rémi Gribonval (2025), following Theorem 3.9 (ICLR 2026)](https://arxiv.org/abs/2508.07370)
- [Marcotte, Gribonval and Peyré, Abide by the Law and Follow the Flow](https://arxiv.org/abs/2307.00144)
- [Gabriel Peyré, Training dynamics and matrix factorization, November 2026](https://www.gpeyre.com/blog/2026/11/12/intrinsic-factor-training-dynamics/)
