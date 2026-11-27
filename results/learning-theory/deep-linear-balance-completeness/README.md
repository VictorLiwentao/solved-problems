# Which conservation laws survive in deep linear networks?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Additional local laws exist with scalar input and output and wide hidden layers. For square layers of any width and depth, the balance matrices generate every smooth local law at generic weights.

**Original question.** Can local conservation laws beyond adjacent Gram balances exist at depth greater than two? [Marcotte, Gribonval and Peyré, 2023, Section 4, following Proposition 4.1 (NeurIPS 2023)](https://arxiv.org/abs/2307.00144)

**Scope and prior work.** The original paper proves the two-factor result. The ICLR follow-up establishes deep ReLU path-lifting completeness and describes special linear initialization conditions. The extra conservation laws constructed here are local.

**Significance estimate.** 67/100. It settles the universal completeness suggestion negatively and proves an arbitrary-depth positive theorem for square networks. Other rectangular architectures remain to be classified.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](deep-linear-balance-completeness.pdf) · [LaTeX source](deep-linear-balance-completeness.tex) · [BibTeX](citation.bib)

## Sources

- [Sibylle Marcotte, Rémi Gribonval and Gabriel Peyré (2023), Section 4, following Proposition 4.1 (NeurIPS 2023)](https://arxiv.org/abs/2307.00144)
- [Marcotte, Peyré and Gribonval, Intrinsic training dynamics of deep neural networks](https://arxiv.org/abs/2508.07370)
- [Marcotte, Gribonval and Peyré, Conservation laws for ResNets and Transformers](https://proceedings.mlr.press/v267/marcotte25a.html)
