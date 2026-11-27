# Infinite quotient fibers in width-one ReLU chains

Wentao Li · Prepared with assistance from OpenAI Codex · November 21, 2026

Every realized function in a chain of at least three scalar hidden layers has uncountably many inequivalent parameterizations, resolving both clauses of Conjecture 1.

**Original question.** Can a width-one architecture have no identifiable parameters, and does every architecture nevertheless have a finitely identifiable parameter? [Moritz Grillo and Guido Montúfar, 2026, Conjecture 1, both clauses](https://arxiv.org/abs/2605.03601)

**Significance estimate.** 54/100. Settles both clauses about quotient fibers, including exceptional parameters. The classification of the scalar functions themselves is prior work, and the obstruction uses a narrow architecture.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 21, 2026 found the following related results. Independent priority review is pending.

Grigsby, Lindsey, Meyerhoff and Wu had already classified scalar-chain shapes and bounded their functional dimension. The output-bias construction here covers every fiber, including constant functions.

[Read the proof (PDF)](width-one-quotient-fibers.pdf) · [LaTeX source](width-one-quotient-fibers.tex) · [BibTeX](citation.bib)

**Reproducible check.** Checks representatives of the constant, ray and clipped shapes at three depths with rational inputs and distinct output biases. [Python script](verify.py)

## Sources

- [Moritz Grillo and Guido Montúfar (2026), Conjecture 1, both clauses](https://arxiv.org/abs/2605.03601)
- [Grigsby, Lindsey, Meyerhoff and Wu, Functional dimension of feedforward ReLU neural networks, Section 9.1](https://arxiv.org/abs/2209.04036)
