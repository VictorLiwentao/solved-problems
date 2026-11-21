# An exponential gap between activation rank and polynomial Jacobian rank

Wentao Li · Prepared with assistance from OpenAI Codex · November 20, 2026

Width-two ReLU networks with $L$ hidden layers have batches of activation rank $2^L$, while their polynomial Jacobians have at most $4L+1$ independent rows after accounting for rescaling symmetries.

**Original question.** Does the rank over the parameter-polynomial ring of the formal evaluation Jacobian bound the rank of the activation matrix? [J. Elisenda Grigsby and Kathryn Lindsey, 2024, Question 7.5 and Proposition 7.4](https://arxiv.org/abs/2410.17191)

**Significance estimate.** 64/100. Gives an exponential obstruction to a proposed comparison for an entire family of deep networks, and identifies the exact real-coefficient rank under the same path expansion.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 20, 2026 found the following related results. Independent priority review is pending.

The construction uses the classical iterated tent map. The new comparison uses a diagonal complete-path submatrix and distinguishes the two coefficient rings in the question. The separate conjecture about persistent pseudodimension remains open.

[Read the proof (PDF)](relu-activation-rank-gap.pdf) · [LaTeX source](relu-activation-rank-gap.tex) · [BibTeX](citation.bib)

**Reproducible check.** Verifies all 4,096 entries of the path minor at depth six and a smaller batch with fewer samples than parameters at depth five. [Python script](verify.py)

## Sources

- [J. Elisenda Grigsby and Kathryn Lindsey (2024), Question 7.5 and Proposition 7.4](https://arxiv.org/abs/2410.17191)
- [Telgarsky, Benefits of depth in neural networks](https://proceedings.mlr.press/v49/telgarsky16.html)
- [Verbockhaven, Rank and computation of the pathlifting Jacobian of a DAG ReLU network](https://arxiv.org/abs/2609.18682)
