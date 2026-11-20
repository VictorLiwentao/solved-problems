# Private generation without a public witness bound

Wentao Li · Prepared with assistance from OpenAI Codex

For finite families, an infinite common intersection characterizes exponential private generation. For countable families a local condition on finite lists of strings is necessary and sufficient.

For a finite family, the proof changes the sampling distribution one language at a time while preserving all earlier exponential error bounds. For a countable family, it characterizes success by finite multisets of words that work across nearby distributions in total variation.

**Original question.** Xiaoyu Li, Andi Han, Jiaojiao Jiang and Junbin Gao (2026), Appendix H.1, question 1. [Primary source](https://arxiv.org/abs/2604.07238v2)

**Significance estimate: 62/100.** Extends a two-language obstruction to an exact finite-family classification and gives a geometric test for countable families.

**Proof status.** Written research draft awaiting independent review. **Priority status.** A targeted literature check found the original question and related work. Priority awaits independent review.

[Read the proof (PDF)](private-generation-without-witness-bound.pdf) · [LaTeX source](private-generation-without-witness-bound.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/private-generation-without-witness-bound/citation.bib)

## Lean formalization

A finite nonempty family of infinite languages admits pure-private generation with exponentially decreasing error on every admissible law exactly when the languages have infinite common intersection. This is the finite-family theorem. The local criterion for countably infinite families is separate. [Lean statement](../../../lean/Statements/PrivateWitness.lean) · [Proof](../../../lean/SolvedProblems/PrivateWitness.lean) · [Comparator and source alignment](../../../lean/submissions/private-generation-without-witness-bound/)
