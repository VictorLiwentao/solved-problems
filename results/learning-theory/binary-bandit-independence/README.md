# Binary bandit learnability and the continuum hypothesis

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](binary-bandit-independence.pdf) · [LaTeX](binary-bandit-independence.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/binary-bandit-independence/citation.bib)

For an explicit class of binary rewards with open winning sets, learnability is equivalent over ZFC to the failure of the continuum hypothesis.

**Original question.** Steve Hanneke and Liu Yang, 2023. [§7, decidability of binary bandit learnability](https://proceedings.mlr.press/v195/hanneke23d.html)

## Argument

The losing arms form a closed subset of the unit interval of size at most ℵ₁. If the continuum is larger, the perfect-set theorem makes every such set countable, so a uniform draw wins almost surely. Under the continuum hypothesis, every nonempty open interval can be the entire winning set. A bounded learner misses one with high probability. A second example characterizes the existence of a diffuse probability measure on all subsets of the interval.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending.

**Priority.** Independent priority review is pending. Hanneke and Yang proved independence for real-valued rewards and a hitting-measure criterion for binary rewards. The note applies classical set theory to two binary classes. Hanneke and Wang addressed the separate noisy-bandit question. [ALT 2025 paper](https://proceedings.mlr.press/v272/hanneke25c.html)

**Significance · 72/100.** Answers an explicit question at the intersection of learning theory and set theory. The first example needs only ordinary relative consistency, and its class definition uses a cardinality condition. [Scoring benchmark](../../../docs/scores-and-sources.md)
