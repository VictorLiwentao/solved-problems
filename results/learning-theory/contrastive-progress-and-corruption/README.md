# Identifying a cut when honest progress outpaces corruption

Wentao Li · Prepared with assistance from OpenAI Codex

A countable class of at least two infinite supports permits identification under diverging honest progress minus corruption exactly when its holes are finite and pairwise disjoint.

The learner adds the size of each candidate’s hole to its violation count. When the criterion fails, two distinct targets admit a single stream of pairs on which both make more and more honest progress beyond their corruption counts.

**Original question.** Xiaoyu Li, Andi Han, Jiaojiao Jiang and Junbin Gao (2026), §8(iii) and Proposition 7.11. [Primary source](https://arxiv.org/abs/2605.06211v2)

**Significance estimate: 54/100.** Gives a matching obstruction and removes the previous uniform bound on hole sizes.

**Proof status.** Written research draft awaiting independent review. **Priority status.** A targeted literature check found the original question and related work. Priority awaits independent review.

[Read the proof (PDF)](contrastive-progress-and-corruption.pdf) · [LaTeX source](contrastive-progress-and-corruption.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/contrastive-progress-and-corruption/citation.bib)

## Lean formalization

Under the divergent honest-progress surplus promise, a countable family of at least two distinct infinite proper supports is identifiable exactly when the holes are finite and pairwise disjoint. The indexed theorem counts each distinct honest positive once and each corrupt observation with multiplicity. The necessity proof constructs one honestly covering stream for two rival targets. The comparator checks `Progress.indexedCriterion`. [Lean proof](../../../lean/SolvedProblems/Progress.lean) · [Reference statements](../../../lean/Challenge.lean)
