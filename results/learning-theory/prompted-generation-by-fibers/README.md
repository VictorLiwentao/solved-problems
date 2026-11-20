# Prompted language generation by label fibers

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](prompted-generation-by-fibers.pdf) · [LaTeX source](prompted-generation-by-fibers.tex) · [Research catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/prompted-generation-by-fibers/citation.bib)

A separate finite-witness condition for each label characterizes prompted generation. Every countable class works even for infinitely many prompts.

**Original question.** Jiaxun Li, Vinod Raman and Ambuj Tewari, 2024, Questions 6.4–6.5, published as Questions 51–52 at COLT 2025. [Primary source](https://arxiv.org/abs/2410.13714v5)

## Argument

When a label is requested, run its ordinary generator on the examples observed with that label. The definition allows a different convergence time for each requested label. Feeding a prompted generator examples and requests with a single fixed label proves the converse.

## Proof and priority

The PDF gives the full argument. Independent review is pending.

The COLT paper proves the countable-class statement for a finite label set. Kleinberg and Mullainathan supply the ordinary countable-family theorem and study a different prefix-completion model. Xiaoyu Li and coauthors supply the ordinary finite-witness characterization. A public Lean development of the countable prompted result still assumes finitely many labels. [COLT statement](https://proceedings.mlr.press/v291/raman25a.html) · [Countable families](https://arxiv.org/abs/2404.06757) · [Finite witnesses](https://arxiv.org/abs/2609.10525) · [Earlier Lean theorem](https://github.com/pengzhang91/generation-in-the-limit-lib/blob/a980574282c6063d437b311dd3b52dfe95bb2ac1/GenLimitLean/GenLimit/Paper02_LearningTheory/PromptedNonuniform.lean#L354-L361)

A search of the primary literature and follow-up work through November 19, 2026 did not identify an earlier resolution of this specific question. Priority awaits independent confirmation.

**Significance estimate: 42/100.** One short reduction answers two explicitly posed questions. Prior theorems supply the ordinary countable-class and finite-witness ingredients. A full resolution of the three-dimensional Navier–Stokes existence and smoothness problem sets the benchmark at 100.

## Lean formalization

Lean proves the fiber reduction in both directions and the countable-class conclusion for arbitrary prompt alphabets. The arbitrary-class finite-witness characterization remains to be formalized. [Lean proof](../../../lean/SolvedProblems/PromptGeneration.lean) · [Comparator checks](../../../lean/README.md)
