# Which language collections attain Pareto-optimal generation times?

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](pareto-generation-orders.pdf) · [LaTeX](pareto-generation-orders.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/pareto-generation-orders/citation.bib)

A well-order test characterizes exactly which countable collections attain Pareto-optimal generation times and recovers every attainable optimal profile in the unrestricted model.

**Original question.** Moses Charikar and Chirag Pabbaraju, 2025. [Introduction and §§3.3–3.4](https://arxiv.org/abs/2510.02795)

## Argument

Process the languages in a chosen order, giving each the earliest deadline compatible with its predecessors. At a limit, check their joint intersection for a fresh word. Conversely, in an optimal profile each deadline above one has a finite sample that prevents lowering it. Sorting by deadline recovers the profile. A second construction realizes arbitrary countable Sperner hypergraphs as deadline constraints.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. On 64 classes with infinite private tails, the program compares all greedy orders with every coordinatewise minimal feasible deadline vector. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The original paper gives a sufficient condition and examples of nonattainment. GenLimitLib formalizes earlier results from that paper. The theorem here concerns unrestricted generation rules and gives no decision procedure for an effective presentation. [ALT paper](https://proceedings.mlr.press/v313/charikar26a.html) · [GenLimitLib](https://github.com/pengzhang91/generation-in-the-limit-lib)

**Significance · 63/100.** Gives a necessary and sufficient condition for the entire collection, including failures first visible at an infinite limit. The criterion is information-theoretic. [Scoring benchmark](../../../docs/scores-and-sources.md)
