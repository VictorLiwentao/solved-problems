# Monadic second-order convergence for caterpillar forests

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](mso-caterpillar-forests.pdf) · [LaTeX](mso-caterpillar-forests.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/finite-model-theory/mso-caterpillar-forests/citation.bib)

Every monadic second-order sentence has a limiting probability in a uniform labelled forest of caterpillars. A component-count criterion extends the result to smooth definable forest classes within bounded distance of paths.

**Original question.** Peter Heinig, Tobias Müller, Marc Noy and Anusch Taraz, 2014. [§6, the caterpillar-forest prediction immediately before Conjecture 6.3](https://arxiv.org/abs/1401.7021)

## Argument

Trimming leaves recovers a canonical path decorated by bounded-height rooted trees. A finite automaton tracks a logical type along the path. The resulting generating functions distinguish the component counts that converge to Poisson laws from those that grow without bound.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. An exhaustive Prüfer-code check tests the core decomposition on 18,249 labelled trees and recovers the exact caterpillar counts through seven vertices. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The original authors proved the first-order caterpillar law, the monadic second-order path-forest law and the component composition lemmas. The draft verifies their proposed component-count approach for caterpillars and bounded-height decorations.

**Significance · 62/100.** Strengthens the known first-order law to monadic second-order logic and gives a general analytic criterion. The conjecture for all smooth decomposable minor-closed classes remains open here. [Scoring benchmark](../../../docs/scores-and-sources.md)
