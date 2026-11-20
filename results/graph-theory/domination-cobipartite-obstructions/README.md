# Minimal domination in hereditary classes of incomparability graphs

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](domination-cobipartite-obstructions.pdf) · [LaTeX](domination-cobipartite-obstructions.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/graph-theory/domination-cobipartite-obstructions/citation.bib)

Forbidding any fixed induced co-bipartite graph gives an incremental-polynomial algorithm for minimal domination in incomparability graphs. Under ETH this exactly characterizes the tractable hereditary subclasses.

**Original question.** Marthe Bonamy, Oscar Defrain, Piotr Micek and Lhouari Nourine, 2020. [§7, Conjecture 7.3](https://arxiv.org/abs/2004.07214v1)

## Argument

A shattered set in a partially ordered set has no chain of length three. A large antichain inside it provides both cliques of an induced forbidden graph by encoding cross-neighbourhoods. For clique sizes a ≤ b the worst-case VC dimension has order a + log(b+1). Mary's algorithm then enumerates the minimal dominating sets.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. A finite check exhausts the shattering and trace-nesting steps on 5,231 naturally labelled posets. [Run the check](verify.py)

**Priority.** Independent priority review is pending. Lozin's hereditary characterization and Mary's bounded-VC algorithm already imply the qualitative upper bound. The draft gives a direct dimension bound and matching-order examples. Kanté and colleagues supply the reduction on co-bipartite graphs. [Mary](https://arxiv.org/abs/2407.00694) · [ETH lower bound](https://arxiv.org/abs/2610.11473) · [2026 journal version of the question](https://doi.org/10.1016/j.disc.2025.114904)

**Significance · 72/100.** Resolves the full forbidden-graph conjecture and gives a conditional classification. The sharp worst-case VC bound is new to this argument. The qualitative algorithm also follows by combining earlier theorems. [Scoring benchmark](../../../docs/scores-and-sources.md)
