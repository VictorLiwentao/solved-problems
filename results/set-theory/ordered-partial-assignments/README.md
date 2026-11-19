# Promise reductions and partial assignments without finite choice

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](ordered-partial-assignments.pdf) · [LaTeX source](ordered-partial-assignments.tex) · [Finite verification](verify.py) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L345-L351)

Bodor asked whether a general reduction between promise constraint problems requires choice for families of finite sets. The proposed proof establishes the compactness implication in pure ZF. It also proves the partial-assignment theorem used in the reduction on every infinite set of variables, including sets that admit no linear ordering. [Question 6.4, Theorems 5.4 and 5.13](https://arxiv.org/abs/2604.08365)

## How the proof removes choice

A query asks about a finite subset of variables. Keep every possible ordering of that subset as a separate presentation. Each presentation now has a first admissible assignment or list, using lexicographic order. A larger query accommodates witnesses for every ordered presentation of each smaller query it contains. There are only finitely many, and their orders may be chosen independently. The induction never needs an ordering of all variables or a simultaneous choice of witnesses across infinitely many queries.

For the reduction itself, take all strict solutions on each finite subset and use restriction to identify their evaluations across overlapping tests. A weak solution produces lists of partial weak solutions. A chain condition on operations guarantees that two lists agree somewhere along each nested chain. The partial-assignment theorem then yields a single global weak solution. [Earlier finite reduction of Barto and Kozik](https://doi.org/10.1137/1.9781611977073.50)

## What the exact definitions require

The published exact-query-size formulation needs the variable set to be large enough for its largest query. On a smaller set, consistency can be vacuous. The draft gives a two-point example and a triangle covering every possible pair of query sizes.

The published definition of an all-input reduction also has an exception when empty relations are allowed. If the output template accepts every input and the input template can reject one, no reduction can preserve rejection. The manuscript proves this is the only exception in the nonempty-domain setting under the stated weak-minion hypothesis. The compactness implication holds across this case as well.

## Verification and priority

The checker exhausts all 421,875 ordered singleton-list systems at the three-point base case and verifies the boundary constructions. The five-page proof handles the induction and arbitrary variable sets. The source search located the finite result and Bodor’s proof with finite choice. Independent proof and priority review and Lean formalization are pending. [Finite partial-assignment and promise-CSP framework](https://doi.org/10.1145/3457606)
