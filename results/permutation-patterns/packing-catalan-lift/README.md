# Catalan representatives for permutation packings

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](packing-catalan-lift.pdf) · [LaTeX source](packing-catalan-lift.tex) · [Result catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/permutation-patterns/packing-catalan-lift/citation.bib)

## Original question

Can count-preserving operations on patterns explain Catalan representatives over the requested overlaps and lengths? [Blitvić, Kammoun, and Steingrímsson, §7, item 6](https://arxiv.org/html/2610.29846v1#S7)

## Result

For every overlap $m\geq3$ and pattern length $K\geq2m$, the construction realizes the Catalan numbers as the packing counts. It answers the Catalan part of item 6. The double-factorial part has a separate solution. [Nagy’s construction](https://arxiv.org/abs/2611.06937)

The lift adds positions that must form an initial chain in every linear extension. Removing that chain recovers the original packing poset, so its count is preserved in every number of windows.

## Verification

The [verifier](verify.py) compares all order relations in 4,356 examples of the lift.

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review.

## Lean formalization

For every admissible seed and number of windows, the lifted packing order is the ordinal sum of a fresh chain and the original packing order. Inserting the chain induces a bijection of the packing permutations. The general lift theorem and bijection are complete. The separate closed-form Catalan count for the 1324 seed remains outside this verification. The comparator checks `PackingLift.ordinalSum` and `PackingLift.preservesCounts`. [Lean proof](../../../lean/SolvedProblems/PackingLift.lean) · [Reference statements](../../../lean/Challenge.lean)
