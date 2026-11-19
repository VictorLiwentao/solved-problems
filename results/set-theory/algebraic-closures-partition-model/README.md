# Which fields have algebraic closures in the finite partition model?

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](algebraic-closures-partition-model.pdf) · [LaTeX source](algebraic-closures-partition-model.tex) · [Research catalogue](../../../README.md)

A field in Bruce’s model has an algebraic closure exactly when its underlying set is well-orderable. Any two closures are isomorphic over the base field.

**Original question.** Amitayu Banerjee, 2021, algebraic-closure part (Form 233) of Question 8.1 in v1, later Question 7.1. [Primary source](https://arxiv.org/abs/2109.05914v1)

## Argument

Choose one square root of minus one in a closure. Every permutation of square one that preserves the field operations and fixes that root acts trivially on the whole field. Such permutations generate a partition stabilizer, so an ambient well-order of the field is available inside the model.

## Proof and priority

The PDF gives the full argument. Independent mathematical review and Lean formalization are pending.

Pincus proved the involution lemma and obtained uniqueness in the basic Fraenkel model. Banerjee applies the lemma in another permutation model. The new application checks generation by involutions for Bruce’s supports and gives the existence equivalence. [Banerjee, Lemma 3.2 and Question 7.1](https://arxiv.org/abs/2109.05914v4)

A search through November 19, 2026 found no earlier resolution of the specific assertion claimed here. Priority awaits independent confirmation.

**Significance estimate: 48/100.** Answers the uniqueness question and identifies exactly when a closure exists in this model. The principal field-theoretic ingredient is classical. The 100-point benchmark is a full resolution of three-dimensional Navier–Stokes existence and smoothness.
