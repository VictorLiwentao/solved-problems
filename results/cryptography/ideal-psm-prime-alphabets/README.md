# Classifying ideal private simultaneous messages on prime alphabets

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](ideal-psm-prime-alphabets.pdf) · [LaTeX](ideal-psm-prime-alphabets.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/ideal-psm-prime-alphabets/citation.bib)

Gives the complete list and exact count of connected nondegenerate ideal PSM functions for every prime alphabet. The functions come from affine differences, point–hyperplane incidence in projective spaces, and one exceptional table on eleven symbols. For arbitrary finite alphabet size, a Latin square admits ideal PSM exactly when it is a relabelled group table.

**Original question.** Keitaro Hiwatashi and Reo Eriguchi, 2025. [§5.2, tightness of the prime-alphabet bound in Theorem 8 (ITCS 2026)](https://eprint.iacr.org/2025/2217)

## Argument

Perfect privacy identifies output values with orbits of simultaneous permutations. Two faithful actions of the same prime-degree group either give affine difference classes, or have a doubly transitive simple subgroup. Pairs of inequivalent actions of that subgroup yield the incidence and exceptional tables.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The check compares the formula with both published small-domain enumeration tables and constructs the two distinct incidence sizes at 31. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The conference authors gave the orbit theorem and enumerated small alphabets. Guralnick classified the group actions underlying the general count. The tightness question for arbitrary composite sizes remains open here. [ITCS paper](https://doi.org/10.4230/LIPIcs.ITCS.2026.76) · [Group-theory source](https://doi.org/10.1016/0021-8693(83)90190-4)

**Significance · 64/100.** Replaces a quasipolynomial upper bound by an exact count and identifies every function it counts. The result uses the published orbit characterization and the classification of finite simple groups. [Scoring benchmark](../../../docs/scores-and-sources.md)
