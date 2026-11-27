# Nonlinearity of a cyclic weightwise quadratic Boolean function

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](cyclic-quadratic-nonlinearity.pdf) · [LaTeX](cyclic-quadratic-nonlinearity.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/cyclic-quadratic-nonlinearity/citation.bib)

The proposed nonlinearity formula for u fails at every multiple of four from 24 onward. An explicit Walsh coefficient gives a gap of at least 16ℓ − 88 in dimension 4ℓ, and the maximum Walsh magnitude has exponential growth rate 3/4 on a base-two logarithmic scale per variable.

**Original question.** Pierrick Méaux and Yassine Ozaim, 2023. [§6.3, the formula for the family u in dimensions divisible by four](https://eprint.iacr.org/2023/1680)

## Argument

Use a mask that repeats 0110 in the interior and has four zero bits at each end. Four generating polynomials give the periodic part of its Walsh coefficient. The seven boundary slices contribute 32ℓ − 176 to that coefficient. At 24 variables the predicted nonlinearity is 8,321,024 and the witness gives at most 8,321,016.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The check evaluates slice polynomials through 160 variables and compares them with direct truth-table sums at 12, 16 and 20 variables. [Run the check](verify.py)

**Priority.** Independent priority review is pending. Méaux and Ozaim formulated the prediction after computations through 16 variables. Méaux, Seuré and Tang later used generating functions for related quadratic functions and listed u through 16 variables in Table 5. [Journal article](https://doi.org/10.1016/j.dam.2024.04.008) · [Later comparison](https://eprint.iacr.org/2024/2022)

**Significance · 64/100.** Disproves an exact spectral prediction across the entire tail of the proposed family and determines its exponential rate. The exact nonlinearity in general remains open here. [Scoring benchmark](../../../docs/scores-and-sources.md)
