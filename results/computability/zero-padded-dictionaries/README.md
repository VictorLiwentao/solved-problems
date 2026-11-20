# Which dictionaries hit all sufficiently zero-padded binary words?

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](zero-padded-dictionaries.pdf) · [LaTeX](zero-padded-dictionaries.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/computability/zero-padded-dictionaries/citation.bib)

A bounded-zero-run subdictionary criterion characterizes padded unavoidability. Recognition is decidable for regular dictionaries, Σ⁰₂-complete for primitive recursive indices and Σ⁰₃-complete for enumerable indices.

**Original question.** Bogdan Alecu, Maria Chudnovsky, Sepehr Hajebi and Sophie Spirkl, 2023. [Question 1.11 in v1, later Question 8.3](https://arxiv.org/abs/2311.05066)

## Argument

Split a positive word at long zero gaps. Each remaining group of ones supplies a canonical test word. For the lower bounds a fixed set of forbidden words forces just one run of ones, whose length encodes a computation. The smallest sufficient padding records whether the computation has bounded output.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The program tests the zero-run truncation and the automaton bound on 470 explicitly given dictionaries. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The original paper tests finite dictionaries and exhibits an infinite minimal example. The note gives the regular-language algorithm and both hardness reductions. [Original paper, §8](https://arxiv.org/abs/2311.05066) · [Finite and cofinite index sets](https://math.berkeley.edu/~marks/notes/computability_notes_v1.pdf)

**Significance · 54/100.** Gives a criterion for arbitrary dictionaries and sharp decision complexity for two infinite input models. The original authors already handled finite dictionaries. [Scoring benchmark](../../../docs/scores-and-sources.md)
