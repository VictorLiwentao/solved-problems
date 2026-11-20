# Exact oracle bounds for memoryless language generation

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](memoryless-generation-jumps.pdf) · [LaTeX](memoryless-generation-jumps.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/computability/memoryless-generation-jumps/citation.bib)

When examples may repeat arbitrarily, the exact universal oracle for memoryless set-valued generation is the first Turing jump for decidable presentations and the second for enumerable ones. The thresholds hold for every fixed sliding window.

**Original question.** Jon Kleinberg, Anay Mehrotra, Amin Saberi and Grigoris Velegkas, 2026. [§6, oracle-access question, applied to Theorem 3.1](https://arxiv.org/abs/2605.30324)

## Argument

An input repeated indefinitely forces every output into the intersection of all compatible languages. The appropriate jump decides this intersection. To show necessity, encode settled initial segments of a halting set so that even an infinite subset of the answers on one marker computes the entire jump.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending.

**Priority.** Independent priority review is pending. The abstract intersection criterion and finite-exception argument are due to the original authors. The degree bounds depend on representing an infinite output by an enumeration. [Computability background](https://math.berkeley.edu/~marks/notes/computability_notes_v1.pdf)

**Significance · 55/100.** Gives matching oracle upper and lower bounds for two effective representations and every fixed window. It resolves the arbitrary-repetition version of a broader access question. [Scoring benchmark](../../../docs/scores-and-sources.md)
