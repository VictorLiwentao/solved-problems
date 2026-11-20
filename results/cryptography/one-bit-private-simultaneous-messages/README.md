# Private simultaneous messages with one bit of evaluator memory

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](one-bit-private-simultaneous-messages.pdf) · [LaTeX](one-bit-private-simultaneous-messages.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/one-bit-private-simultaneous-messages/citation.bib)

A Boolean output admits exact, perfectly private simultaneous messages with a one-bit evaluator precisely when fixing one designated party’s input makes every slice an XOR of single-party functions. For three or more single-bit senders, the only symmetric examples are parity, its complement and the two constants.

**Original question.** Akinori Kawachi and Yuto Nishikubo, 2025. [§1.3, the classical one-bit evaluator comparison in the input-controlled gate model of §2.1](https://doi.org/10.1587/transfun.2024DMP0017)

## Argument

Consider the last gate at which a message can reset the evaluator. Privacy forces the same reset to be possible at every input of its sender unless that sender already determines the output. After a reset, only identity and bit flips remain. Conversely, a random cyclic shift hides which input slice was selected, and fresh masks hide every intermediate state.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The exact transcript check compares the construction and the output-only simulator on every three-bit predicate admitted by the theorem, and on an example with a three-valued sender. [Run the check](verify.py)

**Priority.** Independent priority review is pending. Maslov and coauthors analyzed one-bit computation on unencoded inputs. Their bounds already supply examples through coin fixing. The privacy-dependent necessity and matching protocol address a different question. [Limited-space computation](https://doi.org/10.1038/s41567-021-01271-7) · [Communication bounds for unrestricted evaluators](https://arxiv.org/abs/2610.21216)

**Significance · 67/100.** Classifies every Boolean output for arbitrary finite sender alphabets in this model and gives matching protocols. The one-bit, fixed-access evaluator and perfect security are substantial restrictions. [Scoring benchmark](../../../docs/scores-and-sources.md)
