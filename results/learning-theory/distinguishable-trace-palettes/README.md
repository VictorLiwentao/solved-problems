# No fixed palette distinguishes all comparable languages by prefix traces

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](distinguishable-trace-palettes.pdf) · [LaTeX](distinguishable-trace-palettes.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/distinguishable-trace-palettes/citation.bib)

The strong trace condition requires arbitrarily many colors as alphabet size grows, already for finite collections of languages containing only one-letter words.

**Original question.** Moses Charikar, Jon Kleinberg and Chirag Pabbaraju, 2026. [§6, lower bounds for the distinguishable coloring condition](https://proceedings.mlr.press/v336/charikar26b.html)

## Argument

Take one language for every nonempty subset of an alphabet. Ramsey’s theorem makes its root color and ordered list of letter colors depend only on the size of the subset. Higman’s lemma then supplies two nested sets whose available traces match on every word of the smaller set.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending.

**Priority.** Independent priority review is pending. The original paper proves a three-color lower bound for unrestricted trace functions and a sharp bound under a state-coloring restriction. A follow-up proves different bounds for language identification. [Follow-up paper](https://arxiv.org/abs/2607.11606) · [Higman’s lemma](https://doi.org/10.1112/plms/s3-2.1.326)

**Significance · 58/100.** Raises the known three-color lower bound to an unbounded one for unrestricted trace functions. The growth rate and ordinary identification are separate questions. [Scoring benchmark](../../../docs/scores-and-sources.md)
