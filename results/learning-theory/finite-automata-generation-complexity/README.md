# Uniform generation from all state-bounded binary automata

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](finite-automata-generation-complexity.pdf) · [LaTeX source](finite-automata-generation-complexity.tex) · [Finite checks](verify.py) · [Research catalogue](../../../README.md) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/b0f255641f8f4af462caf94969bbac64c39af0c5/citations.bib#L417-L423)

For the full class of infinite binary languages recognized by at most $s$ states, the worst-case uniform sample complexity $T(s)$ satisfies $\log_2\log_2\log_2 T(s)=\Theta(s\log s)$.

**Original question.** Marcelo Arenas, Pablo Barceló, Luis Cofré and Alexander Kozachinskiy, 2026, question following Theorem 4.2 in the ICML paper. [Primary source](https://proceedings.mlr.press/v306/arenas26a.html)

## Argument

A transition table with order $k$ states reads addresses drawn from $k^k$ possibilities. One automaton guards each address. The least address can appear only once and splits a legal word into two shorter legal words. One free bit per instruction turns the length bound into a double-exponential number of shared words.

## Proof and priority

The PDF gives the full argument. The checker compares 745 address pairs and exhausts 21,845 short address words. It independently computes exact maximum lengths and counts for up to seven addresses. Independent mathematical review and Lean formalization are pending.

The source supplies the reset rule, the upper bound by products, and the criterion using finite intersections. Its lower bound with a comparator that reads fixed binary addresses loses strength when the family has superexponentially many members in the state budget. The new lookup encoding handles precisely that regime. The 2025 preprint predates the ICML formulation. Ang and Shallit’s two-language result concerns the shortest shared word. [Preprint](https://arxiv.org/abs/2511.05759) · [Ang and Shallit](https://arxiv.org/abs/0910.1528)

A search through November 19, 2026 found no earlier resolution of the specific assertion claimed here. Priority awaits independent confirmation.

**Significance estimate: 68/100.** Gives the asymptotic scale for the full state-bounded class. The construction reaches the large-family regime where the published lower bound becomes vacuous. The 100-point benchmark is a full resolution of three-dimensional Navier–Stokes existence and smoothness.
