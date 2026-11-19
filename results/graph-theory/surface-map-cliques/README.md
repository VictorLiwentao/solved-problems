# Clique covers in map graphs on surfaces

Wentao Li · AI-assisted research note

[Read the proof (PDF)](surface-map-cliques.pdf) · [LaTeX source](surface-map-cliques.tex) · [Result catalogue](../../../README.md)

## Original question

Does each fixed Euler genus bound the clique-cover degeneracy of its map graphs? [Dallard, Milanič, Munaro, and Yang, Question 7.3](https://arxiv.org/abs/2506.12424)

## Result

The maximum has order $\Theta(1+\sqrt g)$ at Euler genus $g$. For an $n$-vertex map graph the proof also gives a balanced separator covered by $O(\sqrt{(g+1)n})$ cliques. The size in this second statement counts cliques.

The upper bound counts incidences in an embedded bipartite witness to find a vertex whose neighborhood is covered by few cliques. Subdivided complete bipartite graphs give witnesses for the matching lower bound.

## Verification

The note gives a theoretical proof. The lower-bound construction and the separator argument are both in the PDF.

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
