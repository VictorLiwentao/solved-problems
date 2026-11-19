# A universal spectrum on uncoloured planar graphs

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](universal-planar-spectrum.pdf) · [LaTeX source](universal-planar-spectrum.tex) · [Finite verification](verify.py)

The *spectrum* of a sentence is the set of positive integers that occur as the sizes of its finite models. In Open Question 19, Durand, Jones, Makowsky and More ask whether one spectrum can represent every other spectrum and suggest first-order reductions for the finite-set version. [Original question, p. 531](https://doi.org/10.2178/bsl.1804020)

The proposed construction gives a single first-order graph sentence. For each source sentence, a quantifier-free formula selects tuples from an unordered input set using only equality. The input size is in the source spectrum exactly when the number of selected tuples is in the graph sentence’s spectrum. All its finite models are connected, planar, bipartite graphs of maximum degree three. One can require any fixed lower bound on cycle length.

## How one graph sentence encodes many questions

The number of ordered unequal pairs from an input of size $n$ is $n(n-1)$. For $n\ge2$ this lies strictly between consecutive squares. By taking tuples of these pairs, the reduction can square this number repeatedly. The decoder counts the successive exact square roots to recover the source machine code, then recovers $n$. A short interval around each code handles singleton inputs and the fixed cost of graph encoding. A planar grid records an accepting computation. Replacing each grid cell by a marked cycle encodes its local data using one uncoloured edge relation. [Grid construction, Corollary 4.1](https://doi.org/10.3233/FI-2020-1966)

For every $\eta>0$ one can choose the target to accept only $O(X^\eta)$ sizes up to $X$. Any universal target for these reductions has at least power-law growth along large sizes, and no common upper bound on tuple dimension suffices for all sources. Requiring maximum degree two would also rule out universality for connected models. Closure of all spectra under complement is equivalent to the complement of this particular spectrum being a spectrum. Asser’s complement question itself remains open.

## Checks and priority

The checker exercises the integer decoder and singleton cases, enumerates small equality-defined tuple domains, and constructs cells in small rectangular graphs. It checks the encoded order, connectivity, bipartition, maximum degree and rings. The proof covers arbitrary machines and finite orders.

Universal nondeterministic simulation, complete generalized spectra on structured inputs, and the reduction of Asser’s question to the family of three-variable bipartite spectra all predate this note. The proposed contribution is universality on bare sets with an equality-only tuple domain and a single sparse graph spectrum of the stated form. The priority search found no previous statement of this combination. Independent proof review and Lean formalization are pending. [Fagin](https://www.cs.umd.edu/~gasarch/COURSES/752/S25/slides/genspec.pdf) · [Dawar and Kopczyński](https://doi.org/10.23638/LMCS-13(4:6)2017) · [Kopczyński and Tan](https://www.csie.ntu.edu.tw/~tonytan/research/2018-lmcs-spec-3var.pdf)
