# Which slow sequences count labelled finite models?

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](labelled-model-counts.pdf) · [LaTeX source](labelled-model-counts.tex) · [Finite verification](verify.py) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L73-L79)

Durand, Jones, Makowsky and More ask about the relation between two sequences attached to a logical sentence. One lists the sizes of its finite models. The other counts its models on each labelled domain. On page 515 they ask about the converse to Open Question 10 and give the prime sequence as an example. **No fixed finite relational signature can produce the $n$th prime as its labelled count, even at infinitely many orders.** The pointwise obstruction holds for any isomorphism-invariant class of structures. [Original article, §3.3](https://doi.org/10.2178/bsl.1804020)

## Growth of model counts

For every first-order or monadic second-order sentence, the labelled count $f(n)$ falls into one of two ranges.

- If $f(n)$ is bounded by $C^n$ for some constant $C$, then at every sufficiently large order it equals a fixed sum of terms $P_j(n)j^n$, with rational polynomials $P_j$ and positive integer bases $j$. Its exponential growth rate is an integer. This happens exactly when the number of classes of interchangeable elements in every finite model is bounded.
- Otherwise, arbitrarily large orders have at least $n^{n/b}e^{-O(n)}$ labelled models, where $b\ge2$ bounds the relational arity. For ordinary graphs, perfect matchings attain the exponent $1/2$.

Below exponential base two the eventual counts are exactly the sums $\sum_k a_k\binom nk$ with nonnegative integer coefficients. In particular there is no count growing like $n\log n$. In the other direction, every strictly increasing finite-exponential count lists a first-order spectrum. The unrestricted forward question remains open in the sources checked.

## Why symmetry controls the answer

Two elements are interchangeable if swapping them while fixing every other element preserves every relation. A sentence of fixed monadic quantifier rank cannot distinguish a sufficiently large such class from a larger one. When there are only boundedly many classes, distributing labels among them gives the counting formula. If the number of classes grows, truncate each to a fixed size. The shortened structure still satisfies the sentence. Its automorphism group is then small enough to give factorial growth on these orders.

Determining which growth range a first-order sentence occupies is $\Sigma^0_2$-complete, even within an explicit family of strictly increasing counts. The proof encodes the finite-enumeration index set in the sizes of an ordered active substructure.

## Verification and priority

The checker exhausts small graphs and digraphs and compares 204 template counts with a separate recurrence. The general proof treats arbitrary finite relational signatures and monadic quantification over elements and sets of elements. Earlier results of Laskowski and Terry give a finer hierarchy for hereditary classes. The argument here applies to sentences whose finite models need not be closed under induced substructures. The small-index theorem is classical. I found no earlier resolution of the prime converse or the general finite-exponential classification for these sentences in the sources checked through November 19, 2026. Independent review and Lean formalization are pending. [Hereditary speed theorem](https://arxiv.org/abs/1803.10575) · [Dixon and Mortimer, Theorem 5.2B](https://doi.org/10.1007/978-1-4612-0731-3)
