# Three gaps in logical limit laws for random graphs

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](three-gaps-in-graph-limit-laws.pdf) · [LaTeX source](three-gaps-in-graph-limit-laws.tex) · [Reproducible enumeration](verify.py) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L89-L95)

What probabilities can a logical sentence have on a large uniformly random labelled graph? For forests, exactly three open gaps separate the attainable limits after taking closure. Heinig, Müller, Noy and Taraz predicted at least three gaps for every proper addable minor-closed graph class. Their Conjecture 6.2 asks for an inequality between the exponential generating function of the class and its radius of convergence. [Original paper, §6](https://arxiv.org/abs/1401.7021)

## Result

For every such class with generating function $G$ and radius $\rho$,

$$
G(\rho)\le 1+e(\sqrt e-1)\rho <1+2\rho.
$$

Forests attain the first bound and are the unique equality case. In fact the forest generating function gives a pointwise upper bound after normalization by the radius. The proof applies to every positive-radius class whose membership is determined by its allowed blocks and which allows a single edge.

The largest component leaves behind a random finite graph. Its probabilities of being empty or a single vertex are $p=1/G(\rho)$ and $q=\rho/G(\rho)$. Each outweighs the total mass of the outcomes after it. Choosing whether to include each of these two outcomes splits the limiting probabilities into four separated groups. This applies to both first-order and monadic second-order logic.

## Scope and verification

Outside block-stable classes the conclusion can fail even if adding and deleting bridges is allowed. The paper constructs smooth addable classes with exactly one gap and arbitrarily large $(G(\rho)-1)/\rho$.

The enumeration checks the two decompositions used in the proof on every labelled graph through six vertices. The PDF proves the universal inequalities and the limiting probability statements. The previously known connected-fragment bound gives the middle gap. The new comparison supplies the two outer gaps and the sharp constant. A search of the original paper, citing literature and work on block-stable enumeration found no earlier resolution of Conjecture 6.2. Independent review and Lean formalization are pending. [Block decomposition](https://doi.org/10.1137/100790161) · [Logical laws for smooth addable classes](https://lmcs.episciences.org/5644)
