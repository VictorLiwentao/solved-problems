# A zero-one law for two-connected graphs

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](two-connected-graph-zero-one-law.pdf) · [LaTeX source](two-connected-graph-zero-one-law.tex) · [Finite enumeration](verify.py)

Heinig, Müller, Noy and Taraz asked whether every monadic second-order sentence has limiting probability zero or one on a uniform labelled two-connected graph from a proper 2-addable minor-closed class. These classes allow two graphs to be joined along a shared edge. Examples include planar and series-parallel graphs. We assume the class contains a cycle so that the random model exists at arbitrarily large sizes. [Original question, §6](https://arxiv.org/abs/1401.7021)

## Result

At every fixed quantifier rank, one finite graph gives the truth value of every sentence on the random graph with exponentially high probability. This also holds when the logic can quantify over sets of edges. Each fixed admissible two-connected graph occurs in linearly many vertex-disjoint copies that meet the rest of the graph only at a chosen edge and its endpoints.

The proof counts how many graphs can be constructed by inserting the same fixed graph along several different edges. Two additional triangles make the inserted interior connected, so a bounded number of candidate interiors can contain any given vertex. This controls the overcount even when a vertex has very high degree. Repeated edge gluing then builds a finite graph whose logical type absorbs any admissible remainder.

## Which almost-sure truths can an algorithm decide?

The almost-sure monadic second-order theory is decidable exactly when the class has bounded treewidth. This classification also holds for connected and unrestricted samples from every proper addable minor-closed class. Thus, on two-connected planar graphs every sentence has a zero-one limit, yet no algorithm decides for all sentences which limit it has. The proof uses finite satisfiability and classical theorems of Courcelle and Seese. [Courcelle on recognizable finite graphs](https://doi.org/10.1016/0890-5401(90)90043-H)

## Verification and priority

The checker exhausts all two-connected graphs through six vertices, verifies that cutting along a separating edge leaves two valid pieces, and checks the rooted counting identity and growth inequalities. The PDF gives the proofs for all graph sizes and quantifier ranks. The original connected-graph law, single-root logical construction and bridge-appearance arguments are credited. A search of the authors’ paper, its citing literature, and the later appearance and logical-limit papers found no earlier resolution of the edge-gluing question. Independent review and Lean formalization are pending. [Prior bridge-appearance theorem](https://doi.org/10.1016/j.ejc.2024.103994) · [Prior connected-graph laws](https://lmcs.episciences.org/5644)
