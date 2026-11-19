# The axiom of choice and distinguishing vertex colorings

Wentao Li · Prepared with assistance from GPT-6.2 Astra.

[Proof (PDF)](choice-and-distinguishing-colorings.pdf) · [LaTeX source](choice-and-distinguishing-colorings.tex) · [Finite checker](verify.py)

## The equivalence

Work in Zermelo–Fraenkel set theory (ZF). In a *proper distinguishing coloring*, neighbors get different colors and the only symmetry preserving all colors is the identity. A *least* palette is one that works and injects into every other palette that works. The palettes may be arbitrary sets.

**The axiom of choice is equivalent to the assertion that every infinite connected graph has a least palette for proper distinguishing vertex colorings.** In fact the equivalence already holds for ordinary proper colorings of infinite connected graphs with trivial automorphism group.

This answers Question 8.2(4) of Banerjee, Molnár and Gopaulsingh, posed again as Conjecture 3(2) by Stawiski. Question 8.2(8) also has a positive answer. Its published definition compares the sets of colors in the *open* neighborhoods of adjacent vertices. In a proper coloring, the color of either endpoint appears in the other endpoint's neighborhood and is absent from its own. [Original question and Definition 9.1(9)](https://doi.org/10.26493/1855-3974.3453.4a8) · [Stawiski's conjecture](https://arxiv.org/abs/2602.15221)

## Why a least palette implies choice

Galvin and Komjáth showed how a set $A$ that cannot be well-ordered produces a graph with two explicit proper colorings and no least palette. Their vertices are pairs $(a,\xi)$, where $\xi$ ranges over the first ordinal that does not inject into $A$. Either coordinate can serve as a color. If a least palette existed, it would inject into both coordinates. A coloring by that palette would give each row a distinct least repeated color, well-ordering $A$. [Galvin and Komjáth (1991)](https://doi.org/10.1007/BF02309111)

The new proof transfers this obstruction to a connected graph with no symmetries. It encodes membership among the original vertex labels and the sets in their transitive closure. Any symmetry of the encoding fixes those sets by set induction. Each original coloring with at least three colors available extends using its own palette. Consequently the two coordinate colorings still work, and a least palette would still well-order $A$.

## Verification and priority

The three-page proof gives the ZF construction and both directions of the equivalence. The finite checker tests the construction on all 76 labeled simple graphs on the specified sets of zero through four vertices. It verifies rigidity and induced adjacency, and extends all 1,777 proper assignments from a three-color palette. Run it from this directory with Python 3.

~~~sh
python3 verify.py
~~~

The cardinal obstruction for ordinary graph coloring is due to Galvin and Komjáth. Rigid graph constructions without choice also feature in Pinsky's work. I found no earlier resolution of the proper distinguishing vertex clause in the sources checked. Independent review and Lean formalization are pending. [Pinsky on Frucht's theorem in ZF](https://arxiv.org/abs/2305.11382)
