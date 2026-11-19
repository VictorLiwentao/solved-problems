# Hajnal’s product theorem without the ultrafilter lemma

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](hajnal-products-without-choice.pdf) · [LaTeX source](hajnal-products-without-choice.tex) · [Finite verification](verify.py)

Hajnal proved that a graph of finite chromatic number $k$ retains that chromatic number when multiplied by an infinitely chromatic graph. Two vertices of the product are adjacent when both coordinate pairs are edges. Banerjee and Gyenis asked whether, for $k>3$, this theorem implies the ultrafilter lemma. They explicitly asked for a separating model of ZF or of ZF with atoms. [Hajnal’s theorem](https://doi.org/10.1007/BF02579376) · [Question 5.2 and bibliography](https://arxiv.org/abs/1911.00434) · [Banerjee’s Questions 6.1 and 6.2](https://doi.org/10.14712/1213-7243.2023.028)

## Two models

| Set theory | Graph products | Choice principles |
| --- | --- | --- |
| ZF with atoms, using the basic Fraenkel model | Hajnal’s theorem holds for every finite $k$ simultaneously | Even choice for unordered pairs fails, so the ultrafilter lemma fails |
| Pure ZF with dependent choice | Two countably chromatic graphs have a bipartite product. The same construction can prescribe any finite chromatic number of at least three for either factor | Dependent choice can hold through any prescribed range of ordinal lengths, with the model chosen for that range |

Both conclusions are relative consistency results from ZFC. The first model answers the authors’ question. The second shows how far the graph theorem itself can fail in pure set theory. In ZF, choice for pairs already implies the three-color case by the odd-cycle criterion.

## Why the models differ

In the first model a finite coloring must respect every permutation of atoms fixing its support. Moving the representatives for the two factors so that their supports are disjoint turns a coloring of the product into a coloring of the product of two ordinary orbit graphs. Hajnal’s original theorem applies in the ambient universe, where choice holds.

For the second model, construct two families of pairs. Neither family has a choice function, yet for every row pair and column pair together there is a designated member of their four-element union. This gives a two-coloring of the product of the two matchings. Multiplying each matching separately by a complete graph sets the chromatic numbers of the factors. A theorem of Pincus transfers the existence of the two families into pure ZF while preserving the specified dependent choice. [Transfer theorem](https://doi.org/10.1016/0003-4843(77)90011-0)

## Proof and priority

The PDF gives the permutation-model and transfer arguments. The finite checker verifies the independent-placement map on 256 pairs of graphs with a symmetric-group action and exhausts the two-pair coloring identity. Independent review and Lean formalization are pending. The original papers establish the three-color separation from specific choice axioms and higher-color results with a linearly orderable first vertex set. We found no earlier unrestricted separation for all finite chromatic numbers in the primary papers and their citing literature. [2021 article](https://doi.org/10.14712/1213-7243.2021.028) · [2023 follow-up](https://doi.org/10.14712/1213-7243.2023.028)
