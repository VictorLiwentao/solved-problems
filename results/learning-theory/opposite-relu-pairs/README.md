# Finite local identification of opposite ReLU neuron pairs

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

With free biases, the opposite pairs admit finite local identification exactly when their normals are independent across pairs and their two output vectors are independent within each pair.

**Original question.** When can finite observations away from activation hyperplanes identify a shallow network with several pairs of negative twins? [Stock and Gribonval, 2021, Section 5.4 before Lemma 16, paper first posted in 2021](https://arxiv.org/abs/2107.09370)

**Scope and prior work.** Stock and Gribonval treat one pair and establish the relation with nondegeneracy. The criterion here treats joint perturbations of arbitrarily many pairs. All units have nonzero normal and output, and there are no positive twins.

**Significance estimate.** 54/100. A necessary and sufficient condition covers any number of pairs. It addresses a singular locus of shallow networks with a specific sampling restriction.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](opposite-relu-pairs.pdf) · [LaTeX source](opposite-relu-pairs.tex) · [BibTeX](citation.bib)

## Sources

- [Pierre Stock and Rémi Gribonval (2021), Section 5.4 before Lemma 16, paper first posted in 2021](https://arxiv.org/abs/2107.09370)
- [Yu Xia and Zhiqiang Xu, Finite Samples for Shallow Neural Networks, a distinct same-width reconstruction result](https://arxiv.org/abs/2503.12744)
