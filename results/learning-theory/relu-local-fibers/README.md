# Finite determination of generic local ReLU realization fibers

Wentao Li · Prepared with assistance from OpenAI Codex · November 20, 2026

Near almost every parameter, a finite batch determines agreement on the entire input space. The local fiber dimension is the number of parameters minus the functional dimension.

**Original question.** Does almost every parameter whose only symmetries are neuron permutations and rescalings attain the full functional-dimension bound? [J. Elisenda Grigsby, Kathryn Lindsey and David Rolnick, 2023, Section 2, functional-dimension conjecture and Lemma F.6](https://proceedings.mlr.press/v202/grigsby23a.html)

**Significance estimate.** 66/100. Answers the symmetry conjecture and gives the dimension of the full local fiber even when additional symmetries occur. The determining batch depends on the neighborhood.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 20, 2026 found the following related results. Independent priority review is pending.

The original paper proves an open-ball lemma for symmetry-identifiable parameters. Earlier work gives decisive batches, and later work treats fixed-batch fibers and identifiable open sets. The draft uses connected level sets of affine coefficients to obtain whole-function equivalence throughout a neighborhood.

[Read the proof (PDF)](relu-local-fibers.pdf) · [LaTeX source](relu-local-fibers.tex) · [BibTeX](citation.bib)

## Sources

- [J. Elisenda Grigsby, Kathryn Lindsey and David Rolnick (2023), Section 2, functional-dimension conjecture and Lemma F.6](https://proceedings.mlr.press/v202/grigsby23a.html)
- [Grigsby et al., Functional dimension of feedforward ReLU neural networks](https://arxiv.org/abs/2209.04036)
- [Stock and Gribonval, An Embedding of ReLU Networks and an Analysis of their Identifiability](https://arxiv.org/abs/2107.09370)
- [Grigsby and Lindsey, On Functional Dimension and Persistent Pseudodimension](https://arxiv.org/abs/2410.17191)
- [Flinth, Mereta and Pernice, On the identifiability and semi-algebraicity of ReLU neuromanifolds](https://arxiv.org/abs/2606.02826)
- [Grillo and Montúfar, Most ReLU Networks Admit Identifiable Parameters](https://arxiv.org/abs/2605.03601)
