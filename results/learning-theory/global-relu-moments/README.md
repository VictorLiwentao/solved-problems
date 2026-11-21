# Finite Gaussian moments determine an entire ReLU function

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

For every fixed ReLU architecture, finitely many ordinary mixed Gaussian or product-Laplace moments determine its output everywhere. Almost every list of 2P+1 polynomial measurements suffices for P scalar-network parameters.

**Original question.** Can a list of moments of the outputs under an input distribution recover the identifiability information of the full network function? [Grillo and Montúfar, 2026, Section 7, question 4](https://arxiv.org/abs/2605.03601)

**Scope and prior work.** The tests are expectations of the output multiplied by known input polynomials. Equality recovers the realized function. The finite degree bound is large and the argument supplies no statistical recovery guarantee.

**Significance estimate.** 73/100. One fixed list works for every parameter, including degenerate gates and changes of slope arbitrarily far from the origin. No uniform finite list of point evaluations can do that even for one ridge ReLU.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](global-relu-moments.pdf) · [LaTeX source](global-relu-moments.tex) · [BibTeX](citation.bib)

**Reproducible check.** Direct high-precision quadrature and differentiation test the Gaussian face recurrence on a rotated half-space for six choices of threshold and tilt, using mpmath. [Python script](verify.py)

## Sources

- [Moritz Grillo and Guido Montúfar (2026), Section 7, question 4](https://arxiv.org/abs/2605.03601)
- [Gravin, Lasserre, Pasechnik and Robins, inverse moments of convex polytopes](https://arxiv.org/abs/1106.5723)
- [Gravin et al., moments of a polytope](https://arxiv.org/abs/1210.3193)
- [Batenkov and Binyamini, moment vanishing for piecewise functions](https://arxiv.org/abs/1302.0991)
- [Stock and Gribonval, ReLU identifiability](https://arxiv.org/abs/2107.09370)
