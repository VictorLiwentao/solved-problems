# Local regularizers can fail at PAC learning

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](affine-local-regularization.pdf) · [LaTeX source](affine-local-regularization.tex) · [Finite verification](verify.py)

Can every learnable multiclass problem be learned by ranking the hypotheses that fit the sample, if the ranking can depend on the test point? Eric Hou answered this question negatively in July 2026 using tournaments. This note gives an alternative proof with affine hyperplanes. The affine proof applies even when the ranking uses the sample size and independent randomness. [COLT 2024 open problem, Definition 2](https://proceedings.mlr.press/v247/asilis24b.html)

## The separation

Each hypothesis uses just two labels. Seeing both identifies the hypothesis. Until then, predicting the one observed label gives expected error at most $2/(m+1)$ after $m$ examples. In contrast, every family of test-point rankings of consistent hypotheses has worst-case expected error greater than $1/16$ at every sample size from two onwards. Breaking ties by a fixed enumeration gives an induced learner, as required by the original all-learners definition.

The target distribution is uniform on an affine hyperplane over the two-element field. With probability greater than a quarter, the independent test point completes the training points to an affine basis. On that event the target is the unique hypothesis that fits the sample and gives the right prediction. Four such tasks yield a cycle of incompatible comparisons at the same test point.

## Proof and priority status

The 2025 transductive separation introduced the two-label mask construction and the four-comparison argument. The affine masks and the basis event give a coupling whose four marginals come from i.i.d. sampling. Hou subsequently resolved the PAC question. [Hou’s paper](https://arxiv.org/abs/2607.23449) A separate formulation permits adding an unrestricted penalty to empirical loss. The proof covers penalties of range strictly below $1/m$ and leaves the unrestricted additive formulation open. [Transductive result and PAC discussion](https://proceedings.mlr.press/v291/jafar25a.html) · [Companion COLT paper](https://proceedings.mlr.press/v247/asilis24a.html)

The checker verifies all 5,376 cycles and all 10,752 conditional target and sample outcomes in dimension three. The PDF proves the result for arbitrarily large samples. The affine argument awaits independent proof review and Lean formalization.
