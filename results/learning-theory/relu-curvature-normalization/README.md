# The loss normalization in a ReLU curvature conjecture

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

The bound holds for the squared loss printed in equation (2). Arbitrarily close to a regular minimum, an explicit rotation violates it for the half-squared loss used by the displayed Hessian.

**Original question.** Does the displayed local Hessian lower bound hold near every global minimizer with nonzero student rows in the Gaussian orthonormal teacher model? [Safran, Yehudai and Shamir, 2020, COLT 2021, Conjecture 12 and equations (2) and (5)](https://proceedings.mlr.press/v134/safran21a.html)

**Scope and prior work.** The conference paper proves an approximate bound and reports numerical tests of the exact inequality. Later convergence-rate theorems address different assertions. The present statement concerns the coefficient in Conjecture 12.

**Significance estimate.** 68/100. The factor changes the truth value of an explicit COLT conjecture. Both arguments concern all sufficiently small neighborhoods, and the positive bound handles unequal positive neuron splits.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](relu-curvature-normalization.pdf) · [LaTeX source](relu-curvature-normalization.tex) · [BibTeX](citation.bib)

**Reproducible check.** High-precision differentiation of the full Gaussian kernel loss checks the curvature difference at five perturbation scales using mpmath. [Python script](verify.py)

## Sources

- [Itay Safran, Gilad Yehudai and Ohad Shamir (2020), COLT 2021, Conjecture 12 and equations (2) and (5)](https://proceedings.mlr.press/v134/safran21a.html)
- [Original preprint, 2020](https://arxiv.org/abs/2006.01005)
- [Zhou, Ge and Jin, local convergence](https://proceedings.mlr.press/v134/zhou21b.html)
- [How Gradient Descent Balances Features, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/1a0923d14475272896d54248586af67e-Abstract-Conference.html)
