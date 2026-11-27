# Three attention tokens can have negative energy curvature

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

For positive-definite kernel and mobility matrices, three fixed-mass tokens can have negative intrinsic energy curvature. In dimension at least two, even three equal masses have no finite uniform lower Hessian bound.

**Original question.** Does geodesic convexity hold on smaller classes of measures or under different sign conditions in the twisted attention metric? [Castin et al., 2025, Section 5.4 after Proposition 5.4, 2026 revision](https://arxiv.org/abs/2501.18322)

**Scope and prior work.** The curves are intrinsic geodesics of the fixed-mass token manifold. Minimization over arbitrary splitting of mass in the full Wasserstein space is a different problem.

**Significance estimate.** 65/100. It finds nonconvexity on a natural family of empirical measures in the opposite sign regime to the source theorem, even when the associated attention flow collapses to zero.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](twisted-attention-curvature.pdf) · [LaTeX source](twisted-attention-curvature.tex)

**Reproducible check.** A Christoffel-symbol calculation using mpmath independently checks a negative curvature quotient for three equal masses in the plane. [Python script](verify.py)

## Sources

- [Valérie Castin, Pierre Ablin, José A. Carrillo and Gabriel Peyré (2025), Section 5.4 after Proposition 5.4, 2026 revision](https://arxiv.org/abs/2501.18322)
- [2026 revision with the definition of the twisted metric](https://arxiv.org/html/2501.18322v2)
