# Exact polygon selection at sufficiently large finite depth

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

A depth threshold polynomial in the class count guarantees that every global minimizer in the equal-norm positive-semidefinite logit model is a regular polygon.

**Original question.** Does the regular polygon predicted at infinite depth already occur at finite depth? [Garrod, Keating and Thrampoulidis, 2026, Section 3.3 following Theorem 3.2 and Appendix D.2](https://proceedings.mlr.press/v306/garrod26a.html)

**Scope and prior work.** The planar determinant minimization is due to Garrod et al. The new comparison excludes higher rank uniformly at finite depth. Intermediate depths, unrestricted logits and gradient-descent trajectories remain open here.

**Significance estimate.** 70/100. It turns an asymptotic geometric prediction into an exact statement at finite depth for every class count above two. The model imposes strong conditions on the logits.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](finite-depth-polygon.pdf) · [LaTeX source](finite-depth-polygon.tex)

## Sources

- [Connall Garrod, Jonathan P. Keating and Christos Thrampoulidis (2026), Section 3.3 following Theorem 3.2 and Appendix D.2](https://proceedings.mlr.press/v306/garrod26a.html)
- [Authors’ preprint and planar determinant argument](https://arxiv.org/abs/2605.23087)
