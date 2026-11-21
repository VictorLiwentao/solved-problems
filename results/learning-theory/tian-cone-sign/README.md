# The cone-sign conjecture for two ReLU neurons

Wentao Li · Prepared with assistance from OpenAI Codex · November 21, 2026

Yuandong Tian studied what the exact population gradient reveals about training two ReLU neurons on Gaussian inputs. In Conjecture 1 of his ICML 2017 paper he predicted that an interpolation residual changes sign exactly at the two student directions. Immediately after Theorem 4 he asked whether a stationary point can have exactly one teacher inside that cone. [Original paper, §5.3](https://proceedings.mlr.press/v70/tian17a.html)

**Results.** The manuscript proves the sign conjecture for every opening angle between two independent coplanar student directions. It also constructs, for every such opening, linearly independent teacher directions with exactly one inside the cone for which the students are stationary. These examples have positive loss and a direction of strictly negative curvature.

[Read the proof (PDF)](tian-cone-sign.pdf) · [LaTeX source](tian-cone-sign.tex) · [Reproduce the checks](verify.py) · [BibTeX](citation.bib)

**Scope and significance.** The sign proof makes Tian’s conditional Theorem 4 unconditional on its stated domain. The saddle construction describes a configuration left open in that paper. The full optimization landscape for general teacher configurations requires more. The 2026 work of Li, Li, Wu and Wang classifies a related landscape under its teacher-angle and model hypotheses. **65/100 for the two results together**, conditional on correctness and novelty. [Li et al., Remark 3.6](https://arxiv.org/abs/2610.42118)

**Verification.** The proof uses trigonometric inequalities and the implicit function theorem over the full angle intervals. The accompanying high-precision computation independently evaluates Tian’s original gating formula, the full gradients at noncollinear examples, and the curvature of the profiled loss. Independent proof and priority review are pending.
