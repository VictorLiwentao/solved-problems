# The exact hardmax margin of a neural classifier

Wentao Li · Prepared with assistance from OpenAI Codex · November 20, 2026

The best one-versus-rest margin equals half the squared optimal packing distance. Every best packing is an optimal classifier. Both optimizer sets agree if every best packing has at most one rattler.

**Original question.** Do softmax codes and optimal spherical packings have the same maximizers at arbitrary class count and dimension? [Jiachen Jiang, Jinxin Zhou, Peng Wang, Qing Qu, Dustin Mixon and Chong You, 2023, Section 3.2, conjecture after Theorem 3.7 and Theorem 3.9](https://arxiv.org/abs/2310.05351)

**Significance estimate.** 74/100. The equality gives the exact optimization value and the sharp fixed-dimensional decay rate. Multiple rattlers leave one direction of the original optimizer-set conjecture unresolved.

**Problem status.** The margin theorem has a written proof. The unrestricted conjecture on equality of optimizer sets remains open in the case of multiple rattlers. **Priority status.** A targeted search through November 20, 2026 found the following related results. Independent priority review is pending.

Jiang et al. connected classification margins to spherical packing. Alcala and coauthors classified the orthoplex regime. The draft proves the optimum value for all class counts and dimensions at least two, and proves a converse when at most one vertex in any optimal packing has slack.

[Read the proof (PDF)](hardmax-spherical-margin.pdf) · [LaTeX source](hardmax-spherical-margin.tex)

**Reproducible check.** Checks 81 rational configurations with unequal midpoint lengths and the radial margins of an octahedron. [Python script](verify.py)

## Sources

- [Jiachen Jiang, Jinxin Zhou, Peng Wang, Qing Qu, Dustin Mixon and Chong You (2023), Section 3.2, conjecture after Theorem 3.7 and Theorem 3.9](https://arxiv.org/abs/2310.05351)
- [Alcala et al., Neural collapse in the orthoplex regime](https://arxiv.org/abs/2603.20587)
- [L. Fejes Tóth, spherical packing bound (1943)](https://geodesic.mathdoc.fr/item/JDM_1943__53_146329/)
