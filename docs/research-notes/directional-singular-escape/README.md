# Limiting directions and mixed singular-value escape

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Every escaping predictor has a limiting direction with zero diagonal. Explicit trajectories have simultaneous singular-value growth and decay, with exact rates and diagonal loss tending to one half.

**Original question.** Does a normalized escaping predictor converge, and can some singular values vanish while others diverge? [Treviño, 2026, Section 12.4, questions 2 to 4](https://arxiv.org/abs/2610.05551)

**Scope and prior work.** The new application uses a definable Euclidean factor lift. The list of all possible directions, their generic ranks and the generic completion loss remain undetermined.

**Significance estimate.** 59/100. It answers the directional convergence clause and exhibits singular escape across depths. The general finite-length theorem is prior work, and the example has positive codimension.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](directional-singular-escape.pdf) · [LaTeX source](directional-singular-escape.tex)

## Sources

- [Rodrigo Treviño (2026), Section 12.4, questions 2 to 4](https://arxiv.org/abs/2610.05551)
- [Do, Jentzen and Kuckuck, Finite spherical length for gradient trajectories of definable potentials](https://arxiv.org/abs/2610.29211)
- [Menon and Yu, An entropy formula for the deep linear network](https://arxiv.org/abs/2509.09088)
