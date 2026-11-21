# When noisy attention stays independent at all times

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

From independent uniform tokens, finite marginals remain asymptotically independent uniformly over all times precisely when uniformity is the unique free-energy minimizer. At discontinuous coexistence even two tokens develop persistent correlations at sufficiently long times.

**Original question.** Can uniform-in-time independence fail for noisy self-attention, and what does the phase transition imply for this question? [Rigollet, 2025, Section 7, noisy transformers](https://arxiv.org/abs/2512.01868)

**Scope and prior work.** The source asks about a broader quantitative theory. This result gives a qualitative criterion for one initialization, with no all-time error rate. The static phase diagram is due to Mun and Rosenzweig.

**Significance estimate.** 70/100. It links a static phase diagram to correlations over arbitrarily many layers and resolves the coexistence endpoint for the exponential kernel and uniform initialization.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](uniform-time-noisy-attention.pdf) · [LaTeX source](uniform-time-noisy-attention.tex)

## Sources

- [Philippe Rigollet (2025), Section 7, noisy transformers](https://arxiv.org/abs/2512.01868)
- [Mun and Rosenzweig, phase transitions in arbitrary dimension](https://arxiv.org/abs/2606.05140)
- [Delarue and Tse, uniform weak propagation of chaos on the torus](https://doi.org/10.1214/23-AIHP1451)
