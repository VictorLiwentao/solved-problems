# Finite-temperature classifiers can improve on every hardmax pair

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Throughout the interior orthoplex regime, every hardmax pair is suboptimal at sufficiently low positive temperature. At high temperature, unrestricted optima approach centered tight frames whenever these exist.

**Original question.** Which classifiers minimize cross-entropy at positive temperature, beyond optimization restricted to hardmax codes? [Alcala et al., 2026, Theorem 12 and Section 5](https://arxiv.org/abs/2603.20587)

**Scope and prior work.** The source characterizes temperature selection restricted to aligned hardmax codes. Bondarenko, Hardin and Saff studied a related moving-pyramid limit for pairwise spherical energy.

**Significance estimate.** 66/100. It separates two optimization problems across a full range of class counts and dimensions. The minimizers at intermediate temperatures have yet to be classified.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](orthoplex-temperature.pdf) · [LaTeX source](orthoplex-temperature.tex)

**Reproducible check.** Verifies 80 ordered contact counts and one finite-temperature comparison. [Python script](verify.py)

## Sources

- [James Alcala, Rayna Andreeva, Vladimir A. Kobzar, Dustin G. Mixon, Sanghoon Na, Shashank Sule and Yangxinyu Xie (2026), Theorem 12 and Section 5](https://arxiv.org/abs/2603.20587)
- [Bondarenko, Hardin and Saff, Mesh ratios for best-packing and limits of minimal energy configurations](https://arxiv.org/abs/1212.6211)
