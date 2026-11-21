# An unattained zero training loss for a scalar deep ReLU network

Wentao Li · Prepared with assistance from OpenAI Codex · November 21, 2026

A scalar network with hidden widths one and two has squared-loss infimum zero on 30 rational examples. No weights interpolate the examples.

**Original question.** Must a fixed fully connected scalar ReLU network attain its optimal loss on a finite training set? [Eloi Martinet and Leon Bungert, 2026, Section 5, finite-data question and equation (10)](https://arxiv.org/abs/2611.09887)

**Significance estimate.** 67/100. Settles finite-sample attainment negatively even for a small, fully connected scalar network. Shallow scalar attainment and vector-output counterexamples were already known.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 21, 2026 found the following related results. Independent priority review is pending.

Lim, Michałek and Qi gave a finite-data counterexample with vector output. Le, Riccietti and Gribonval proved finite-data attainment for scalar one-hidden-layer networks. Kassing and Martinet–Bungert studied continuous-domain obstructions.

[Read the proof (PDF)](finite-data-relu-nonattainment.pdf) · [LaTeX source](finite-data-relu-nonattainment.tex) · [BibTeX](citation.bib)

**Reproducible check.** Evaluates the explicit networks and the squared-loss identity with rational arithmetic. The interval-count argument in the manuscript excludes every exact interpolant. [Python script](verify.py)

## Sources

- [Eloi Martinet and Leon Bungert (2026), Section 5, finite-data question and equation (10)](https://arxiv.org/abs/2611.09887)
- [Lim, Michałek and Qi, Best k-Layer Neural Network Approximations](https://doi.org/10.1007/s00365-021-09545-2)
- [Le, Riccietti and Gribonval, scalar one-hidden-layer result (2023)](https://arxiv.org/abs/2306.02666)
- [Kassing, continuous-target nonattainment (2026)](https://arxiv.org/abs/2610.31264)
