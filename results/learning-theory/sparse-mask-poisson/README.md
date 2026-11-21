# When random sparse ReLU networks have no best fit

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

For independent masks of bounded expected degree, the probability that some nine-example ReLU problem has no minimizer tends to one. The linear matrix-product test has a different, explicit Poisson limit.

**Original question.** How likely is a randomly supported network to admit some finite training problem with no optimal weights? [Q.-T. Le, Riccietti and Gribonval, 2023, Question 3.2 (NeurIPS 2023)](https://arxiv.org/abs/2306.02666)

**Scope and prior work.** All three layer sizes grow together, with edge probabilities a/n and b/n for any fixed positive a and b. The data may depend on the mask. The theorem concerns potential failure for the mask and does not give the frequency on independently sampled data.

**Significance estimate.** 66/100. It distinguishes true finite-data nonattainment from the commonly used linear-image test and gives exact limiting probabilities in a canonical sparse ensemble.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](sparse-mask-poisson.pdf) · [LaTeX source](sparse-mask-poisson.tex) · [BibTeX](citation.bib)

**Reproducible check.** Exact rational calculations verify the nine training examples, affine independence of every triple and a sequence of networks approaching the unattainable target. [Python script](verify.py)

## Sources

- [Quoc-Tung Le, Elisa Riccietti and Rémi Gribonval (2023), Question 3.2 (NeurIPS 2023)](https://arxiv.org/abs/2306.02666)
- [Le, Riccietti and Gribonval, NeurIPS conference paper](https://proceedings.neurips.cc/paper_files/paper/2023/file/cdda0657a9f32bc7ddd4343686e7371e-Paper-Conference.pdf)
