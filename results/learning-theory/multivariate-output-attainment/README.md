# When a width-one network attains its best fit

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Vector-output tanh chains of every hidden depth can fail to attain the least-squares infimum on an open set of labels. Width-one ReLU chains attain a best fit on every finite sample.

**Original question.** Does positive-measure nonattainment extend to vector outputs or ReLU for the width-one chains in Theorem 5? [Lim, Michałek and Qi, 2019, two questions after Theorem 5 in the 2022 journal version](https://arxiv.org/abs/1907.01507)

**Scope and prior work.** The hidden layers have width one. Wider finite-data ReLU networks can have different attainment behavior. The tanh input design can have repeats, as allowed in the original theorem.

**Significance estimate.** 57/100. It settles the two alternatives for the architecture in the original theorem. The tanh argument extends the authors’ scalar example, and the ReLU proof classifies its finite-data prediction shapes.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](multivariate-output-attainment.pdf) · [LaTeX source](multivariate-output-attainment.tex) · [BibTeX](citation.bib)

**Reproducible check.** Exact rational arithmetic checks the strict gap identity in the weighted least-squares calculation. [Python script](verify.py)

## Sources

- [Lek-Heng Lim, Mateusz Michałek and Yang Qi (2019), two questions after Theorem 5 in the 2022 journal version](https://arxiv.org/abs/1907.01507)
- [Journal version with Theorem 5 and the open question](https://doi.org/10.1007/s00365-021-09545-2)
- [Le, Riccietti and Gribonval on sparse ReLU attainment](https://arxiv.org/abs/2306.02666)
