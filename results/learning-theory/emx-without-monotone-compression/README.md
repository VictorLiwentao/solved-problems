# EMX learnability without bounded monotone compression

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](emx-without-monotone-compression.pdf) · [LaTeX](emx-without-monotone-compression.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/emx-without-monotone-compression/citation.bib)

A countable family of finite sets is properly EMX-learnable, yet compressing samples of length up to m takes asymptotically log₂ m sample entries.

**Original question.** Shai Ben-David, Pavel Hrubeš, Shay Moran, Amir Shpilka and Amir Yehudayoff, 2017. [§7, Question 1](https://arxiv.org/abs/1711.05195v1)

## Argument

In each block a hypothesis omits a small set of points. For learning it is enough to leave out one low-mass row. Exact reconstruction must distinguish all the possible missing sets. A cyclic encoder also gives the matching leading term for the optimal compression size.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The finite check exhausts both encoding formats on 4,262 realizable samples. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The original equivalence assumes union boundedness. Hanneke and Yang also use that assumption for their converse reduction. [2019 journal article](https://doi.org/10.1038/s42256-018-0002-3) · [COLT 2023 paper](https://proceedings.mlr.press/v195/hanneke23d.html)

**Significance · 73/100.** Separates two notions of learnability in a question dating to 2017 and quantifies the gap. The separate finite-VC compression question remains open here. [Scoring benchmark](../../../docs/scores-and-sources.md)
