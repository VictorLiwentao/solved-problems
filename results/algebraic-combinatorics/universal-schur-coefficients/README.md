# Universal Schur coefficients of chromatic symmetric functions

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](universal-schur-coefficients.pdf) · [LaTeX](universal-schur-coefficients.tex) · [BibTeX](citation.bib)

## Original problem

Which partition shapes have a nonnegative Schur coefficient in the chromatic symmetric function of every finite graph? [Noah Kravitz, 2026](https://doi.org/10.1007/s00026-026-00855-5) (Section 1.2, final paragraph).

## Result

Exactly the hooks. For each non-hook shape, a complete multipartite graph gives a strictly negative coefficient at that prescribed shape.

Kravitz proved the elementary-basis classification. Kaliszewski proved the Schur hook direction. Shelburne and van Willigenburg classified which complete multipartite graphs are Schur-positive. Their quantifier fixes the graph. Sun, Wang and Wang subsequently classified elementary positivity within that graph class. Here the prescribed datum is the individual Schur coefficient. [Sun, Wang and Wang](https://arxiv.org/abs/2607.19110) [Kaliszewski](https://intlpress.com/site/pub/files/_fulltext/journals/joc/2015/0006/0003/JOC-2015-0006-0003-a004.pdf) · [Shelburne and van Willigenburg](https://arxiv.org/abs/2604.26158)

**Significance 66/100.** Completes a classification in Stanley’s chromatic symmetric function theory. The construction targets every shape, using classical Kostka triangularity and the known hook theorem. Independent review of the proof and priority is pending.

## Reproducible check

Schur alternant extraction verifies the negative coefficient independently for each of the 778 non-hook shapes through size 16. [Verification script](verify.py)
