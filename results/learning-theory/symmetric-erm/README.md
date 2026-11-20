# A logarithmic gap between empirical risk minimizers under label symmetry

Wentao Li · Prepared with assistance from OpenAI Codex

Two proper empirical risk minimizers on one label-symmetric class have realizable sample complexities differing by a factor logarithmic in the Natarajan dimension.

**Original question.** Amit Daniely, Sivan Sabato, Shai Ben-David and Shai Shalev-Shwartz (2011), Question 16; sharpened in JMLR 2015, Question 19. [Primary source](https://proceedings.mlr.press/v19/daniely11a.html) The later journal version states the logarithmic Natarajan-dimension question explicitly. [JMLR, Question 19](https://jmlr.org/papers/v16/daniely15a.html)

**Significance estimate.** 73/100. A shared label dictionary resolves a longstanding question about how much the choice of empirical minimizer can matter under symmetry.

**Proof status.** Written research draft awaiting independent verification. **Priority status.** Targeted source checks found the originating question and related work. Independent priority review is pending.

[Proof (PDF)](symmetric-erm.pdf) · [LaTeX source](symmetric-erm.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/symmetric-erm/citation.bib)

[Finite check](verify.py). Exhausts all realizable partial samples of a two-block example and checks the decoder.
