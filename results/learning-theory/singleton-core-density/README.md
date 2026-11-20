# The singleton sparse-core density game

Wentao Li · Prepared with assistance from OpenAI Codex

For a known target and an unknown core of exact density $a$ up to one half, the optimal output density is $1-a$. Prescribing only lower density changes the answer.

The adversary reserves a quota in each block of target words and immediately repairs a block if a generator output endangers its quota. A spare word per block prevents repair moves from starving the other blocks.

**Original question.** Xiaoyu Li, Andi Han, Dai Shi, Zheng Gao, Jiaojiao Jiang and Junbin Gao (2026), §5, open problem 1. [Primary source](https://arxiv.org/abs/2606.14688v1)

**Significance estimate: 47/100.** A quota strategy gives the matching obstruction against every generator and identifies a consequential density convention.

**Proof status.** Written research draft awaiting independent review. **Priority status.** A targeted literature check found the original question and related work. Priority awaits independent review.

The checker exhausts generator moves on a finite board and tests the quota invariant after each response. [Run the finite check](verify.py)

[Read the proof (PDF)](singleton-core-density.pdf) · [LaTeX source](singleton-core-density.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/singleton-core-density/citation.bib)
