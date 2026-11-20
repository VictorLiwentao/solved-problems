# The closure dimension for corrupted contrastive pairs

Wentao Li · Prepared with assistance from OpenAI Codex

A deletion-based dimension gives the exact uniform distinct-pair threshold at every finite corruption budget and characterizes nonuniform generation by increasing unions.

At a prefix, the possible targets come from deleting up to the corruption budget in distinct observed edges. A prefix defeats every generator exactly when those targets have no common unseen positive. The note also gives a three-target example with a sharp one-third corruption threshold.

**Original question.** Xiaoyu Li, Andi Han, Jiaojiao Jiang and Junbin Gao (2026), §8(ii), with the unknown-budget example of Appendix D.2 discussed separately. [Primary source](https://arxiv.org/abs/2605.06211v2)

**Significance estimate: 36/100.** Extends the clean dimension by a direct deletion argument. A separate example tolerates an unknown finite corruption budget with empty common support.

**Proof status.** Written research draft awaiting independent review. **Priority status.** A targeted literature check found the original question and related work. Priority awaits independent review.

The checker compares edge deletion with direct violation counts and tests all length-five streams of representative pairs. [Run the finite check](verify.py)

[Read the proof (PDF)](robust-contrastive-closure.pdf) · [LaTeX source](robust-contrastive-closure.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/robust-contrastive-closure/citation.bib)
