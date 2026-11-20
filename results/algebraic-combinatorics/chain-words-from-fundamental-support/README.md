# Reading longest chains from fundamental support

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](chain-words-from-fundamental-support.pdf) · [LaTeX](chain-words-from-fundamental-support.tex) · [BibTeX](citation.bib)

## Original problem

Does equality of labeled partition enumerators determine height? Does containment of fundamental supports reverse the height inequality? [McNamara and Ward, 2012, Question 4.4](https://arxiv.org/abs/1210.2412) · [Lesnevich and McNamara, 2020, Question 3.8](https://arxiv.org/abs/2006.10087).

## Result

Yes to both. The support determines every word of weak and strict edge types occurring as a subsequence along a saturated chain. Its longest word recovers height.

Lesnevich and McNamara posed the stronger support-containment question in 2020. Their bounds on the counts of strict and weak edges allowed different chains to realize the two bounds. [Stronger question 3.8](https://arxiv.org/abs/2006.10087)

**Significance 69/100.** Answers a 2012 equality question and its 2020 strengthening with one theorem for all finite labeled posets. The recovered information is finer than height or the separate counts of weak and strict edges. Independent review of the proof and priority is pending.

## Reproducible check

The check compares chain subsequences with cuts of linear extensions for 30,421 schedules on 1,007 orders with vertex labelings, through four vertices. [Verification script](verify.py)
