# A finite-witness test for oracle-free sound coverage

Wentao Li · Prepared with assistance from OpenAI Codex

Finite positive witnesses characterize when full positive data suffice to cover every unseen target point while remaining inside an unknown ambient language.

A finite witness for a target must exclude every smaller candidate whose allowed ambient set cannot contain the whole target. When witnesses exist, the first compatible candidate supplies an output meeting both inclusion requirements.

**Original question.** Xiaoyu Li, Andi Han, Dai Shi, Zheng Gao, Jiaojiao Jiang and Junbin Gao (2026), §5, open problem 5. [Primary source](https://arxiv.org/abs/2606.14688v1)

**Significance estimate: 43/100.** Gives an exact criterion in a nested-language model through a short extension of Angluin’s argument.

**Lean formalization.** `SoundCoverage.finiteWitnessCriterion` proves the main equivalence. For necessity, a learner that succeeds on every full text must have a finite history that forces coverage on every on-target extension. For sufficiency, the least eligible index eventually gives an output between the unseen target and its ambient language. The universe is coded by natural numbers, histories allow repetitions, and the learner receives only the history. The proof works for every nonempty target, including the infinite targets in the paper. [Model](../../../lean/SolvedProblems/SoundCoverageModel.lean) · [Proof](../../../lean/SolvedProblems/SoundCoverage.lean) · [Comparator and axiom checks](../../../lean/README.md)

**Proof status.** The written draft awaits independent review. **Priority status.** A targeted literature check found the original question and related work. Priority awaits independent review.

[Read the proof (PDF)](oracle-free-sound-coverage.pdf) · [LaTeX source](oracle-free-sound-coverage.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/oracle-free-sound-coverage/citation.bib)
