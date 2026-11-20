# Dense set-valued generation under bounded displacement

Wentao Li · Prepared with assistance from OpenAI Codex

A finite-witness condition characterizes all attainable lower-density guarantees on full noiseless enumerations, including target-specific guarantees.

A smaller candidate can mimic the target while it can fill every rank deadline. The witnesses only have to rule out mimics that would leave too little of the target covered. The generator intersects candidates while checking the density demanded by each one.

**Original question.** Anay Mehrotra, Grigoris Velegkas, Xifan Yu and Felix Zhou (2025), after Theorem 7.8 in the preprint, after Theorem 39 at COLT 2026. [Primary source](https://arxiv.org/abs/2511.07417)

**Significance estimate: 55/100.** Characterizes a full range of density guarantees and extends an earlier deadline argument for exact identification.

**Proof status.** Written research draft awaiting independent review. **Priority status.** A targeted literature check found the original question and related work. Priority awaits independent review.

[Read the proof (PDF)](bounded-displacement-set-density.pdf) · [LaTeX source](bounded-displacement-set-density.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/bounded-displacement-set-density/citation.bib)

## Lean formalization

Finite witnesses characterize the lower densities attainable on full bounded-displacement texts. A generator using just the seen set attains every target-specific guarantee and always outputs infinitely many fresh points. Rational cuts express both limit inferiors. The proof allows every nondecreasing integer deadline D(t) ≥ t, including the linear deadlines in the draft. [Formal statement](../../../lean/Statements/SetDensity.lean) · [Proof](../../../lean/SolvedProblems/SetDensity.lean) · [Comparator and metadata](../../../lean/submissions/bounded-displacement-set-density/)
