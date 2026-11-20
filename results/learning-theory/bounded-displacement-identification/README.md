# Identifying languages under bounded displacement

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](bounded-displacement-identification.pdf) · [LaTeX source](bounded-displacement-identification.tex) · [Research catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/bounded-displacement-identification/citation.bib)

Finite witnesses characterize exactly which countable language families can be identified from full, noiseless enumerations of bounded displacement.

**Original question.** Anay Mehrotra, Grigoris Velegkas, Xifan Yu and Felix Zhou, 2025, question before Theorem 7.6, published before Theorem 37 at COLT 2026. [Primary source](https://arxiv.org/abs/2511.07417)

## Argument

For each target and each starting time, a finite witness must separate the target from every proper candidate sublanguage that can still fill every later rank deadline. The learner rejects hypotheses at the first missed deadline. Without a witness, an adversary can repeatedly imitate a smaller language while it finishes enumerating the true target.

## Proof and priority

The PDF gives the full argument. Independent review and Lean formalization are pending.

The source gives an impossibility example using exact enumerations. Angluin’s classical criterion treats arbitrary positive presentation order. Kleinberg and Wei study partial enumeration with a different identification goal. The theorem here is information-theoretic and assumes every target element occurs exactly once. [COLT version, Appendix D.1](https://proceedings.mlr.press/v336/mehrotra26a.html) · [Angluin](https://doi.org/10.1016/S0019-9958(80)90285-5) · [Kleinberg and Wei](https://arxiv.org/abs/2511.05295)

A search of the primary literature and follow-up work through November 19, 2026 did not identify an earlier resolution of this specific question. Priority awaits independent confirmation.

**Significance estimate: 60/100.** Gives both a learning rule and a matching adversary for every displacement factor in the exact-enumeration model. The argument extends the classical finite tell-tale method. A full resolution of the three-dimensional Navier–Stokes existence and smoothness problem sets the benchmark at 100.

## Lean formalization

A learner identifies the target on every full repetition-free text meeting the rank deadlines exactly when every target and starting time admit the paper’s finite witness. The proof covers every nondecreasing integer deadline $D(t) \ge t$, including $D(t)=\lfloor Mt\rfloor$ for $M\ge1$. The comparator checks `Displacement.finiteWitnessCriterion`. [Lean proof](../../../lean/SolvedProblems/Displacement.lean) · [Reference statements](../../../lean/Challenge.lean)
