# A communication obstruction to optimal noise rates in conditional disclosure of secrets

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](conditional-disclosure-noise-bound.pdf) · [LaTeX](conditional-disclosure-noise-bound.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/conditional-disclosure-noise-bound/citation.bib)

The graph bound can strictly exceed the best possible linear noise rate. On the Li–Sun graph it gives 4/7, while every linear scheme has rate at most 14/25. An entropy argument relates noise to communication along every unqualified path and applies to nonlinear messages as well.

**Original question.** Zhou Li, Siyan Qin, Xiang Zhang, Jihao Fan, Haiqiang Chen and Giuseppe Caire, 2025. [§VIII, achievability of the linear converse in Theorem 2 (full version of the ISIT 2025 work)](https://arxiv.org/abs/2510.22671)

## Argument

A single unqualified edge reveals no secret. Each further message on the path can supply at most the shared noise entropy minus the preceding message entropy in additional information. The endpoints together recover the secret. Combining the resulting bound with Li and Sun’s exact communication capacity gives a strict gap.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The check enumerates the paths and connected covers on the published graph and verifies both bounds exactly. [Run the check](verify.py)

**Priority.** Independent priority review is pending. The linear path inequality already appears as equation (80) in the source. This note gives an entropy proof for arbitrary deterministic encoders and combines it with the sharper Li–Sun communication theorem. [Li–Sun, Figure 6 and Theorem 3](https://arxiv.org/abs/2106.04483)

**Significance · 61/100.** Answers the universal achievability question and gives a path inequality without a linearity hypothesis. The strict numerical gap uses a previously established linear communication converse. [Scoring benchmark](../../../docs/scores-and-sources.md)
