# A successful regularizer with infinite selected disagreement dimension

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](selected-disagreement-dimension.pdf) · [LaTeX source](selected-disagreement-dimension.tex) · [Finite check](verify.py) · [Research catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/selected-disagreement-dimension/citation.bib)

A fixed regularizer PAC learns even though hypotheses it actually selects can shatter arbitrarily large sets of disagreements with one target.

**Original question.** Julian Asilis, Shaddin Dughmi, Vatsal Sharan, Alec Sun, Shang-Hua Teng and Chang Wang, 2026, question before Proposition 5.10. [Primary source](https://arxiv.org/abs/2608.26516v2)

## Argument

Give each finite disagreement set its own marker. One labeled marker makes the matching hypothesis the unique minimizer. On any sample, a wrong selection is either a fixed default or can be named by a single observed marker. Conditioning on its position leaves the other examples independent and gives a distribution-free error bound.

## Proof and priority

The PDF gives the full argument. Independent review and Lean formalization are pending.

Example 5.8 of the source treats all lower-ranked hypotheses. Definition 5.9 restricts to hypotheses actually selected on some sample. Here a one-point sample selects each witness uniquely. Earlier multiclass ERM separations already use revealing labels. The conclusion concerns the particular successful regularizer. [Daniely, Sabato, Ben-David and Shalev-Shwartz](https://jmlr.org/papers/v16/daniely15a.html)

A search of the primary literature and follow-up work through November 19, 2026 did not identify an earlier resolution of this specific question. Priority awaits independent confirmation.

**Significance estimate: 57/100.** Gives a negative answer to a proposed converse for hard structural risk minimization. It distinguishes the complexity of all possible selections from the candidates one sample can name. A full resolution of the three-dimensional Navier–Stokes existence and smoothness problem sets the benchmark at 100.

## Lean formalization

The fixed regularizer has a unique consistent minimum on every realizable sample, and its selections shatter arbitrarily large disagreement sets. The full IID probability of error above ε is at most 2(1−ε)ᵐ + m(1−ε)ᵐ⁻¹. The confidence bound tends to zero uniformly over targets and countable input laws. [Formal statement](../../../lean/Statements/SelectedDisagreement.lean) · [Proof](../../../lean/SolvedProblems/SelectedProbability.lean) · [Comparator and metadata](../../../lean/submissions/selected-disagreement-dimension/)
