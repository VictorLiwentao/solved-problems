# A process criterion for universal multiclass online learning

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](universal-multiclass-processes.pdf) · [LaTeX source](universal-multiclass-processes.tex) · [Finite verification](verify.py) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/universal-multiclass-processes/citation.bib)

Hanneke and Wang asked which input processes admit online learning for a specified concept class when the labels can be any natural numbers. The learner must have vanishing average error almost surely on every target whose finite observed prefixes are realizable. Their example shows why input-only experts can miss information revealed by an earlier label. [ICML 2026, Appendix D.1, Open Question 1](https://proceedings.mlr.press/v306/hanneke26b.html)

## The criterion

Choose finitely many target-labelled input prefixes and weight their positions using the probabilities supplied by the input process. Group positions with the same observed history, including the current input. In each group, count the weight assigned to all labels except the most frequent next label. This measures how much one prediction must lose on that test.

For each error tolerance, the targets must admit a countable cover by subfamilies. On each subfamily the largest such test loss must fall within the tolerance as the minimum tested horizon grows. This is necessary and sufficient under the countable input and label assumptions of the original question. The PDF specifies the permissible weights and gives a finite witness for any strict violation of a subfamily bound. It also gives the **exact optimal worst-target expected limit superior of average error**, with a randomized learner attaining it. At value zero a deterministic learner suffices.

With all functions available as targets and infinitely many labels, the value has a simpler form. It is the expected limit superior of the fraction of distinct input points seen so far. The proof includes a process whose expected fraction at each fixed time vanishes, yet long bursts of new inputs rule out almost-sure learning.

## Realizable and agnostic learning can differ maximally

On one fixed sequence of inputs the realizable mistake count can grow arbitrarily slowly, while agnostic regret tends to **one**. A label at the start of each block encodes its remaining labels. A realizable learner decodes it. Corrupting only those opening labels costs the target comparator a vanishing fraction of mistakes and can leave every subsequent prediction essentially unconstrained. The note gives a separate criterion for agnostic randomized prediction.

## Proof and priority

The general proof combines finite minimax duality, compactness for countably many label probabilities, and aggregation of countably many prediction rules. The checker independently evaluates primal prediction tables and dual weighted-prefix witnesses on 766 finite trees. The PDF proves the infinite-horizon characterization. The finite tests can use the probabilities of the given process and extension to a target subfamily, so the characterization is information-theoretic.

The binary static-expert criterion, the full-class reduction to binary learning, and classical expert aggregation are credited in the paper. A review of the published question, its citing work and earlier process-prediction results found no matching characterization for arbitrary multiclass concept classes. Independent mathematical review is pending. [Binary process characterization](https://arxiv.org/abs/2501.08551) · [Full-class reduction](https://proceedings.mlr.press/v178/blanchard22a.html) · [Related statistical prediction criteria](https://jmlr.org/papers/v11/ryabko10a.html)

## Lean formalization

For every diverging nondecreasing mistake budget there is a closed class on a deterministic process that meets the budget on all realizable streams. Every randomized learner has a fixed stream on which regret tends to one almost surely. This covers the separation proposition. The paper’s general process criteria are separate. [Statement](../../../lean/Statements/ProcessSeparation.lean) · [Proof](../../../lean/SolvedProblems/ProcessSeparation.lean) · [Comparator and source alignment](../../../lean/submissions/universal-multiclass-processes/)
