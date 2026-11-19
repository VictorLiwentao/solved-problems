# Lean formalizations

[Result catalogue](../README.md) · [Python verification](../docs/verification.md)

**Lean covers 0 of 28 main statements.** The collection currently contains written proofs and Python checks. This directory is reserved for the shared Lean 4 project when the first proof is contributed.

| Coverage | What a reader can verify |
| --- | --- |
| Partial | A named theorem checks a specified lemma, special case, or certificate. The entry identifies the remaining mathematical step. |
| Complete | A named theorem checks the note’s main statement with its stated hypotheses. The entry points to the declaration, reproducible build, and axiom report. |

For the first contribution, place the Lake project here and commit the toolchain and dependency pins used for its build. Link the Lean module from the corresponding result page. In this index record the note, theorem name, checked scope, any extra hypotheses, and the commands to build it and inspect `#print axioms` for that declaration.

For example, the parking-function note gives three natural milestones. Lean could first check the signed integer identity, then show that the counted coefficients describe the parking-function polynomial, then deduce that the polynomial has a nonreal zero. The identity alone would earn a **partial** entry. [Parking-function statement and proof](../results/algebraic-combinatorics/parking-excedances/)
