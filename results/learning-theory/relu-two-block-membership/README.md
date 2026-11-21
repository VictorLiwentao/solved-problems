# Exact representability of two ReLU activation blocks

Wentao Li · Prepared with assistance from OpenAI Codex · November 20, 2026

A finite linear-algebra test decides exact membership, including at boundary points. For rational block data, complex representability already gives rational factors.

**Original question.** Can one decide whether prescribed linear maps on two selected activation patterns belong to the pattern-map image using finite kernel and generic-rank tests? [Yulia Alexandr, Moritz Grillo, Thiago Holleben, Guido Montúfar and Teresa Yu, 2026, Section 2.2, criterion after Proposition 4](https://arxiv.org/abs/2611.23846)

**Significance estimate.** 65/100. Addresses exact factorization for arbitrary block sizes and overlap counts. The field-of-definition consequence distinguishes representability from merely satisfying closure equations.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 20, 2026 found the following related results. Independent priority review is pending.

The source already proves the defining ideal and characterizes closedness. The draft uses the classical finite classification of triples of subspaces to turn exact membership for individual pairs into linear equations and determinant tests.

[Read the proof (PDF)](relu-two-block-membership.pdf) · [LaTeX source](relu-two-block-membership.tex) · [BibTeX](citation.bib)

**Reproducible check.** Includes a rational-input membership routine and checks 72 scalar cases and seven matrix cases. Requires SymPy. [Python script](verify.py)

## Sources

- [Yulia Alexandr, Moritz Grillo, Thiago Holleben, Guido Montúfar and Teresa Yu (2026), Section 2.2, criterion after Proposition 4](https://arxiv.org/abs/2611.23846)
- [Alexandr and Montúfar, Constraining the outputs of ReLU neural networks](https://arxiv.org/abs/2508.03867)
- [Enomoto and Watatani, Relative position of three subspaces in a Hilbert space](https://arxiv.org/abs/1407.6852)
