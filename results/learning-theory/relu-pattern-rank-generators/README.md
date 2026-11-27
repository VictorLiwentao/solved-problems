# A finite generating list for shallow ReLU rank constraints

Wentao Li · Prepared with assistance from OpenAI Codex · November 20, 2026

Integer simplex grids on rational subspaces generate the entire single-combination rank ideal. Linear algebra selects its contribution to the minimal pattern-ideal generators.

**Original question.** Which finite list of integer combinations of activation blocks supplies all minimal generators arising from the rank constraints in equation (5)? [Yulia Alexandr and Guido Montúfar, 2025, Problem 35 and Theorem 34](https://arxiv.org/abs/2508.03867)

**Significance estimate.** 57/100. Constructs a finite list for every collection of shallow activation patterns. It resolves the specified family of rank constraints, while other equations may contribute to the full ideal.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 20, 2026 found the following related results. Independent priority review is pending.

Finkel, Fu and Wu gave explicit generators under conditions on the selected patterns. Alexandr and coauthors settled the two-block ideal. The interpolation argument concerns the rank family in Problem 35 for arbitrary collections.

[Read the proof (PDF)](relu-pattern-rank-generators.pdf) · [LaTeX source](relu-pattern-rank-generators.tex) · [BibTeX](citation.bib)

**Reproducible check.** Checks 16 interpolation systems and reconstructs a determinantal polynomial at a rational point outside the sample grid. [Python script](verify.py)

## Sources

- [Yulia Alexandr and Guido Montúfar (2025), Problem 35 and Theorem 34](https://arxiv.org/abs/2508.03867)
- [Finkel, Fu and Wu, Canonical activation patterns and ReLU pattern varieties](https://arxiv.org/abs/2611.20346)
- [Alexandr et al., Defining equations for two-block shallow ReLU pattern varieties](https://arxiv.org/abs/2611.23846)
