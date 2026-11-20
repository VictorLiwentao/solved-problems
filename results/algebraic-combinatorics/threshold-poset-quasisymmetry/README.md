# Which threshold-labeled posets are quasisymmetric?

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](threshold-poset-quasisymmetry.pdf) · [LaTeX](threshold-poset-quasisymmetry.tex) · [BibTeX](citation.bib)

## Original problem

For which posets with arbitrary weakly increasing edge thresholds is the tableau enumerator quasisymmetric? [Thomas Lam and Pavlo Pylyavskyy, 2006](https://arxiv.org/abs/math/0609249) (Problem 7.1).

## Result

A finite list of forbidden comparison patterns characterizes the labelings of each fixed poset. Every nonzero quasisymmetric output has a strict/weak comparison model after deleting inactive edges. Recognition is decidable for Presburger-definable thresholds and undecidable for general computable thresholds.

Lam and Pylyavskyy established sufficiency for ordinary strict/weak edges and a component-factorization theorem. The criterion here permits every increasing threshold in their definition. It uses finite comparison patterns even when deciding which patterns occur is uncomputable.

**Significance 61/100.** Gives a structural restriction on all possible outputs and a recognition theorem for the full class of thresholds in a 2006 problem. The finite obstruction lists can be large. Independent review of the proof and priority is pending.

Every failure has a certificate involving at most twice as many distinct colors as vertices. For one edge, the paper also classifies the threshold function itself.
