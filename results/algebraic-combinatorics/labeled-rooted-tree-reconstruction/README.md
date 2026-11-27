# Reconstructing a labeled rooted tree from its partition enumerator

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](labeled-rooted-tree-reconstruction.pdf) · [LaTeX](labeled-rooted-tree-reconstruction.tex) · [BibTeX](citation.bib)

## Original problem

Does the partition enumerator distinguish rooted trees with arbitrary strict and weak edges? [Jean-Christophe Aval, Karimatou Djenabou and Peter R. W. McNamara, 2022](https://doi.org/10.5802/alco.273) (Conjecture 1.3, first posted in 2022).

## Result

It determines the rooted tree and the decoration of every edge. A pole at a root of unity proves branch irreducibility. A new smallest variable distinguishes a strict attachment from a weak one.

Hasebe and Tsujie treated uniformly labeled rooted trees. Aval, Djenabou and McNamara treated fair trees. Albertin, Aval and Mlodecki later treated cypress trees and fair series-parallel posets. For Stanley’s 1972 symmetry conjecture, the manuscript also shows that a decorated rooted forest has a symmetric enumerator exactly when every component has hook shape, with one weak row and one strict column meeting at its root. Either arm can be empty. [Hasebe and Tsujie](https://arxiv.org/abs/1610.03908) · [Albertin, Aval and Mlodecki](https://ajc.maths.uq.edu.au/pdf/90/ajc_v90_p341.pdf)

**Significance 72/100.** Resolves a main conjecture of the source paper for arbitrary branching and edge decorations. The same argument yields an explicit branch-recovery procedure. Independent review of the proof and priority is pending.

## Reproducible check

All 2,659 decorated rooted trees on at most seven vertices have distinct fundamental expansions at each size. The same computation tests the hook symmetry characterization from the full monomial coefficient lists. [Verification script](verify.py)
