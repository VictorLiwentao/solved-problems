# Point deletion does not determine poset substitution

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](ur-substitution-counterexample.pdf) · [LaTeX](ur-substitution-counterexample.tex) · [BibTeX](citation.bib)

## Original problem

Do the order polynomials before and after deleting a marked point determine the effect of substituting any poset at that point? [Thomas Browning, Max Hopkins and Zander Kelley, 2016](https://sites.math.washington.edu/~reu/papers/2016/thomas/Doppelganger%20Paper.pdf) (Conjecture 48 in the June 2016 manuscript).

## Result

No. Two five-element posets have equal order polynomials and isomorphic deletions. Substituting two incomparable elements gives 138 and 140 maps to three colors.

The authors gave a criterion using a family of substitutions. The counterexample tests their proposed reduction to the original poset and its deletion. [2017 preprint, Conjecture 4.11](https://arxiv.org/abs/1710.10407) · [FPSAC 2018, Conjecture 4.7](https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2018/80-Browning-Hopkins-Kelley.pdf)

**Significance 60/100.** Refutes the FPSAC conjecture with explicit factorizations and a small witness. Adjoining a top chain gives connected counterexamples of arbitrarily large size. Independent review of the proof and priority is pending.

## Reproducible check

Direct enumeration checks the original and deleted order polynomials at enough integer arguments to determine them, then returns 138 and 140 on the specified replacements. [Verification script](verify.py)
