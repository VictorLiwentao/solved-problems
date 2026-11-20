# A descent-preserving injection for mixed caterpillar inequalities

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](mixed-caterpillar-positivity.pdf) · [LaTeX](mixed-caterpillar-positivity.tex) · [BibTeX](citation.bib)

## Original problem

Can one explain the fundamental-positivity comparison for mixed caterpillars displayed in equation (7.4)? [Nathan R. T. Lesnevich and Peter R. W. McNamara, 2020](https://arxiv.org/abs/2006.10087) (Section 7(3), equation (7.4)).

## Result

A descent-preserving injection explains the comparison and extends it to any attached labeled poset whose largest label lies at a maximal element.

The authors exhibited the five-vertex inequality. Their 2025 correction concerns the hypotheses of a different caterpillar theorem. [Corrected paper and diagram](https://www.linux.bucknell.edu/~pm040/Papers/P_partition_positivity.pdf) · [Published correction](https://doi.org/10.1007/s00026-025-00744-3)

**Significance 46/100.** Gives a uniform explanation of the authors’ displayed inequality. The result addresses that question and allows side posets with arbitrary internal structure. Independent review of the proof and priority is pending.

## Reproducible check

All 546 eligible side orders with vertex labelings enumerated through four vertices pass independent checks of the injection, including validity of the output extension and preservation of every descent. [Verification script](verify.py)
