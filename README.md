# solved-problems

A collection of solutions to open problems in mathematics and computer science. Each problem has its own folder with the argument, the original question, and any supporting code.

| Problem | Result | Field |
| --- | --- | --- |
| [Can a fixed number of counts distinguish permutation-packing sequences?](packing-cutoff/packing-cutoff.pdf) | For every positive integer h, two patterns of the same length and overlap agree through h counts and differ at the next one. | Enumerative combinatorics |

The first entry is a research note awaiting independent review. It addresses the universal-cutoff question in [Blitvić, Kammoun, and Steingrímsson, §7, item 8](https://arxiv.org/html/2610.29846v1#S7).

The [LaTeX source](packing-cutoff/packing-cutoff.tex) gives the full construction. From the repository root, run `python3 packing-cutoff/verify.py` to reproduce the [finite checks](packing-cutoff/verify.py).
