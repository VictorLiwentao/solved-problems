# solved-problems

A collection of solutions to open problems in mathematics and computer science. Each problem has its own folder with the argument, the original question, and any supporting code.

| Problem | Result | Field |
| --- | --- | --- |
| [Can a fixed number of counts distinguish permutation-packing sequences?](packing-cutoff/packing-cutoff.pdf) | For every positive integer h, two patterns of the same length and overlap agree through h counts and differ at the next one. | Enumerative combinatorics |
| [Which integer power sequences occur as permutation-packing counts?](packing-powers/packing-powers.pdf) | Every positive integer base occurs for infinitely many patterns with overlap two. For base two, each doubling corresponds to a disjoint pair whose order can be reversed. | Enumerative combinatorics |

The first entry is a research note awaiting independent review. It addresses the universal-cutoff question in [Blitvić, Kammoun, and Steingrímsson, §7, item 8](https://arxiv.org/html/2610.29846v1#S7).

The [LaTeX source](packing-cutoff/packing-cutoff.tex) gives the full construction. From the repository root, run `python3 packing-cutoff/verify.py` to reproduce the [finite checks](packing-cutoff/verify.py).

The second entry addresses the power-sequence existence statement in [§7, item 9 of the same paper](https://arxiv.org/html/2610.29846v1#S7) and also awaits independent review. Its [LaTeX source](packing-powers/packing-powers.tex) includes the construction and the base-two characterization. Run `python3 packing-powers/verify.py` to reproduce the [finite checks](packing-powers/verify.py).
