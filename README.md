# solved-problems

A collection of solutions to open problems in mathematics and computer science. Each problem has its own folder with the argument, the original question, and any supporting code.

| Problem | Result | Field |
| --- | --- | --- |
| [Can a fixed number of counts distinguish permutation-packing sequences?](packing-cutoff/packing-cutoff.pdf) | For every positive integer h, two patterns of the same length and overlap agree through h counts and differ at the next one. | Enumerative combinatorics |
| [Which integer power sequences occur as permutation-packing counts?](packing-powers/packing-powers.pdf) | Every positive integer base occurs for infinitely many patterns with overlap two. For base two, each doubling corresponds to a disjoint pair whose order can be reversed. | Enumerative combinatorics |
| [Which packing posets have a separator?](packing-separators/packing-separators.pdf) | A prefix–suffix rank test decides the question for every number of copies. For overlap m the answer stabilizes by 6(m+1)+1 copies. | Enumerative combinatorics |
| [Can every requested overlap and length realize the Catalan numbers?](packing-catalan-lift/packing-catalan-lift.pdf) | A lift adds a forced chain to the packing poset and preserves every count. Applying it to 1324 gives Catalan representatives for every m ≥ 3 and K ≥ 2m. | Enumerative combinatorics |

The first entry is a research note awaiting independent review. It addresses the universal-cutoff question in [Blitvić, Kammoun, and Steingrímsson, §7, item 8](https://arxiv.org/html/2610.29846v1#S7).

The [LaTeX source](packing-cutoff/packing-cutoff.tex) gives the full construction. From the repository root, run `python3 packing-cutoff/verify.py` to reproduce the [finite checks](packing-cutoff/verify.py).

The second entry addresses the power-sequence existence statement in [§7, item 9 of the same paper](https://arxiv.org/html/2610.29846v1#S7) and also awaits independent review. Its [LaTeX source](packing-powers/packing-powers.tex) includes the construction and the base-two characterization. Run `python3 packing-powers/verify.py` to reproduce the [finite checks](packing-powers/verify.py).

The [separator note](packing-separators/packing-separators.tex) answers [§7, item 5](https://arxiv.org/html/2610.29846v1#S7) and proves the proposed overlap-two family. Run `python3 packing-separators/verify.py` to check the [decision procedure](packing-separators/separators.py). The note awaits independent review.

The [Catalan note](packing-catalan-lift/packing-catalan-lift.tex) answers the Catalan portion of [§7, item 6](https://arxiv.org/html/2610.29846v1#S7). Run `python3 packing-catalan-lift/verify.py` to reproduce the [order-relation checks](packing-catalan-lift/verify.py). The note awaits independent review.
