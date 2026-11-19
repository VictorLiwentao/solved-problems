# solved-problems

A collection of solutions to open problems in mathematics and computer science. Each problem has its own folder with the argument, the original question, and any supporting code.

| Problem | Result | Field |
| --- | --- | --- |
| [Can a fixed number of counts distinguish permutation-packing sequences?](packing-cutoff/packing-cutoff.pdf) | For every positive integer h, two patterns of the same length and overlap agree through h counts and differ at the next one. | Enumerative combinatorics |
| [Which integer power sequences occur as permutation-packing counts?](packing-powers/packing-powers.pdf) | Every positive integer base occurs for infinitely many patterns with overlap two. For base two, each doubling corresponds to a disjoint pair whose order can be reversed. | Enumerative combinatorics |
| [Which packing posets have a separator?](packing-separators/packing-separators.pdf) | A prefix–suffix rank test decides the question for every number of copies. For overlap m the answer stabilizes by 6(m+1)+1 copies. | Enumerative combinatorics |
| [Can every requested overlap and length realize the Catalan numbers?](packing-catalan-lift/packing-catalan-lift.pdf) | A lift adds a forced chain to the packing poset and preserves every count. Applying it to 1324 gives Catalan representatives for every m ≥ 3 and K ≥ 2m. | Enumerative combinatorics |
| [Do consecutive type-D Eulerian polynomials interlace?](type-d-interlacing/type-d-interlacing.pdf) | For every positive q the zeros strictly alternate from rank three onward, with one explicit rank-two exception. | Algebraic combinatorics |
| [Are the Fuss–Dyck peak polynomials real-rooted?](fuss-dyck-peaks/fuss-dyck-peaks.pdf) | Once the number of north steps and peaks is fixed, all Fuss parameters give the same zeros, including multiplicities. | Algebraic and enumerative combinatorics |
| [How many rational Dyck paths have specified run and return counts?](rational-dyck-run-return/rational-dyck-run-return.pdf) | A binomial determinant formula gives the joint distribution with either run statistic for every width at least the height. | Enumerative combinatorics |
| [When do counts with varying permutation overlaps factor?](packing-factorization/packing-factorization.pdf) | A finite test characterizes all allowed overlap alphabets and splitting overlaps. On failure it constructs a word violating the product formula. | Enumerative combinatorics |
| [How large is clique-cover degeneracy for map graphs on surfaces?](surface-map-cliques/surface-map-cliques.pdf) | The worst case on surfaces of Euler genus g grows as Θ(1 + √g). An n-vertex map graph has a balanced separator covered by O(√((g+1)n)) cliques. | Topological graph theory |
| [Are parking-function excedance polynomials always real-rooted?](parking-excedances/parking-excedances.pdf) | No. At n = 17 the polynomial violates the Laguerre inequality at −1/5. Two independent integer counts certify the sign. | Algebraic combinatorics |

The first entry is a research note awaiting independent review. It addresses the universal-cutoff question in [Blitvić, Kammoun, and Steingrímsson, §7, item 8](https://arxiv.org/html/2610.29846v1#S7).

The [LaTeX source](packing-cutoff/packing-cutoff.tex) gives the full construction. From the repository root, run `python3 packing-cutoff/verify.py` to reproduce the [finite checks](packing-cutoff/verify.py).

The second entry addresses the power-sequence existence statement in [§7, item 9 of the same paper](https://arxiv.org/html/2610.29846v1#S7) and also awaits independent review. Its [LaTeX source](packing-powers/packing-powers.tex) includes the construction and the base-two characterization. Run `python3 packing-powers/verify.py` to reproduce the [finite checks](packing-powers/verify.py).

The [separator note](packing-separators/packing-separators.tex) answers [§7, item 5](https://arxiv.org/html/2610.29846v1#S7) and proves the proposed overlap-two family. Run `python3 packing-separators/verify.py` to check the [decision procedure](packing-separators/separators.py). The note awaits independent review.

The [Catalan note](packing-catalan-lift/packing-catalan-lift.tex) answers the Catalan portion of [§7, item 6](https://arxiv.org/html/2610.29846v1#S7). Run `python3 packing-catalan-lift/verify.py` to reproduce the [order-relation checks](packing-catalan-lift/verify.py). The note awaits independent review.

The [type-D proof](type-d-interlacing/type-d-interlacing.tex) addresses the consecutive-rank question listed in [SymCat](https://www.symmetricfunctions.com/realRootedOpenProblems.htm). Its [verifier](type-d-interlacing/verify.py) uses SymPy to certify interlacing by exact polynomial arithmetic. The note awaits independent review.

The [Fuss–Dyck proof](fuss-dyck-peaks/fuss-dyck-peaks.tex) answers [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedCatalan.htm). Run the [verifier](fuss-dyck-peaks/verify.py) to compare the formula with direct path counts. The note awaits independent review.

The [joint run–return formula](rational-dyck-run-return/rational-dyck-run-return.tex) answers an enumeration question in [Dai, Fu and Qiu, §5](https://arxiv.org/abs/2503.20155). The [implementation](rational-dyck-run-return/run_return.py) has a [direct enumerative check](rational-dyck-run-return/verify.py). The note awaits independent review.

The [variable-overlap proof](packing-factorization/packing-factorization.tex) addresses [§7, item 2 of the packing paper](https://arxiv.org/html/2610.29846v1#S7). Its [implementation](packing-factorization/factorization.py) and [linear-extension verifier](packing-factorization/verify.py) use the Python standard library. The note awaits independent review.

The [surface map-graph proof](surface-map-cliques/surface-map-cliques.tex) answers [Dallard et al., Question 7.3](https://arxiv.org/abs/2506.12424) and establishes the asymptotic lower bound. It awaits independent review.

The [parking-function counterexample](parking-excedances/parking-excedances.tex) disproves [Alexandersson’s excedance conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm). The [integer certificate](parking-excedances/verify.py) checks the labeled-subset and Ferrers-board counts independently. The note awaits independent review.
