# Mathematical research notes

**Wentao Li** · [GitHub profile](https://github.com/VictorLiwentao)

Proofs and counterexamples in combinatorics and graph theory. Each entry links to the original question, a downloadable proof, its LaTeX source, and any accompanying code. The twelve notes are AI-assisted research drafts awaiting independent review.

[Graph theory](#graph-theory) · [Algebraic combinatorics](#algebraic-combinatorics) · [Lattice paths](#lattice-paths) · [Permutation patterns](#permutation-patterns)

[Run the checks](docs/verification.md) · [Lean formalizations](lean/README.md)

## Graph theory

| Note | Main result | Proof |
| --- | --- | --- |
| [Random graphs and independence roots](results/graph-theory/random-graph-independence-roots/) | For every fixed edge probability $0<p<1$, the probability of a right-half-plane root has a positive limit superior. At $p=1/2$ it is at least $1-e^{-1/4}$. | [PDF](results/graph-theory/random-graph-independence-roots/random-graph-independence-roots.pdf) |
| [Map graphs on surfaces](results/graph-theory/surface-map-cliques/) | The worst-case clique-cover degeneracy on a surface of Euler genus $g$ grows as $\Theta(1+\sqrt g)$. | [PDF](results/graph-theory/surface-map-cliques/surface-map-cliques.pdf) |

## Algebraic combinatorics

| Note | Main result | Proof |
| --- | --- | --- |
| [Large-genus Hurwitz roots](results/algebraic-combinatorics/hurwitz-root-asymptotics/) | For every fixed cycle profile, the first correction gives the direction and exponential rate at which each moving root approaches its limit. | [PDF](results/algebraic-combinatorics/hurwitz-root-asymptotics/hurwitz-root-asymptotics.pdf) |
| [Parking-function excedances](results/algebraic-combinatorics/parking-excedances/) | An exact integer certificate at $n=17$ disproves the real-rootedness conjecture. | [PDF](results/algebraic-combinatorics/parking-excedances/parking-excedances.pdf) |
| [Type-D Eulerian polynomials](results/algebraic-combinatorics/type-d-interlacing/) | For every $q>0$, the zeros at consecutive ranks strictly interlace from rank three onward. | [PDF](results/algebraic-combinatorics/type-d-interlacing/type-d-interlacing.pdf) |

## Lattice paths

| Note | Main result | Proof |
| --- | --- | --- |
| [Peaks in Fuss–Dyck paths](results/lattice-paths/fuss-dyck-peaks/) | Fixing the number of north steps and peaks fixes all zeros of the $NNE$ counting polynomial, with multiplicities, across all Fuss slopes. | [PDF](results/lattice-paths/fuss-dyck-peaks/fuss-dyck-peaks.pdf) |
| [Runs and returns in rational Dyck paths](results/lattice-paths/rational-dyck-run-return/) | A determinant formula counts paths with prescribed returns and either run statistic for every width at least the height. | [PDF](results/lattice-paths/rational-dyck-run-return/rational-dyck-run-return.pdf) |

## Permutation patterns

These five notes address questions in §7 of the same paper by Blitvić, Kammoun, and Steingrímsson. The item numbers below follow the authors’ list. [Original questions](https://arxiv.org/html/2610.29846v1#S7)

| Item | Note | Main result | Proof |
| --- | --- | --- | --- |
| 2 | [Factorization with variable overlaps](results/permutation-patterns/packing-factorization/) | A finite criterion decides whether counts split at a designated overlap and gives a witness whenever they fail to split. | [PDF](results/permutation-patterns/packing-factorization/packing-factorization.pdf) |
| 5 | [Separators in packing posets](results/permutation-patterns/packing-separators/) | At overlap $m$, the answer for any number of copies is determined by testing up to $6(m+1)+1$ copies. | [PDF](results/permutation-patterns/packing-separators/packing-separators.pdf) |
| 6 | [Catalan packing representatives](results/permutation-patterns/packing-catalan-lift/) | A count-preserving lift gives Catalan representatives for every overlap $m\ge 3$ and length $K\ge 2m$. | [PDF](results/permutation-patterns/packing-catalan-lift/packing-catalan-lift.pdf) |
| 8 | [The universal packing cutoff](results/permutation-patterns/packing-cutoff/) | Two patterns can have arbitrarily many initial counts in common and differ at the very next count. | [PDF](results/permutation-patterns/packing-cutoff/packing-cutoff.pdf) |
| 9 | [Integer powers as packing counts](results/permutation-patterns/packing-powers/) | Every positive integer base occurs for infinitely many patterns with overlap two. | [PDF](results/permutation-patterns/packing-powers/packing-powers.pdf) |

## Verification and citation

Eleven notes have runnable Python checks. The surface map-graph note has a theoretical proof. Lean coverage is currently **0 of 12 main statements**. [Verification guide](docs/verification.md) · [Lean status and scope](lean/README.md)

To cite an individual note, use Wentao Li and the title from its PDF, link to the note at a specific commit (press **Y** on its GitHub page), and cite the publication that posed the question. For older citations, all ten original paths are available in the [snapshot before the reorganization](https://github.com/VictorLiwentao/solved-problems/tree/f5bcb6167a737e6a70c1965b3635db963adc792c).
