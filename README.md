# Mathematical research notes

[**Wentao Li**](https://github.com/VictorLiwentao) · Prepared with assistance from **OpenAI GPT-6.2 Astra**.

Thirty-six research drafts across eight fields, each with the original question, a proposed proof or counterexample, and downloadable LaTeX and PDF files. The drafts await independent review.

![The two-state Busy Beaver on a blank tape. Its head visits cells 0, 1, 0, −1, −2, −1, and 0, leaving four ones when it halts at step six.](docs/figures/two-state-busy-beaver.svg)

*Six steps is the runtime record for a two-state, two-symbol Turing machine. How much information does one record give about the next?* [Read the Busy Beaver advice note](results/computability/prefix-free-busy-beaver-advice/)

## Browse the collection

| Foundations and learning theory | Combinatorics and graph theory |
| --- | --- |
| [Computability](#computability) · 4 notes<br>[Set theory](#set-theory) · 2 notes<br>[Finite model theory](#finite-model-theory) · 6 notes<br>[Learning theory](#learning-theory) · 9 notes | [Graph theory](#graph-theory) · 3 notes<br>[Algebraic combinatorics](#algebraic-combinatorics) · 3 notes<br>[Lattice paths](#lattice-paths) · 2 notes<br>[Permutation patterns](#permutation-patterns) · 7 notes |

[Reproduce the 32 Python checks](docs/verification.md) · [Lean formalization status](lean/README.md) · [Cite a note](#verification-and-citation)

## Foundations of mathematics

### Computability

| Note | Main result | Proof |
| --- | --- | --- |
| [Splitting the Busy Beaver runtime](results/computability/splitting-busy-beaver/) | Two records each outgrow every computable function. Neither can bound the other, and their maximum is exactly Busy Beaver. Even ZFC given every other colour’s record faces an eventual independence threshold. | [PDF](results/computability/splitting-busy-beaver/splitting-busy-beaver.pdf) |
| [The Lazy Beaver runtime spectrum](results/computability/lazy-beaver-runtime-spectrum/) | Even across all initial tapes, the number of distinct runtime profiles is exponentially smaller than the number of graphically accessible tables. | [PDF](results/computability/lazy-beaver-runtime-spectrum/lazy-beaver-runtime-spectrum.pdf) |
| [Advice between Busy Beaver records](results/computability/prefix-free-busy-beaver-advice/) | For optimal prefix-free programs, constant advice suffices at every length. In the classical state-count model the one-step cost averages $\Theta(\log N)$ below $N$ states. | [PDF](results/computability/prefix-free-busy-beaver-advice/prefix-free-busy-beaver-advice.pdf) |
| [Busy Beaver bouncer tapes](results/computability/bouncer-tape-inclusion/) | An exact linear-time inclusion test for aligned tape formulas with separated repeaters and equal repeater counts. An empty-wall counterexample separates two proposed conditions. | [PDF](results/computability/bouncer-tape-inclusion/bouncer-tape-inclusion.pdf) |

### Set theory

| Note | Main result | Proof |
| --- | --- | --- |
| [Hajnal’s product theorem without the ultrafilter lemma](results/set-theory/hajnal-products-without-choice/) | One model satisfies every finite-color product theorem while choice for pairs fails. In pure ZF with dependent choice, two countably chromatic graphs can have a bipartite product. | [PDF](results/set-theory/hajnal-products-without-choice/hajnal-products-without-choice.pdf) |
| [Choice and distinguishing vertex colorings](results/set-theory/choice-and-distinguishing-colorings/) | Over ZF, the axiom of choice is equivalent to the existence of a distinguishing chromatic number for every infinite connected graph, even when restricted to rigid graphs. | [PDF](results/set-theory/choice-and-distinguishing-colorings/choice-and-distinguishing-colorings.pdf) |

### Finite model theory

| Note | Main result | Proof |
| --- | --- | --- |
| [A universal spectrum on planar graphs](results/finite-model-theory/universal-planar-spectrum/) | One sentence about connected subcubic graphs represents every first-order spectrum. The reduction selects tuples using only equality on the input set. | [PDF](results/finite-model-theory/universal-planar-spectrum/universal-planar-spectrum.pdf) |
| [Which slow sequences count labelled finite models?](results/finite-model-theory/labelled-model-counts/) | The primes cannot occur as the labelled counts. Every first-order or monadic second-order count bounded by a fixed exponential eventually has an exact exponential-polynomial formula. | [PDF](results/finite-model-theory/labelled-model-counts/labelled-model-counts.pdf) |
| [A zero-one law for two-connected graphs](results/finite-model-theory/two-connected-graph-zero-one-law/) | Every monadic second-order sentence has an exponential zero-one limit. The almost-sure theory is decidable exactly at bounded treewidth. | [PDF](results/finite-model-theory/two-connected-graph-zero-one-law/two-connected-graph-zero-one-law.pdf) |
| [Three gaps in logical limit laws](results/finite-model-theory/three-gaps-in-graph-limit-laws/) | In every proper addable minor-closed graph class, at least three gaps separate the attainable limiting probabilities. Forests attain the sharp generating-function bound. | [PDF](results/finite-model-theory/three-gaps-in-graph-limit-laws/three-gaps-in-graph-limit-laws.pdf) |
| [Labeled compositions and limiting probabilities](results/finite-model-theory/labeled-composition-limit-law/) | Every monadic second-order sentence has an exponentially convergent probability. An explicit spectrum characterizes the limits and is already attained by first-order sentences. | [PDF](results/finite-model-theory/labeled-composition-limit-law/labeled-composition-limit-law.pdf) |
| [Failure of a first-order convergence law](results/finite-model-theory/permutation-limit-counterexample/) | In a proper hereditary permutation class, the probability that the two orders share a least element tends to one along selected sizes and to zero at the immediately following sizes. | [PDF](results/finite-model-theory/permutation-limit-counterexample/permutation-limit-counterexample.pdf) |

## Learning theory

| Note | Main result | Proof |
| --- | --- | --- |
| [Private generation on uncountable collections](results/learning-theory/private-generation-uncountable/) | One observation suffices for ordinary uniform generation, yet pure privacy can drive worst-case eventual success to zero. For a second collection, optimal success equals the additive privacy allowance. | [PDF](results/learning-theory/private-generation-uncountable/private-generation-uncountable.pdf) |
| [Lists and finite partitions in uniform generation](results/learning-theory/uniform-list-generation/) | Two guesses suffice after one example, yet every finite partition has a part that defeats single-word generation. A Ramsey construction gives the separation at every list length. | [PDF](results/learning-theory/uniform-list-generation/uniform-list-generation.pdf) |
| [A process criterion for multiclass online learning](results/learning-theory/universal-multiclass-processes/) | Weighted tests on shared histories characterize learning with infinitely many labels. On a fixed process, sparse corruptions can drive regret to one even when realizable mistakes grow arbitrarily slowly. | [PDF](results/learning-theory/universal-multiclass-processes/universal-multiclass-processes.pdf) |
| [Private language identification](results/learning-theory/private-language-identification/) | Private identification from repetition-free texts is possible exactly when distinct languages share finitely many words. The largest common overlap determines the optimal success probability for lists of guesses. | [PDF](results/learning-theory/private-language-identification/private-language-identification.pdf) |
| [Private list learning at both dimensions one](results/learning-theory/private-list-learning-on-products/) | Two necessary conditions for private list learning fail together at their minimum nonzero values. One online mistake suffices, yet every label can be needed for private prediction. | [PDF](results/learning-theory/private-list-learning-on-products/private-list-learning-on-products.pdf) |
| [Finite evidence for computable online learning](results/learning-theory/computable-online-learning-certificates/) | Finite evidence characterizes learnability for arbitrary classes and the exact uniform mistake budget. Finding a defeating stream can require computing a path through any prescribed recursive tree. | [PDF](results/learning-theory/computable-online-learning-certificates/computable-online-learning-certificates.pdf) |
| [An unbounded compactness gap for agnostic learning](results/learning-theory/agnostic-compactness-gap/) | Every finite part has vanishing excess error at a common rate, yet the full class has error one at every sample size. The first possible density for this failure is $\aleph_\omega$. | [PDF](results/learning-theory/agnostic-compactness-gap/agnostic-compactness-gap.pdf) |
| [When the previous guess cannot remember a language](results/learning-theory/last-guess-identification/) | A nested family of regular languages with singleton telltales defeats every last-guess learner, even on repetition-free texts. One extra bit restores exact identification. | [PDF](results/learning-theory/last-guess-identification/last-guess-identification.pdf) |
| [The halting threshold for prompted language generation](results/learning-theory/prompted-generation-oracle/) | Two polynomial-time-checkable languages already require a halting oracle for eventual prompt completion. A bound on answer length characterizes the countable families that admit a generator. | [PDF](results/learning-theory/prompted-generation-oracle/prompted-generation-oracle.pdf) |

## Combinatorics and graph theory

### Graph theory

| Note | Main result | Proof |
| --- | --- | --- |
| [Unbounded fragments in unlabelled random graphs](results/graph-theory/unlabelled-fragment-counterexample/) | One bridge-addable class has nearly linear expected fragment size infinitely often, even with finite exponential growth. This disproves two conjectured bounds. | [PDF](results/graph-theory/unlabelled-fragment-counterexample/unlabelled-fragment-counterexample.pdf) |
| [Random graphs and independence roots](results/graph-theory/random-graph-independence-roots/) | For every fixed edge probability $0<p<1$, the probability of a right-half-plane root has a positive limit superior. At $p=1/2$ it is at least $1-e^{-1/4}$. | [PDF](results/graph-theory/random-graph-independence-roots/random-graph-independence-roots.pdf) |
| [Map graphs on surfaces](results/graph-theory/surface-map-cliques/) | The worst-case clique-cover degeneracy on a surface of Euler genus $g$ grows as $\Theta(1+\sqrt g)$. | [PDF](results/graph-theory/surface-map-cliques/surface-map-cliques.pdf) |

### Algebraic combinatorics

| Note | Main result | Proof |
| --- | --- | --- |
| [Large-genus Hurwitz roots](results/algebraic-combinatorics/hurwitz-root-asymptotics/) | For every fixed cycle profile, the first correction gives the direction and exponential rate at which each moving root approaches its limit. | [PDF](results/algebraic-combinatorics/hurwitz-root-asymptotics/hurwitz-root-asymptotics.pdf) |
| [Parking-function excedances](results/algebraic-combinatorics/parking-excedances/) | An exact integer certificate at $n=17$ disproves the real-rootedness conjecture. | [PDF](results/algebraic-combinatorics/parking-excedances/parking-excedances.pdf) |
| [Type-D Eulerian polynomials](results/algebraic-combinatorics/type-d-interlacing/) | For every $q>0$, the zeros at consecutive ranks strictly interlace from rank three onward. | [PDF](results/algebraic-combinatorics/type-d-interlacing/type-d-interlacing.pdf) |

### Lattice paths

| Note | Main result | Proof |
| --- | --- | --- |
| [Peaks in Fuss–Dyck paths](results/lattice-paths/fuss-dyck-peaks/) | Fixing the number of north steps and peaks fixes all zeros of the $NNE$ counting polynomial, with multiplicities, across all Fuss slopes. | [PDF](results/lattice-paths/fuss-dyck-peaks/fuss-dyck-peaks.pdf) |
| [Runs and returns in rational Dyck paths](results/lattice-paths/rational-dyck-run-return/) | A determinant formula counts paths with prescribed returns and either run statistic for every width at least the height. | [PDF](results/lattice-paths/rational-dyck-run-return/rational-dyck-run-return.pdf) |

### Permutation patterns

#### Permutations with bounded adjacent jumps

| Note | Main result | Proof |
| --- | --- | --- |
| [Fixed and growing jump radii](results/permutation-patterns/adjacent-jump-limit/) | For 123-avoiders, the fixed-radius growth deficit is asymptotic to $16\pi^2/m^2$. A Brownian excursion maximum gives the surviving fraction when the radius grows with length. | [PDF](results/permutation-patterns/adjacent-jump-limit/adjacent-jump-limit.pdf) |
| [An automaton for arbitrary forbidden patterns](results/permutation-patterns/bounded-jump-automaton/) | Every finite forbidden set has a finite-state counting algorithm and a rational generating function for each fixed jump bound. | [PDF](results/permutation-patterns/bounded-jump-automaton/bounded-jump-automaton.pdf) |

#### Regular permutation packings

These five notes address questions in §7 of the same paper by Blitvić, Kammoun, and Steingrímsson. The item numbers below follow the authors’ list. [Original questions](https://arxiv.org/html/2610.29846v1#S7)

| Item | Note | Main result | Proof |
| --- | --- | --- | --- |
| 2 | [Factorization with variable overlaps](results/permutation-patterns/packing-factorization/) | A finite criterion decides whether counts split at a designated overlap and gives a witness whenever they fail to split. | [PDF](results/permutation-patterns/packing-factorization/packing-factorization.pdf) |
| 5 | [Separators in packing posets](results/permutation-patterns/packing-separators/) | At overlap $m$, the answer for any number of copies is determined by testing up to $6(m+1)+1$ copies. | [PDF](results/permutation-patterns/packing-separators/packing-separators.pdf) |
| 6 | [Catalan packing representatives](results/permutation-patterns/packing-catalan-lift/) | A count-preserving lift gives Catalan representatives for every overlap $m\ge 3$ and length $K\ge 2m$. | [PDF](results/permutation-patterns/packing-catalan-lift/packing-catalan-lift.pdf) |
| 8 | [The universal packing cutoff](results/permutation-patterns/packing-cutoff/) | Two patterns can have arbitrarily many initial counts in common and differ at the very next count. | [PDF](results/permutation-patterns/packing-cutoff/packing-cutoff.pdf) |
| 9 | [Integer powers as packing counts](results/permutation-patterns/packing-powers/) | Every positive integer base occurs for infinitely many patterns with overlap two. | [PDF](results/permutation-patterns/packing-powers/packing-powers.pdf) |

## Verification and citation

Thirty-two notes have runnable Python checks. The surface map-graph, prefix-free Busy Beaver advice, last-guess identification, and private language identification notes give theoretical proofs. Lean coverage is currently **0 of 36 main statements**. [Verification guide](docs/verification.md) · [Lean status and scope](lean/README.md)

To cite an individual note, use Wentao Li and the title from its PDF, link to the note at a specific commit (press **Y** on its GitHub page), and cite the publication that posed the question. For older citations, all ten original paths are available in the [snapshot before the reorganization](https://github.com/VictorLiwentao/solved-problems/tree/f5bcb6167a737e6a70c1965b3635db963adc792c).
