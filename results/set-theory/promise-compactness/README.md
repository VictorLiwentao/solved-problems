# Integer weights and promise compactness without choice

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](promise-compactness.pdf) · [LaTeX source](promise-compactness.tex) · [Finite verification](verify.py) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/promise-compactness/citation.bib)

A promise compactness principle asks for a global solution under a weaker rule when every finite part can satisfy a stronger rule. Bodor posed three questions about how much choice these principles need. The draft gives two constructions. [Questions 6.3, 6.5 and 6.6](https://arxiv.org/abs/2604.08365)

| Question | Proposed answer |
| --- | --- |
| Does local exact-one satisfiability on triples require the ultrafilter lemma to obtain a global not-all-equal solution? | No. There is a model of pure ZF in which the promise principle holds and even choice for pairs fails. Of the prime sizes, the principle implies choice for triples alone. |
| Can a cyclic operation coexist with a promise compactness principle implying choice for sets of that prime size? | Yes, for every prime. Integer addition gives a symmetric operation of the prescribed arity and the principle implies the ultrafilter lemma. |
| Can such a principle imply choice for families of each fixed finite size? | Yes. The same construction works, including one example whose symmetric operation is binary. |

## Why integer counts lead to an ultrafilter

Use bits for the strict answers and integers from zero to a fixed mass for the weak answers. Require disjoint sums to add and require the whole space to have full mass. Any finite collection of these requirements on a Boolean algebra can be solved with bits by picking one cell of a finite partition. A global weak solution is an integer-valued measure. On a set of least positive mass, exactly one side of every split retains that mass. These choices give an ultrafilter. This part of the proof is elementary and does not use a forcing construction.

The argument extends to polymorphisms admitting a minor-preserving map into a family of nonconstant operations, each depending on a bounded number of inputs. This gives a compactness counterpart of a known computational hardness criterion. [Barto, Bulín, Krokhin and Opršal](https://doi.org/10.1145/3457606)

## Why exact-one gives a different answer

Across a finite group of symmetries whose order is prime to three, count how often each variable is true in a strict solution. Mark it when the count exceeds one third. The three counts on a constraint sum to the group order, so at least one mark is true and one is false. The proof turns these finite observations into an invariant weak solution, then uses the companion paper to obtain a model of pure ZF. In the other direction, a not-all-equal coloring of disjoint triples directly picks the minority member of each triple. [Companion transfer proof](../affine-compactness/) · [Earlier finite-instance algorithm](https://arxiv.org/abs/1704.01937)

## Verification and priority

The checker tests 74 weighted operations and 117,912 possible triples of counts. The infinite constructions and their choice implications are proved in the manuscript. The source search covered Bodor’s preprint, the earlier promise-CSP literature, and later records. Independent proof and priority review and Lean formalization are pending.

## Lean formalization

Lean proves that the endpoint-preserving addition template has cyclic and symmetric polymorphisms exactly at arities dividing the mass. The ZF compactness equivalence remains to be formalized. [Lean proof](../../../lean/SolvedProblems/PromiseMass.lean) · [Comparator checks](../../../lean/README.md)
