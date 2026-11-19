# Unbounded fragments in unlabelled random graphs

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](unlabelled-fragment-counterexample.pdf) · [LaTeX source](unlabelled-fragment-counterexample.tex) · [Finite construction checks](verify.py) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/graph-theory/unlabelled-fragment-counterexample/citation.bib)

Pick a graph uniformly from the isomorphism types of a fixed order. Its *fragment* consists of everything outside its largest connected component. McDiarmid asked whether the expected fragment size is bounded in every decomposable class that permits adding bridges between components, and whether the asymptotic bound can be universal. With labelled sampling, the expected fragment has fewer than two vertices. [Original conjectures 3 and 4](https://arxiv.org/abs/2001.05256)

## Result

Both conjectures have negative answers. For any function $f(n)$ tending to infinity, a single such class has expected fragment size at least $n/f(n)$ at infinitely many orders. Taking $f(n)=\log(n+2)$ makes the expected fragment unbounded. Every forest belongs to the class and bridges may also be deleted. The stronger construction has a finite exponential growth constant for its number of unlabelled graphs and a convergent generating function at the critical radius.

The counterexample uses many distinct bridgeless graphs of the same size whose vertices fall into few symmetry orbits. Two of these graphs can stay separate or be joined by a bridge. Only the endpoint orbits matter for the isomorphism type of the connected result. At selected sizes this leaves enough probability on two equally large disconnected components to force a large mean. By spacing the sizes, one fixed class exhibits the phenomenon infinitely often.

## Verification and priority

The PDF gives the counting argument for all sizes, including the attachment estimates that keep the growth constant finite. The checker verifies connectivity after every single-edge deletion, the cyclic symmetries and the recovery of the original interchangeable vertex groups in finite examples. McDiarmid’s earlier large-fragment example uses one exceptional size in each of a succession of classes. Searches of the original problem note, its cited and citing work, and later papers on pendant appearances found no earlier resolution of the two expectation conjectures. The connectivity-probability conjectures in the same note are separate. Independent review and Lean formalization are pending. [Original problem note](https://arxiv.org/abs/2001.05256) · [Later appearance results](https://doi.org/10.1016/j.ejc.2024.103994)
