# Wentao Li’s mathematical research notes

[Wentao Li](https://github.com/VictorLiwentao) studies open questions in mathematics and theoretical computer science with assistance from OpenAI GPT-6.2 Astra and OpenAI Codex. The collection has **77 research drafts across eight fields**. Each draft links its proposed proof or counterexample to the original question. Independent review of the arguments and their priority is pending.

[**All drafts, A–Z**](results/README.md) · [Original questions and scores](docs/scores-and-sources.md) · [Lean proofs](lean/README.md) · [How to cite](#verification-and-citation)

## Browse the collection

| Field | Topics | Drafts |
| --- | --- | ---: |
| <a name="foundations-of-mathematics"></a><a name="computability"></a>[Computability](results/computability/README.md) | Busy Beaver, halting times and Turing degrees | 5 |
| <a name="set-theory"></a>[Set theory](results/set-theory/README.md) | Axioms of choice, compactness, infinite graphs and permutation models | 16 |
| <a name="finite-model-theory"></a>[Finite model theory](results/finite-model-theory/README.md) | Logical limit laws, spectra and finite model counts | 7 |
| <a name="learning-theory"></a>[Learning theory](results/learning-theory/README.md) | Classification, privacy, contrastive learning and language generation | 33 |
| <a name="combinatorics-and-graph-theory"></a><a name="graph-theory"></a>[Graph theory](results/graph-theory/README.md) | Random graphs, independence polynomials and map graphs | 3 |
| <a name="algebraic-combinatorics"></a>[Algebraic combinatorics](results/algebraic-combinatorics/README.md) | Roots and interlacing of counting polynomials | 3 |
| <a name="lattice-paths"></a>[Lattice paths](results/lattice-paths/README.md) | Peaks, runs and returns in Dyck paths | 2 |
| <a name="permutation-patterns"></a><a name="growth-of-atomic-classes"></a><a name="permutations-with-bounded-adjacent-jumps"></a><a name="regular-permutation-packings"></a>[Permutation patterns](results/permutation-patterns/README.md) | Growth rates, bounded jumps and overlapping patterns | 8 |

## Selected questions

- **Can two records share the computational power of Busy Beaver?** The proposed construction splits halting machines into two groups. Together their runtime records recover Busy Beaver, while neither record computes an upper bound for the other. [Read the draft](results/computability/splitting-busy-beaver/README.md)
- **How much choice is hidden in Rado’s selection lemma?** The draft uses one ultrafilter to order sets rank by rank. This gives the missing implication from Rado’s lemma to the Boolean prime ideal theorem in pure ZF. [Read the draft](results/set-theory/rado-prime-ideal/README.md)
- **Can the choice between equally good training fits change how much data a learner needs?** Even when every label can be renamed freely, two empirical risk minimizers can require sample sizes that differ by a logarithmic factor. [Read the draft](results/learning-theory/symmetric-erm/README.md)
- **How long can two permutation counts agree before they diverge?** For any prescribed length, two patterns have matching counts that far and differ at the very next term. The construction has a Lean proof. [Read the draft](results/permutation-patterns/packing-cutoff/README.md) · [Formal statement](lean/Statements/PackingCutoff.lean) · [Lean proof](lean/SolvedProblems/PackingCutoff.lean)

## Verification and citation

**Lean.** The project records 15 drafts with at least one main result formalized end to end and four more with partial proofs. The index identifies the theorem and its scope for each draft. [Formalization index](lean/README.md)

**Python.** 46 drafts include runnable checks. Each note explains what its computation verifies. [Run the checks or rebuild a PDF](docs/verification.md)

**Citations.** Each draft has a BibTeX entry under Wentao Li with a permanent link to the cited version. The source index credits the original proposer and dates the question. [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/citations.bib) · [Collection citation](CITATION.cff) · [Scores and sources](docs/scores-and-sources.md)

**For search tools and AI agents.** The catalogue contains titles, summaries, original attributions and versioned manuscript links. [Raw JSON](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/catalogue.json) · [Agent guide](llms.txt)

## Expository notes

Two companion notes give alternative proofs of published results.

- [Local regularizers and PAC learning](docs/expositions/affine-local-regularization/) gives an affine proof of Eric Hou’s separation. [Hou’s paper](https://arxiv.org/abs/2607.23449)
- [Two countability principles for partial orders](docs/expositions/poset-countability/) gives direct proofs of two results of Eleftherios Tachtsis. [Tachtsis’s paper](https://doi.org/10.1007/s00605-023-01933-z)

[Archive of the ten original note paths](https://github.com/VictorLiwentao/solved-problems/tree/f5bcb6167a737e6a70c1965b3635db963adc792c)
