# Deleting one edge from a join in the Kromatic symmetric function

Wentao Li · Prepared with assistance from OpenAI Codex

[Read the proof (PDF)](kromatic-bridge.pdf) · [LaTeX source](kromatic-bridge.tex) · [Verification script](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/algebraic-combinatorics/kromatic-bridge/citation.bib)

## Original question

Can the Kromatic deletion–contraction relation construct further pairs of nonisomorphic graphs with the same Kromatic symmetric function? [Laura Pierson and Soham Samanta, 2025](https://arxiv.org/abs/2508.17682v2) · Question 2.24, construction alternative

## Result

One five-term expansion per graph certifies an infinite family of equal pairs. For joins with one edge removed, an exact vertex-deletion criterion decides when the endpoint can change.

Fix two graphs joined by all cross edges and delete one cross edge. With one endpoint fixed, moving the other from $u$ to $u'$ preserves the invariant exactly when deleting $u$ or $u'$ from their side gives equal invariants. The explicit family uses two vertices of a tree with isomorphic deletion graphs and distinct automorphism orbits.

## Earlier work and verification

Pierson and Samanta already constructed equal pairs and gave other operations producing more. Their question asks specifically about using the Crew–Pechenik–Spirkl relation. The draft answers its construction alternative. [Five-term relation](https://arxiv.org/abs/2301.02177) · [Pierson’s induced-subgraph characterization](https://arxiv.org/abs/2502.21285)

Exact multisets of induced independence polynomials agree on every subset in the first three new graph pairs, of orders 14, 15 and 16. Run `python3 verify.py` from this directory in a repository checkout.

**Significance 46/100.** Gives a short certificate for the construction alternative of Question 2.24 and classifies a local graph operation. Equal pairs were already known. Independent proof and priority review is pending. [Scoring scale](../../../docs/scores-and-sources.md#algebraic-combinatorics)
