# Lists and finite partitions in uniform language generation

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](uniform-list-generation.pdf) · [LaTeX source](uniform-list-generation.tex) · [Finite verification](verify.py) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L209-L215)

A generator sees words from an unknown language and tries to produce a new word from that language. A list of guesses succeeds if it contains at least one such word. Charikar, Pabbaraju and Tewari asked whether every collection that generates uniformly with $r$ guesses can be covered by $r$ collections that each generate uniformly with one guess. Their theorem proves the corresponding assertion for *identifying* the target language. [Original COLT 2026 question, §5](https://proceedings.mlr.press/v336/charikar26a.html)

## Result

Two guesses can suffice from the very first example even when **every finite partition** contains a part on which single-word generation fails at arbitrarily large sample sizes. More generally, for every $r\ge2$ there is a countable collection of unary regular languages that generates with $r$ guesses after one example and defeats every finite cover by collections that generate with $r-1$ guesses.

The two-guess example uses complete graphs. Each vertex has a language with its own infinite supply of private words. Each edge contributes a finite set of words shared by its endpoints. Seeing one edge word leaves two possible targets, so the generator can take one fresh private word from each. In every finite coloring, a sufficiently large complete graph has an edge with both endpoints the same color. After the shared words of that edge have been exhausted, the two languages have disjoint remainders. The number of shared words grows with the size of the graph.

For general $r$, the faces of a simplex play the role of the endpoints, and the finite Ramsey theorem supplies the monochromatic simplex. With $s\le r$ guesses, the optimal worst-case probability of succeeding throughout the stream after a uniform threshold is exactly $s/r$, even with a finite-valued hint about the target.

## Characterization and verification

For an arbitrary collection, the exact threshold for $k$ guesses is one more than the largest size of a finite common intersection whose subcollection still needs more than $k$ words to meet every language outside that intersection. The paper handles unbounded sizes and the empty-sample convention. This extends the ordinary closure dimension. [Raman, Li and Tewari, COLT 2025](https://proceedings.mlr.press/v291/raman25a.html)

The checker compares the formula with direct list feasibility on small families, checks the pairwise intersections in the construction, and exhausts every two-coloring of the edges of the complete graphs on five and six vertices. The proof applies the classical finite Ramsey theorem at all list lengths. A literature search through November 19, 2026 found the published open question and related results on finite unions, without locating this separation. Priority remains provisional. Independent review and Lean formalization are pending. [Related work on union closure](https://arxiv.org/abs/2506.18642)
