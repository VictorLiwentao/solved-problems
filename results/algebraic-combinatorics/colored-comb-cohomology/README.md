# A colored-comb basis for the full weighted partition poset

Wentao Li · Prepared with assistance from OpenAI Codex

[Read the proof (PDF)](colored-comb-cohomology.pdf) · [LaTeX source](colored-comb-cohomology.tex) · [Verification script](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/algebraic-combinatorics/colored-comb-cohomology/citation.bib)

## Original question

Do the colored combs whose root avoids the largest color form a basis of the top reduced cohomology of the full weighted partition poset with its bottom element removed? [Rafael S. González D’León, 2014](https://arxiv.org/abs/1408.5415) · Conjecture 5.11. Also Conjecture 6.3.4 of the [2014 dissertation](https://scholarship.miami.edu/esploro/outputs/doctoral/On-the-Combinatorics-of-the-Free/991031448073702976)

## Result

The proposed combs form a basis for every number of colors. Decomposing a tree at its root gives exactly the number of classes required for independence.

Let $C$ count all colored combs and $D$ count those with an allowed root, using exponential generating functions. A forbidden root has an arbitrary left subtree containing the minimum label and an allowed right subtree. This gives $D'=C'(1-D)$, so $D=1-e^{-C}$. The Möbius formula for the whole poset gives the same series for its top cohomology dimension.

## Earlier work and verification

González D’León proved spanning for the full poset and a comb basis for each one-block interval. González D’León and Wachs had already proved the full-poset result for two colors. [Two-color theorem](https://arxiv.org/abs/1309.5527)

Independent tree enumeration and Möbius inversion in the finite poset agree for all 16 combinations of two through five labels and one through four colors. Run `python3 verify.py` from this directory in a repository checkout.

**Significance 55/100.** Completes the missing independence argument in the 2014 conjecture. The proof uses the original spanning theorem and the known bases of the one-block intervals. Independent proof and priority review is pending. [Scoring scale](../../../docs/scores-and-sources.md#algebraic-combinatorics)
