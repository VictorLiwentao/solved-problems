# Characters of the free Lie algebra with compatible brackets

Wentao Li · Prepared with assistance from OpenAI Codex

[Read the proof (PDF)](multibracketed-lie-characters.pdf) · [LaTeX source](multibracketed-lie-characters.tex) · [Verification script](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/algebraic-combinatorics/multibracketed-lie-characters/citation.bib)

## Original question

For any prescribed counts of the different brackets, what are the symmetric-group character values of the multilinear component, and how often does each irreducible representation occur? [Rafael S. González D’León, 2014](https://arxiv.org/abs/1408.5415) · Question 7.13. Also Question 8.3.8 of the [2014 dissertation](https://scholarship.miami.edu/esploro/outputs/doctoral/On-the-Combinatorics-of-the-Free/991031448073702976)

## Result

A finite multinomial sum gives the character on every cycle type and all irreducible multiplicities. Every prime-length cycle has trace −1 in each bracket multidegree.

The expansion is indexed by forests whose vertex types are positive integers. A child’s type is a multiple of its parent’s. Cutting the edges where the type increases reduces the count to ordinary plane forests. On a single cycle this gives a sum over ordered factorizations of its length.

## Earlier work and verification

González D’León gave the plethystic inverse that encodes the representations. Dotsenko and Khoroshkin computed the two-bracket character. The draft gives a signed formula and leaves the separate Schur-positivity conjecture open. [Two-bracket character formula](https://doi.org/10.1007/s10688-007-0001-3) · [Classical inversion for species](https://doi.org/10.1016/0097-3165(95)90030-6)

The verifier compares the formula with Möbius inversion on permutation-fixed weighted partitions, using the known sign twist and the Hopf trace formula. Across degrees two through five, all 179 three-color character values at the 17 cycle types agree. Run `python3 verify.py` from this directory in a repository checkout.

**Significance 58/100.** Makes the character and multiplicities explicit for arbitrarily many brackets, starting from a known implicit character formula. The prime-cycle trace has a particularly simple form. Independent proof and priority review is pending. [Scoring scale](../../../docs/scores-and-sources.md#algebraic-combinatorics)
