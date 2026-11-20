# Separators in permutation-packing posets

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](packing-separators.pdf) · [LaTeX source](packing-separators.tex) · [Result catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/permutation-patterns/packing-separators/citation.bib)

## Original question

Which packing posets have an element comparable with every other element, with incomparable elements both below and above it? [Blitvić, Kammoun, and Steingrímsson, §7, item 5](https://arxiv.org/html/2610.29846v1#S7)

## Result

Fix a pattern and an admissible overlap $m$. For $j$ copies, the answer agrees with the answer at $\min(j,6(m+1)+1)$ copies. This gives a finite test for the property at every $j>m$ and proves the authors’ proposed overlap-two family.

The ranks at the two ends of a window determine how comparisons propagate into the next window. The proof bounds how far that propagation must be followed to decide whether a position separates the poset.

## Verification

The [implementation](separators.py) applies the criterion. The [verifier](verify.py) makes 2,100 checks using the order on the actual positions and the proposed family.

From this directory, run

```sh
python3 verify.py
```

The note awaits independent human review. [Formalization index](../../../lean/README.md)

## Lean formalization

For overlap m, a packing of j windows has a separator exactly when the packing with min(j,6(m+1)+1) windows has one. A finite rank test decides this condition, and the proposed overlap-two family has separators at every length of at least two. The physical-position order, clipped rank tests and the overlap-two example are each checked. [Lean statement](../../../lean/Statements/PackingSeparators.lean) · [Proof](../../../lean/SolvedProblems/PackingSeparators.lean) · [Comparator and source alignment](../../../lean/submissions/packing-separators/)
