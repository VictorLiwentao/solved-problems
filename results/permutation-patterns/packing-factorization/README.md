# When permutation-packing counts factor

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](packing-factorization.pdf) · [LaTeX source](packing-factorization.tex) · [Result catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/permutation-patterns/packing-factorization/citation.bib)

## Original question

Which overlap choices give a product formula when a pattern occurs in a sequence of windows with varying overlaps? [Blitvić, Kammoun, and Steingrímsson, §7, item 2](https://arxiv.org/html/2610.29846v1#S7)

## Result

Fix a pattern of length $K$, an alphabet of allowed overlaps, and a designated overlap $m$. A finite test decides whether the counts multiply across $m$ for every overlap word. A failed test produces a violating word with at most $K+1$ overlaps on either side of the split.

The positions shared across the split are totally ordered. Counts factor precisely when the two sides cannot both place a new position in the same gap of that order.

## Verification

The [algorithm](factorization.py) constructs overlap words that witness a failure. The [verifier](verify.py) enumerates linear extensions to check 8,390 product equalities and 324 strict failures.

From this directory, run

```sh
python3 verify.py
```

Independent mathematical review is pending. [Formalization index](../../../lean/README.md)

## Lean formalization

For a pattern, an allowed alphabet of overlaps and a designated seam, a finite test decides whether every packing count factors across the seam. A failed test yields overlap words witnessing strict inequality. The Lean decision procedure enumerates bounded overlap words and compatible cuts. The Python implementation above searches a graph of cuts. [Lean statement](../../../lean/Statements/PackingFactorization.lean) · [Proof](../../../lean/SolvedProblems/Factorization.lean) · [Comparator and source alignment](../../../lean/submissions/packing-factorization/)
