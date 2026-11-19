# When permutation-packing counts factor

Wentao Li · AI-assisted research note

[Read the proof (PDF)](packing-factorization.pdf) · [LaTeX source](packing-factorization.tex) · [Result catalogue](../../../README.md)

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

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
