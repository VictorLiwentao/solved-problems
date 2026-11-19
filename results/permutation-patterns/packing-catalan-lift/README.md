# Catalan representatives for permutation packings

Wentao Li · AI-assisted research note

[Read the proof (PDF)](packing-catalan-lift.pdf) · [LaTeX source](packing-catalan-lift.tex) · [Result catalogue](../../../README.md)

## Original question

Can count-preserving operations on patterns explain Catalan representatives over the requested overlaps and lengths? [Blitvić, Kammoun, and Steingrímsson, §7, item 6](https://arxiv.org/html/2610.29846v1#S7)

## Result

For every overlap $m\geq3$ and pattern length $K\geq2m$, the construction realizes the Catalan numbers as the packing counts. It answers the Catalan part of item 6. The double-factorial part has a separate solution. [Nagy’s construction](https://arxiv.org/abs/2611.06937)

The lift adds positions that must form an initial chain in every linear extension. Removing that chain recovers the original packing poset, so its count is preserved in every number of windows.

## Verification

The [verifier](verify.py) compares all order relations in 4,356 examples of the lift.

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
