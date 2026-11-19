# Integer powers as permutation-packing counts

[Read the proof (PDF)](packing-powers.pdf) · [LaTeX source](packing-powers.tex) · [Result catalogue](../../../README.md)

## Original question

Does every positive integer base occur in the packing counts of infinitely many pattern–overlap pairs? [Blitvić, Kammoun, and Steingrímsson, §7, item 9](https://arxiv.org/html/2610.29846v1#S7)

## Result

For every $k\geq1$ and every $K\geq k+4$, a length-$K$ pattern with overlap two has count $k^{j-1}$ in $j$ windows. A second result characterizes when a pattern with two two-window packings attains the lower bound $2^{j-1}$.

The construction gives a repeated choice of how to interleave two chains. In the base-two equality case the packing poset consists of ordered blocks, each a singleton or a pair whose internal order can be reversed.

## Verification

The [verifier](verify.py) checks 840 exact counts for the construction and 176 comparisons for the base-two characterization.

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
