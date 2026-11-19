# No universal cutoff for permutation-packing sequences

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](packing-cutoff.pdf) · [LaTeX source](packing-cutoff.tex) · [Result catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/permutation-patterns/packing-cutoff/citation.bib)

## Original question

Can a fixed number of initial counts distinguish every pair of distinct permutation-packing sequences? [Blitvić, Kammoun, and Steingrímsson, §7, item 8](https://arxiv.org/html/2610.29846v1#S7)

## Result

For every integer $h\geq1$, there are two patterns of the same length and overlap whose counts agree through term $h$ and differ at term $h+1$. Both sequences are unbounded.

A family of window posets has an explicit formula for the point at which its counts first branch. Choosing two offsets makes one sequence first exceed one at the requested term while the other still equals one.

## Verification

The [verifier](verify.py) builds the order constraints directly and checks 754 counts against the formula.

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
