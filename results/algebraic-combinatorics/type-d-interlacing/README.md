# Strict interlacing of type-D Eulerian polynomials

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](type-d-interlacing.pdf) · [LaTeX source](type-d-interlacing.tex) · [Result catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/algebraic-combinatorics/type-d-interlacing/citation.bib)

## Original question

Do the zeros of type-D Eulerian polynomials interlace in consecutive ranks? [Chow, §5](https://doi.org/10.1016/j.jmaa.2022.126019)

## Result

For each $q>0$ and $n\geq3$, the $n$ simple zeros at rank $n$ lie strictly between successive zeros at rank $n+1$. The same holds starting at rank two for $q\ne1$. At $q=1$, ranks two and three share the zero $-1$.

The refined Eulerian polynomials already interlace within a row. The recurrence rules out a common zero of the entire row and turns the weak sign inequalities at successive ranks into strict ones. [Yang and Zhang](https://arxiv.org/abs/1401.6273)

## Verification

The [SymPy verifier](verify.py) compares small signed-permutation groups directly and makes 56 exact interlacing checks. Install SymPy as described in the [verification guide](../../../docs/verification.md).

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
