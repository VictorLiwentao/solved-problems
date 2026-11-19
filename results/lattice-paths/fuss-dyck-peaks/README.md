# Peak polynomials for Fuss–Dyck paths

[Read the proof (PDF)](fuss-dyck-peaks.pdf) · [LaTeX source](fuss-dyck-peaks.tex) · [Result catalogue](../../../README.md)

## Original question

Are the polynomials counting occurrences of NNE on Fuss–Dyck paths with a fixed number of peaks real-rooted? [Alexandersson’s question](https://www.symmetricfunctions.com/realRootedCatalan.htm)

## Result

Fix the number $n$ of north steps and the number $k$ of peaks, with $1\leq k\leq n$. Changing the positive integer Fuss parameter multiplies the entire polynomial by a positive constant. All of its zeros are real and nonpositive, with the same multiplicities for every parameter.

A cyclic count of vertical runs separates out the slope-dependent factor. The remaining polynomial is a specialization of an elementary symmetric polynomial, and Gauss–Lucas locates its zeros.

## Verification

The [verifier](verify.py) compares 251 full coefficient distributions against a direct lattice-path computation.

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
