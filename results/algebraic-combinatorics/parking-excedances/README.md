# Nonreal zeros of a parking-function polynomial

[Read the proof (PDF)](parking-excedances.pdf) · [LaTeX source](parking-excedances.tex) · [Result catalogue](../../../README.md)

## Original question

Are the excedance polynomials of parking functions real-rooted in every size? [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjParkingExcedances)

## Result

The size-17 polynomial has a nonreal conjugate pair of zeros. At $x=-1/5$ it violates $(P'(x))^2-P(x)P''(x)\geq 0$, a necessary condition for a polynomial with only real zeros.

The integer certificate evaluates the polynomial and its first two derivatives independently by a labeled-subset recurrence and a Ferrers-board count. The latter formula also computes the coefficients in arbitrary sizes.

## Verification

The [integer certificate](verify.py) reproduces both counts and the strict negative sign.

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
