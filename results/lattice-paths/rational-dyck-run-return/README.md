# Joint run and return counts for rational Dyck paths

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](rational-dyck-run-return.pdf) · [LaTeX source](rational-dyck-run-return.tex) · [Result catalogue](../../../README.md)

## Original question

How many rational Dyck paths have a prescribed run value and return count? [Dai, Fu, and Qiu, §5](https://arxiv.org/abs/2503.20155)

## Result

For a rectangle of width $m$ and height $n$ with $m\geq n\geq1$, the note gives an explicit formula for both the run and ratio-run statistics jointly with returns. The dimensions may have a common factor.

Binomial determinants count path segments between specified returns. Matrix multiplication joins the segments, and inclusion–exclusion recovers the count with exactly the requested number of returns.

## Verification

The [implementation](run_return.py) evaluates the formula. The [verifier](verify.py) compares 532 joint-distribution rows with direct enumeration.

From this directory, run

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Formalization index](../../../lean/README.md)
