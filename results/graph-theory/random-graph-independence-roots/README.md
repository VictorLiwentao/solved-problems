# Right-half-plane independence roots of random graphs

[Read the proof (PDF)](random-graph-independence-roots.pdf) · [LaTeX source](random-graph-independence-roots.tex) · [Result catalogue](../../../README.md)

## Original question

An independent set has no edges between its vertices. If $X_s$ counts the independent sets of size $s$ in a graph $G$, its independence polynomial is $I_G(z)=\sum_s X_s z^s$. Brown and Cameron asked whether, with probability tending to one, this polynomial has all its roots in the closed left half-plane for a random graph. Cameron also conjectured that almost every graph has all its roots in a narrower sector about the negative real axis. [Brown and Cameron, Problem 2](https://doi.org/10.37236/7280) · [Cameron, Conjecture 6.1.1](https://hdl.handle.net/10222/75412)

## Result

Both assertions fail. In $G(n,p)$, write $U_n$ for the event of a root with strictly positive real part. For every fixed edge probability $0<p<1$,

$$\limsup_{n\to\infty}\Pr(U_n)\ \ge\ 1-\exp(-(1-p)^2).$$

In the uniform labeled graph model, $p=1/2$, this lower bound is about **22.12%**. It concerns a subsequence of graph orders. For every fixed $p$ there are also subsequences with positive probability of a root whose real part exceeds $c_p n/(\log n)^2$. When $1-p>\sqrt{(\sqrt5-1)/2}$, the instability probability tends to one along a subsequence.

## How the proof works

Choose the number of vertices so that independent sets of size $k$ are rare, while the counts at sizes $k-1$, $k-2$, and $k-3$ concentrate. If there is even one $k$-set, its count can be large enough relative to the other three to violate a necessary coefficient inequality for roots in the left half-plane. A Poisson approximation gives the quantitative bound. An elementary second-moment proof already gives 20% in the uniform graph model.

## Verification

The [exact checker](verify.py) verifies the determinant identities, compares the overlap formulas with every five-vertex graph, and certifies that the instability probability at $p=1/2$, $n=555422$ exceeds **10.32%** using rational arithmetic. The PDF gives the proof for arbitrarily large orders. With SymPy installed, run the following from this directory.

```sh
python3 verify.py
```

This note awaits independent review and Lean formalization. [Verification guide](../../../docs/verification.md) · [Formalization index](../../../lean/README.md)
