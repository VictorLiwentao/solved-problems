# How precisely must one measure resistance to recover every missing edge?

Wentao Li · November 27, 2026 · Prepared with assistance from OpenAI GPT-6.2 Astra

If a connected, unweighted graph on $n$ labeled vertices has $k$ missing adjacency entries, measure the electrical resistance once across each unknown pair. **Even if every reading is perturbed by just under $1/n^2$, those $k$ readings recover every missing edge exactly in polynomial time.** Two ways to remove a matching from a complete graph show that the leading constant one is sharp.

[Read the three-page proof (PDF)](resistance-completion.pdf) · [LaTeX](resistance-completion.tex) · [Exact decoder](decode.py) · [Reproduce the checks](verify.py) · [BibTeX](citation.bib)

## The original question

Huck Bennett, Mitchell Black, Amir Nayyeri and Evelyn Warton first posted the question in 2025. Their ALT 2026 paper gives an exact $k$-query algorithm by exhaustive search, a polynomial-time algorithm using $O(k^2)$ readings, and a log-determinant objective for numerical recovery with $k$ readings. Section 1.1 asks whether polynomial running time and subquadratic query count can be combined. [2025 preprint](https://arxiv.org/abs/2502.18350) · [ALT paper, Sections 1.1, 6.2 and 6.3](https://proceedings.mlr.press/v313/warton26a.html)

## Where the precision threshold comes from

A conductance of zero means that an edge is absent, and one means it is present. Adding a multiple of $x(1-x)$ to the authors’ convex objective gives it a one-sided slope at the true binary weight that dominates the measurement error. The curvature of the log determinant keeps the sum convex. The same construction interpolates between adjacent levels of any explicitly given finite rational alphabet. Rational cuts and an exact optimality certificate turn it into a deterministic polynomial-bit algorithm.

For the obstruction, start with the complete graph. In one copy erase edges 12 and 34. In a second erase edges 13 and 24. If these are the four unknown pairs, every reading changes by exactly $2/[n(n-2)]$. At error $1/[n(n-2)]$ the same four numbers can therefore describe either graph. This upper bound applies to the specified missing-pair measurements.

## Verification and significance

The supplied decoder implements the rational ellipsoid updates and verifies every returned graph by exact optimality inequalities. The checker compares all 703 pairs of connected labeled four-vertex graphs using independently enumerated spanning forests. It also exercises the decoder with adversarial error signs and both binary and four-level weights. Run `python3 verify.py` with SymPy installed.

**Significance estimate: 74/100.** It answers a conference paper’s algorithmic question in the finite rational model and gives a sharp asymptotic adversarial noise threshold. The query choice and noiseless convex formulation are due to the original authors. The known positions of the missing entries are essential to the stated result.

**Proof status.** Complete written argument and executable exact-arithmetic checks. Independent review and Lean verification are pending. **Priority status.** The November 27 search located the authors’ preprint and proceedings paper and earlier work on partial, noisy resistance data. I found no prior proof of this exact finite-alphabet decoding and sharp noise threshold. [Hoskins et al., NeurIPS 2018](https://proceedings.neurips.cc/paper_files/paper/2018/file/2f25f6e326adb93c5787175dda209ab6-Paper.pdf)
