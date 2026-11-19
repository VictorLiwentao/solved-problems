# Private generation in the limit on uncountable collections

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](private-generation-uncountable.pdf) · [LaTeX source](private-generation-uncountable.tex) · [Finite verification](verify.py)

A generator sees an enumeration of an unknown language and tries to output valid unseen words at every sufficiently late time. Continual-release privacy protects the joint distribution of all its outputs against changing any one input. Mehrotra, Velegkas, Yu and Zhou proved that every countable collection admits almost-sure generation under pure differential privacy and raised the uncountable case. [COLT 2026 paper, Theorem 1.1 and §5](https://arxiv.org/abs/2604.08504)

## Two uncountable collections

| Collection | Ordinary generation | Optimal worst-case probability under privacy |
| --- | --- | --- |
| All nonempty unions of complete columns in the grid of pairs of natural numbers | One observed word suffices on every enumeration. Its column supplies fresh words forever. | Zero under pure privacy and under any fixed finite Rényi budget of order greater than one. Probability one is attainable under $(0,\delta)$-privacy for every $\delta>0$. |
| A body containing a column tail, together with a single tag naming the column and cutoff | The generator succeeds from the instant the tag appears. | Exactly $\delta$ under $(\varepsilon,\delta)$-privacy for every finite $\varepsilon$, even if the tag is promised first. |

All lower bounds use fixed repetition-free enumerations. The probabilities are worst-case over targets and streams. The first collection proves that ordinary uniform generation from one example can coexist with zero worst-case utility under pure privacy. The examples address the eventual, continual-release criterion. Wang and Ye study private generation with an almost-sure uniform sample threshold. [Private Uniform Language Generation](https://arxiv.org/abs/2611.00797)

## Why the bounds hold

For complete columns, first give one word from each of many independently hidden columns. Replacing one record shows that the generator has little probability of naming that record’s column when the selection pool is large. A closed-event argument allows the missing words to be inserted sufficiently late to obtain a full enumeration while preserving a high probability of infinitely many errors. Positive additive privacy has a different effect. Sampling one record out of a long fixed prefix privately supplies a valid column, and oblivious sampling within it is eventually fresh almost surely.

For the tagged example the proof determines exactly what a randomized generator can do without the tag. If one of $r$ columns is known to be cofinite in the target, the optimal worst-case probability is $1/r$. More generally, the guarantees $p_j$ for individual columns are achievable exactly when their sum is at most one. The proof builds a fixed enumeration in stages while preserving a finite set of wrong guesses at each stage. On infinitely many columns, replacing the private tag by a dummy would turn any utility above $\delta$ into a positive uniform guarantee for the untagged problem.

## Verification and priority

The checker verifies the finite randomized-response privacy bound and the exact change in the law of a uniformly sampled record on neighboring inputs. The arguments about complete infinite enumerations are in the written proof. Earlier deterministic union obstructions are due independently to Hanneke and coauthors and to Bai, Panigrahi and Zhang. Searches of the cited papers and later work through November 19, 2026 did not locate either privacy separation or this randomized column guarantee. Independent review and Lean formalization are pending. [NeurIPS 2025 union theorem](https://arxiv.org/abs/2506.18642) · [SODA 2026 union theorem](https://arxiv.org/abs/2507.15319)
