# An unbounded compactness gap for agnostic transductive learning

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](agnostic-compactness-gap.pdf) · [LaTeX source](agnostic-compactness-gap.tex) · [Reproducible finite checks](verify.py) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/agnostic-compactness-gap/citation.bib)

## The conjecture

In leave-one-out prediction, the learner knows all the input points and sees every label except the one it must predict. In the agnostic setting the labels may be arbitrary, and the learner competes with the best hypothesis in its class. Asilis, Devic, Dughmi, Sharan and Teng conjectured that finite projections can understate the full class’s error by more than a factor of two under a metric loss. [NeurIPS 2024, §§3.3 and 4](https://proceedings.neurips.cc/paper_files/paper/2024/file/eb7295a8bc613b375726659c2ecd6f14-Paper-Conference.pdf)

## Result

There is a single class of constant functions for which the optimal full-class excess error is exactly **1 at every sample size** on a loss scale from 0 to 2. Every finite projection has excess error at most

$$
\sqrt{2\log(n+1)/n}+2/n.
$$

This gives an unbounded ratio and a qualitative failure of compactness. The finite guarantee is uniform in the number of hypotheses and allows every label in the original metric space. The lower bound also holds for randomized learners. The same construction separates finite projections from the full class in agnostic PAC learning, where the test example is drawn independently.

## Why finite and infinite classes behave differently

Each hypothesis names a finite set of tokens. For a finite list of hypotheses their union is another finite set, so the learner can use it as a default. A candidate can outperform the default only to the extent that the observed label puts mass on the atom representing that candidate. Across all candidates there is at most one unit of such mass per round. This gives the common finite-class bound.

For the full class, each particular prediction can substantially improve its loss on only finitely many tokens. Kuratowski’s free-set theorem yields a sample on which *every* withheld token escapes the corresponding prediction, even though one finite set contains the whole sample. The required size of the label space is sharp. For every bounded separable metric of diameter $D$, the gap in excess error is at most $D/n$. More generally it is at most $D(k+1)/n$ at density at most $\aleph_k$. The first density permitting failure of qualitative compactness is $\aleph_\omega$.

## Proof and priority

The proof includes both metric bounds, the randomized lower bound, the density threshold, and the PAC consequence. With tokens drawn from the reals, transductive learnability of this particular construction is equivalent to the continuum having cardinality below $\aleph_\omega$. The free-set and compression arguments and their earlier use in EMX learning are classical. The claimed new results concern supervised prediction with arbitrary labels under a bounded complete metric. No matching prior resolution appeared in the sources checked. Independent review and formal verification are pending. [Earlier EMX result](https://doi.org/10.1038/s42256-018-0002-3) · [Free-set theorem](https://arxiv.org/abs/0902.4448)

The checker exhausts finite instances of the atom metric, the default-comparator inequality, activation accounting and deletion stability of the finite hull. The cardinal and learning statements are proved in the PDF.
