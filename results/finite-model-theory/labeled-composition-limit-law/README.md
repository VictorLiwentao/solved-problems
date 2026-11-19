# Logical limit laws and their probability spectrum for labeled compositions

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](labeled-composition-limit-law.pdf) · [LaTeX source](labeled-composition-limit-law.tex) · [Result catalogue](../../../README.md)

## The question

Partition the labels $1,\ldots,n$ into nonempty blocks and order the blocks. Choose uniformly from all such ordered partitions. A sentence can test whether two elements belong to the same block or whether one block precedes another. The names of the labels are invisible to the sentence. Braunfeld and Kukla asked whether the probability of **every first-order sentence** converges as $n$ grows. Their earlier theorem treated uniform sampling of unlabeled compositions, which assigns different weights to the block sizes. [Original paper, Question 5.1](https://doi.org/10.54550/ECA2022V2S4PP2)

## Answer and exact limiting probabilities

**Yes.** Every fixed sentence converges exponentially fast, even in monadic second-order logic, which also allows quantification over subsets. The exponential rate may depend on the sentence.

Let $\rho=\log 2$. First-order and monadic second-order logic have the same set of limiting probabilities. In addition to zero and one, it consists exactly of

$$R(\rho),\qquad R\in\mathbb{Q}(X),\qquad 0<R(x)<1\ \text{for all }0<x\le\rho,$$

where $R$ must be defined throughout that interval. The proof constructs the rational function from a sentence and a first-order sentence from any admissible rational function. Equality and order of limits are decidable.

| Property or candidate | Limiting probability |
| --- | --- |
| The first block contains exactly one label | $\log 2\approx0.693147$ |
| The number of blocks is even | $1/2$ |
| The first block of size greater than one has size two | $(\log 2)^2/[2(1-\log 2)]$ |
| Any prescribed rational in $[0,1]$ | Realizable by a first-order sentence |
| $2\log 2-1\approx0.386294$ | Impossible for either logic |

For the last entry, $\log 2$ is transcendental, so the only rational function over $\mathbb Q$ that can take that value at $\log 2$ is $2x-1$. This function is negative near zero. The statement concerns the **set of numerical limits**. For example, the first-order sentence realizing a limit of $1/2$ may describe a different event from block parity.

## How the proof works

For a fixed sentence, sufficiently large unordered blocks all look alike. Clipping their sizes at a threshold reduces evaluation to running a finite automaton on a word of block sizes. Counting label assignments gives a block of size $j$ the generating function weight $z^j/j!$. Summing over all blocks puts the first singularity at $z=\log 2$. The large-block letter represents consecutive sizes, which excludes competing singularities on that circle and yields exponential convergence.

For the converse, blocks of size two can mark off trials. A first-order sentence can find the earliest gap whose sequence of block types belongs to either of two finite lists, then report which list matched. The proof constructs the lists so that the probability of the first outcome is the specified rational function evaluated at $\log 2$.

## Verification and priority

Run the following from this directory with SymPy installed.

~~~sh
python3 verify.py
~~~

The checker computes six rational functions symbolically, compares their finite counts with direct generation of labeled structures through size seven, and verifies an explicit first-order construction for $3/4-\log 2$. The PDF supplies the universal proof. [Calculator and checker](verify.py) · [Verification guide](../../../docs/verification.md)

Earlier work studies individual block statistics, the unlabeled logical law, and finite-state simulation of rational probabilities. I found no earlier solution to the labeled logical question or this exact spectrum in the sources checked. Independent review and Lean formalization are pending. [Random preorders](https://doi.org/10.1016/j.disc.2009.04.021) · [Finite-state coin simulation](https://doi.org/10.1007/s00493-005-0043-1)
