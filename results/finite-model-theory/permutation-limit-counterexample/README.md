# A proper permutation class without a first-order convergence law

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](permutation-limit-counterexample.pdf) · [LaTeX source](permutation-limit-counterexample.tex) · [Result catalogue](../../../README.md) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L81-L87)

## The question

View a finite permutation as a set with two orders, one by position and one by value. A permutation class is hereditary if deleting entries and relabeling the remaining values in increasing order keeps the permutation in the class. It is proper if it omits at least one finite permutation. Braunfeld and Kukla asked whether, in every proper permutation class, the probability of each fixed first-order sentence converges as the size grows. [Original paper, Question 5.4](https://doi.org/10.54550/ECA2022V2S4PP2)

## The counterexample

There is a single proper hereditary class and an increasing sequence of sizes $r_i$ with the following behavior under uniform sampling.

| First-order property | At size $r_i$ | At size $r_i+1$ |
| --- | --- | --- |
| The first entry is the smallest value. | Probability tends to 1. | Probability tends to 0. |

The sentence asks whether there is an element that is least in both orders. It uses two variables and has quantifier rank two. Every rank-one sentence is constant on nonempty structures in this language, so two is the minimum possible rank for a counterexample.

## Why the probabilities change

Pantone and Vatter constructed a class with exponentially many members at selected sizes compared with the immediately following sizes. We use their adjacent-size estimates. We add a copy of each permutation with a new minimum placed first. This carries the large count forward by one size and makes every copied member satisfy the sentence.

We also include the class of permutations expressible as at most $K$ consecutive decreasing blocks. Its exponential growth rate is $K$. Starting with a minimum uses up one block, so the satisfying permutations in this part grow at rate $K-1$. Choosing $K$ strictly between Pantone and Vatter’s two bounds makes the copied members dominate at the first size. At the very next size the total count is large enough to make the satisfying members a vanishing fraction. The proof includes explicit bounds on both errors. [Enumerative input, §6.3](https://arxiv.org/abs/2610.30369v1)

The construction answers the general hereditary-class question. It does not satisfy the extra sum-closure hypothesis of Question 5.3. Earlier positive results cover small permutation classes. [Falgas-Ravry, Markström, Räty, and Skerman](https://arxiv.org/abs/2610.34328)

## Proof, checks, and priority

The proof for arbitrarily large sizes is in the PDF. The checker independently compares decreasing-block counts with a coloring construction, interprets the first-order sentence directly, and checks heredity and the exact count of satisfying members on finite examples. Run the following from this directory.

~~~sh
python3 verify.py
~~~

For a finite illustration, take all permutations through size 10 as the base class and allow two decreasing blocks. The exact probabilities at sizes 11 and 12 are $907200/907709$ and $1/4084$. This example exhibits one change. The cited infinite construction supplies changes at arbitrarily large sizes. [Checker](verify.py)

I found no earlier negative answer to Question 5.4 in the sources checked. The proof and priority claim await independent review. Lean formalization is pending. [Verification guide](../../../docs/verification.md)
