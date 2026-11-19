# Private list learning can fail at both dimensions one

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](private-list-learning-on-products.pdf) · [LaTeX source](private-list-learning-on-products.tex) · [Finite verification](verify.py)

A list learner can name several labels and succeeds if the true one is among them. Hanneke, Moran, Schefler and Tsubari asked whether two necessary conditions together suffice for differentially private list learning. Their list Littlestone dimension measures the depth of a realizable mistake tree. Their monotone dimension measures how many ordered points can realize every monotone assignment of the chosen labels. [COLT 2025 open question](https://proceedings.mlr.press/v291/hanneke25d.html)

## Result

For **every list length $k\ge2$**, there is a class on $\mathbb N^2$ with just $k+1$ labels and both dimensions **exactly one**, yet no approximate differentially private PAC learner can learn it with lists of length $k$. An ordinary online learner makes at most **one mistake**. In a related family, two labels suffice for online learning while the required private list length is arbitrarily large.

For the three-label example, the nonzero points form two finite blocks. Points labelled 1 increase in both coordinates. Points labelled 2 increase in the first coordinate and decrease in the second. The first block lies strictly southwest of the second. Once an online learner sees a point labelled 2, it can safely rule out one label everywhere. Yet point locations can vary independently in the two orders while preserving a balanced sample of all three labels. Privacy prevents a learner from reliably excluding a label on every such sample.

## The privacy argument

A finite product Ramsey argument reduces the learner's omission probabilities to a table indexed by the query’s ranks in the separate coordinates. Accuracy forces a jump between neighboring cells of the table. Moving one training example across a large gap would therefore produce arbitrarily many pairwise private output distributions with ordered, distinguishable event probabilities. The paper proves a packing inequality by clipping densities and applying the perceptron bound. Its cutoff in the additive privacy parameter is sharp.

For prediction classes formed by coloring products of independent monotone functions, the paper determines the exact list lengths for all three criteria. They are the most colors in a box with two levels per axis, the most colors on a chain monotone in a chosen direction on each axis, and the total number of colors.

## Verification and priority

The checker exhausts the admissible colorings of a three-by-three grid for three list lengths. It also verifies the balanced sample templates and the equality construction for the packing cutoff. The PDF proves the general lower bound for improper randomized learners under approximate differential privacy, including an inverse-linear additive privacy parameter. The one-order Ramsey and packing approach is due to earlier work cited in the paper. A search of the original COLT paper, its citing literature and newer work found no prior solution to the joint-sufficiency question. Independent review and Lean formalization are pending. [Prior threshold argument](https://arxiv.org/abs/1806.00949) · [Original list-learning lower bounds](https://arxiv.org/abs/2506.12856)
