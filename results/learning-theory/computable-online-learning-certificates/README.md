# Finite evidence for computable universal online learning

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](computable-online-learning-certificates.pdf) · [LaTeX source](computable-online-learning-certificates.tex) · [Finite verification](verify.py) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L161-L167)

An adversary asks for one binary prediction at a time. Every finite set of revealed labels must agree with some allowed hypothesis, but the adversary can change which hypothesis explains the data. The learner is a program that must answer after every realizable history. Kalociński and Steifer asked how to characterize success for arbitrary classes, both when each stream permits finitely many mistakes and when one error budget must cover all streams. [NeurIPS 2025, §3](https://arxiv.org/abs/2510.18352)

## Two characterizations

* **Finitely many mistakes on each stream.** A finite set of observations can name a program giving correct answers on the whole queried part of the domain. The assignment is computable, and the named program must be total whenever its evidence is realizable. This identifies online learnability with classical total sublearning of the product closure of the class. Jain, Kinber and Wiehagen gave the finite-evidence representation for sublearning in 2004. The proof connects the two success criteria and handles arbitrary query orders, omitted inputs and programs that can diverge off the class. [Classical sublearning theorem](https://doi.org/10.1016/j.ic.2004.03.003)
* **At most a fixed number of mistakes.** There must be computably enumerable families of unordered labelled sets, from the empty set up to size one greater than the budget. Every realizable certificate has a listed extension at each new input. Every top-level set is forbidden. The least possible budget is exact. A learner can store only its mistaken examples and search for one listed extension to decide its next prediction. [Earlier effective Littlestone dimension](https://proceedings.mlr.press/v272/delle-rose25a.html)

## How difficult is recognition?

For effectively listed hypotheses that are nonzero at only finitely many inputs, recognizing universal computable learnability is $\Pi^1_1$-complete. Recognizing whether some finite uniform computable mistake budget exists is $\Sigma^0_2$-complete. The lower bounds already use classes where checking whether a finite sample is consistent is decidable.

For one fixed predictor that memorizes positive examples, the proof converts any recursive tree into a learning class. Computing an admissible stream that causes infinitely many errors is equivalent to computing an infinite path through the tree. In one example every hyperarithmetic admissible stream produces only finitely many errors for this predictor, although no learner succeeds on all admissible streams.

## Verification and priority

The program exhausts all 255 nonempty binary classes on three inputs and checks the finite consistency test on 2,187 traces. The PDF proves the characterizations and the infinite reductions. Earlier work established undecidability, the classical sublearning representation, and several restricted online-learning characterizations. A search of these sources and subsequent work found no earlier statement of the arbitrary-class online equivalence, the exact enumerable certificate criterion, or the stated recognition and adversary results together. Independent review and formal verification are pending. [Prior undecidability results](https://arxiv.org/abs/2106.01382) · [Related fixed-target characterization](https://arxiv.org/abs/2609.28551)
