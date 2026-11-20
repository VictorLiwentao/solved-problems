# Which languages can a private learner identify in the limit?

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](private-language-identification.pdf) · [LaTeX source](private-language-identification.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/private-language-identification/citation.bib)

An observer sees words from an unknown language and must eventually name it correctly forever. The entire sequence of guesses must protect every individual input. For countable families of infinite languages on repetition-free texts, Mehrotra, Velegkas, Yu and Zhou showed that finite pairwise intersections suffice. Their impossibility theorem required an infinite intersection and at least one finite directed difference. [COLT 2026 paper](https://proceedings.mlr.press/v336/mehrotra26b.html) · [Full statements and proofs](https://arxiv.org/abs/2604.08504)

## The result

Finite pairwise intersections are necessary and sufficient. Even when two languages each have infinitely many words absent from the other, an adversary can delay those distinguishing words. If the languages share infinitely many words, the optimal worst-case probability of eventual identification on the pair is exactly one half.

More generally, let $d$ be the supremum of the numbers of languages sharing an infinite set of words. The optimal worst-case success probability for lists of length $k$ is **$\min(1,k/d)$**, with value zero if $d$ is infinite. The result holds under pure differential privacy or a finite positive Rényi privacy budget of any order greater than one.

| Presentation of the target | Which intersections count toward $d$? |
| --- | --- |
| Each word appears once or any finite number of times | Infinite intersections |
| Repetitions are unrestricted | Nonempty intersections |
| Every word appears infinitely often | Nonempty intersections |

In the last setting, allowing any fixed positive additive privacy slack restores the classical list identification criterion. Independently keeping each record with that small probability still reveals every word eventually.

## Proof and priority

The lower bound starts on a stream common to several languages. A closed event in the output transcript can lose arbitrarily little probability under a sufficiently late single edit. Successively freezing longer input prefixes turns the common stream into an enumeration of a chosen target while preserving a high probability of failure. For the matching upper bound, a learner counts inconsistent words on disjoint blocks with independent noise. Ranking languages by cumulative failed tests eventually gives the target a fixed rank at most $d$.

The PDF contains the general proofs. The private single-index sufficiency theorem for repetition-free texts belongs to Mehrotra and coauthors. Charikar, Pabbaraju and Tewari characterized ordinary list identification. Their decomposition into single-identifiable classes can fail for private learners even with lists of size two. A search of the primary work, citing papers and recent preprints found no earlier matching adversarial privacy classification. Independent human review is pending. [Classical list identification](https://proceedings.mlr.press/v336/charikar26a.html) · [Statistical privacy setting](https://arxiv.org/abs/2604.07238) · [Uniform generation setting](https://arxiv.org/abs/2611.00797)

## Lean formalization

When s languages share an infinite subset, the optimal worst-case success probability for private identification with k slots is k/s. With unrestricted repetitions, a single shared word suffices. A private learner attains the bound. This is the finite common-intersection minimax theorem. The paper also treats countable families and classifies almost-sure identification. [Lean statement](../../../lean/Statements/PrivateIdentification.lean) · [Proof](../../../lean/SolvedProblems/PrivateIdentification.lean) · [Comparator and source alignment](../../../lean/submissions/private-language-identification/)
