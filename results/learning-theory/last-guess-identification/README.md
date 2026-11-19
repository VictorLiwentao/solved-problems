# When the previous guess cannot remember a language

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](last-guess-identification.pdf) · [LaTeX source](last-guess-identification.tex) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L169-L175)

Kleinberg, Mehrotra, Saberi and Velegkas ask whether the weak Angluin condition still characterizes approximate identification when a learner remembers only its most recent guess. Their learner must output an index of a candidate language at every round. We give a counterexample and an exact characterization for families nested by inclusion. [Original question, §1.3, and definitions, §5](https://arxiv.org/abs/2605.30324)

## The counterexample

Partition the data into disjoint infinite columns numbered from zero and add a common marker. Target number $n$ contains the marker and every column numbered $n$ or higher. Its regular language has a one-word telltale. A learner with the sample history identifies the target exactly by reporting the smallest column number it has seen. The same algorithm needs just one private bit in addition to its guess, recording whether a column has appeared yet.

Every learner restricted to the previous output fails, even with a freely chosen first response, unlimited computation and a text that never repeats a word. Present the common marker and let $j$ be its guess. Success on target $j$ would require the learner to stay at $j$ on all but finitely many of its words. Start the remaining text in a sufficiently high column and enumerate that column and all higher ones. Every transition leaves the learner at $j$ even though its guess misses the target by infinitely many words.

With fresh randomness and no hidden state, the infimum of the success probabilities over a fixed list of repetition-free texts is zero. The proof also characterizes arbitrary nested families on texts with repetitions, including the effect of a spare output index.

## Proof and priority

The PDF contains the deterministic separation, the randomized bound and the nested-family classification. All three are mathematical proofs. Independent review and formalization are pending. The necessity argument for arbitrary texts uses the previously published observation that a uniquely correct guess must absorb all inputs from its target. We found no earlier matching repetition-free counterexample or chain characterization in the materials checked. [Jain, Kötzing, Ma and Stephan, Lemma 22](https://hpi.de/friedrich/docs/publications/2016/InCo_b.pdf) · [Case, Jain, Lange and Zeugmann on iterative learning and redundant hypotheses](https://doi.org/10.1006/inco.1998.2784)
