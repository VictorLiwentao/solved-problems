# Two countability principles for partial orders without choice

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](poset-countability.pdf) · [LaTeX source](poset-countability.tex)

Suppose all chains in a poset are finite and all antichains are countable. Does the assertion that such a poset is countable imply the corresponding assertion with chains and antichains exchanged? Banerjee and Gopaulsingh also ask whether the first assertion follows if every set is well-orderable or has an amorphous subset. The draft gives a negative answer to Question 6.1 and a positive answer to Question 6.3, including in pure ZF. [Original questions](https://doi.org/10.4064/ba221221-6-6)

## The two arguments

Under dependent choice, a poset with only finite chains is well-founded in both directions. Its minimal elements form a countable antichain. If the poset were uncountable, one of their upper cones would be uncountable. Within such a cone the argument supplies a strictly higher point with an uncountable cone. This contradicts the existence of a maximal point with that property. A previously published model of dependent choice already refutes the dual countability assertion. [Banerjee, Corollary 4.6](https://dml.cz/handle/10338.dmlcz/151857)

An amorphous set is infinite and every subset is finite or cofinite. Any partial order on such a set has a cofinite antichain. Every point has finitely many predecessors or finitely many successors. On a cofinite subset the same side is finite with the same cardinality, which prevents comparability. Under the well-orderable-or-amorphous-subset principle this forces posets with only countable antichains to be well-orderable and implies both countability principles.

## Proof and priority status

The three-page argument uses the published model and the prior countability theorem for well-orderable posets. Independent proof review, priority confirmation and Lean formalization are pending.
