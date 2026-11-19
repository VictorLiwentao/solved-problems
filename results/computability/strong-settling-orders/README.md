# Countable orders of strong settling times

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](strong-settling-orders.pdf) · [LaTeX source](strong-settling-orders.tex) · [Finite verification](verify.py) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L57-L63)

Enumerate a set $A$ by a computer program. Its settling time $m_A(x)$ is the last stage when a number at most $x$ enters. Csima and Shore asked whether *every countable partial order* could be represented both by the rates at which these enumerations settle and by what the resulting sets can compute as oracles. Two incomparable elements must give sets that cannot compute each other. The proof gives such a representation, even inside a family whose combined information is insufficient to decide the halting problem. [Original article](https://doi.org/10.2178/jsl/1191333856) · [Authors’ manuscript, Conjecture 7.16](https://www.math.uwaterloo.ca/~csima/papers/settlingtime.pdf)

## Two comparisons at once

For every strict comparison $a<b$, the representative for $b$ eventually takes longer to settle than that for $a$, even after *any* computable change of input scale and *any* computable increase of the time bound. Knowing membership in $A_b$ up to $x$ also suffices to decide whether $x$ belongs to $A_a$. If $a$ is outside the set of predecessors of $b$ and $a\ne b$, even unrestricted oracle access to $A_b$ cannot compute $A_a$.

The proof also answers Csima’s question about choosing representatives of two specified high computably enumerable degrees. Whenever $\mathbf a<\mathbf b$ are such degrees, the lower and upper representatives can be made strictly comparable by strong settling-time domination. Inside even a *single* high Turing degree, one can realize every countable partial order simultaneously by strong settling times and by oracle computations with computably bounded query positions. [Csima’s Questions 2 and 6](https://www.math.uwaterloo.ca/~csima/papers/siennast2.pdf)

## How the construction works

Small numbers in each enumeration are reserved for responses to late entries in enumerations below it. At each level only finitely many rows take part. Counting the possible movements in one order, then the possible responses in the reverse order, gives a finite reserve at every level. A computably enumerable set with a sufficiently fast settling time supplies a time limit for the simulations. Every fixed total computable function passes that limit on sufficiently large inputs.

A separate data position records information about the predecessors of a row. Moving that position leaves a permanent flag. The flags let an oracle for the finished row recover its data, and the proof identifies exactly which data suffice to reconstruct the entire row. This is what prevents an unintended Turing reduction between incomparable elements.

## Verification and priority

Csima and Shore proved that the weaker settling-time ordering is universal. Clinton Loo proved the finite partial-order case of strong domination and stated the countable case as a conjecture. The new argument treats arbitrary countable orders and enforces the Turing nonreductions in the original Csima–Shore conjecture. It uses classical work of Robinson, Martin, Sacks and Harrington. The source and citation search found no prior proof of either this simultaneous embedding or the prescribed-degree pair result. Independent review and Lean formalization are pending. [Loo’s Theorem 4.9 and Conjecture 4.15](https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/796cde70-67e3-4073-a406-5d93d5c0140a/content) · [Robinson’s theorem](https://doi.org/10.1002/malq.19680142105)

The finite checker runs a version with one input function and one delay function. It checks movement bounds, response capacity, data decoding and every point at which either settling time changes on 1,011 intervals, across all 219 labelled four-point orders and six schedules with changing local orders. The infinite domination and oracle nonreducibility assertions are proved in the manuscript.
