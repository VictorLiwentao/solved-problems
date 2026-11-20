# When does uniqueness force a cyclic circuit to settle?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

[Proof (PDF)](cyclic-circuit-propagation.pdf) · [LaTeX](cyclic-circuit-propagation.tex) · [Exhaustive check](verify.py)

David Heath’s 2023 paper on simulating parallel random-access machines with cyclic circuits defines legality by requiring each input to determine a unique assignment to all wires. The sentence after Definition 4 infers that each wire then has finite delay. A three-gate XOR circuit shows where this inference fails. The note gives an exact condition on the wiring that makes the implication valid. [Heath’s paper, §4](https://arxiv.org/abs/2309.05133)

## The example

Give the circuit input $x$ and wire equations $a=b\oplus x$, $b=c\oplus x$, and $c=a\oplus b$. Substitution gives the unique assignment $(a,b,c)=(x,0,x)$ for both values of $x$. Each XOR waits for both inputs, so $a$ must settle after $b$, $b$ after $c$, and $c$ after $a$. No finite settling times satisfy all three requirements.

## The classification

Think of a wire as known once the values already present at its gate force the output on every possible completion. The graphs below specify which connections a gate may use.

- **Arbitrary Boolean gates.** Uniqueness guarantees propagation for every circuit on a wiring diagram exactly when each cyclic strongly connected component is a single directed cycle and no such component can reach another. Both conditions can be checked in linear time.
- **Gates with known input signs.** When each permitted input can only increase or only decrease its gate’s value, the exact obstruction is a positive cycle with a directed path to a negative cycle. A cycle is negative if it has an odd number of decreasing connections. With this obstruction absent, a system that stalls and has a solution has at least $2^s$ solutions, where $s$ is the number of source components in the remaining dependency graph. Detecting the signed obstruction is equivalent, by linear-time reductions, to detecting an even directed cycle.

## Proof and priority

The PDF proves both directions of each criterion for all finite diagrams. Running `python3 verify.py` compares the graph predictions with exhaustive truth-table checks through three internal wires. Independent proof review is pending.

Shiple, Berry and Touati already distinguished Boolean uniqueness from constructive evaluation in 1996. Richard established related fixed-point theorems for signed graphs. The contribution proposed here is the pair of exact criteria for permitted wiring. We formulated that question after reading Heath. His published open question in §8 concerns the overhead of PRAM simulation and remains separate. Independent priority review of the criteria is pending. [Shiple, Berry and Touati](https://www.cecs.uci.edu/~papers/compendium94-03/papers/1996/edt96/pdffiles/07a_1.pdf) · [Richard](https://arxiv.org/abs/1509.07702)

**Significance estimate · 52/100.** The classification identifies exactly when an entire class of circuit diagrams can use uniqueness to certify propagation. Its scope is circuit semantics. The manuscript gives no improvement to the running time or size of Heath’s simulation. [Scoring benchmark](../../../docs/scores-and-sources.md)
