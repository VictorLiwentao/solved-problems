# Language inclusion for Busy Beaver bouncer tapes

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](bouncer-tape-inclusion.pdf) · [LaTeX source](bouncer-tape-inclusion.tex) · [Checker](verify.py) · [Result catalogue](../../../README.md) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/computability/bouncer-tape-inclusion/citation.bib)

## The question

A *bouncer* is a type of Turing machine studied by the Busy Beaver Challenge. Its tape can contain blocks that expand on successive sweeps. A tape formula describes a family of configurations by giving the repeating blocks and the fixed strings, called walls, around them. The bouncer method can use a return to a more specific formula as part of a proof that a machine runs forever.

The researchers asked whether inclusion of the two families of configurations forces a specific change to the written formula. In their syntax, a repeater may acquire mandatory copies. For example, changing $r^*$ to $rr^*$ requires at least one copy of $r$. The project discussion records a proof for one repeater and a counterexample involving two adjacent commuting repeaters. It proposes requiring nonempty walls between repeaters, or forbidding adjacent repeaters that commute. [Project discussion](https://discuss.bbchallenge.org/t/186) · [Paper, §7.1.2 and footnote 21](https://arxiv.org/abs/2504.20563)

## Result

**Nonempty intervening walls suffice.** Read each side of the head outward. Assume both formulas are aligned by the project's rule, both have a nonempty wall between every successive pair of repeaters on the same side, and both have the same total number of repeaters. Then language inclusion holds exactly when the head symbols match and the following changes produce the narrower formula.

- At each repeater $r^*$, independently require $a\ge0$ whole copies on the head-facing side.
- Replace that repeater by $(r^b)^*$ for a positive integer $b$. Its multiplicity in the wider formula is now $a+bn$ when its multiplicity in the narrower formula is $n$.

The final exterior wall on each side must agree. Equal corresponding block widths force $b=1$, proving the proposed syntactic characterization for arbitrarily many repeaters. With the walls and blocks written out, testing the criterion takes linear time in their total length.

**Forbidding adjacent commuting repeaters is insufficient.** Take the two right half-tapes below, with the same head and left half. A star means zero or more copies.

$$F=(001)^*(011)^*,\qquad G=0(010)^*11(011)^*.$$

For every $i,j\ge0$, the word $0(010)^i11(011)^j$ equals $(001)^i(011)^{j+1}$. Hence every word of $G$ belongs to $F$. Both formulas are already aligned. All blocks are primitive and have width three, and the two blocks in either formula do not commute. Yet inserting mandatory copies in $F$ cannot change the first block from $001$ to $010$.

## Proof and verification

The first repeating block determines an infinite word obtained by following it forever. Among all infinite words, it is the unique one whose every finite prefix still allows the full growth rate of the tape language. Inclusion forces this word to agree for both formulas. The first mismatch against it then gives the mandatory offset and repetition stride. Removing that first part yields the same problem for the remaining repeaters.

Run the following from this directory with Python 3.

~~~sh
python3 verify.py
~~~

The checker compares the structural criterion with an independent finite-automaton inclusion test. It exhausts 47,961 formula pairs on a small binary input family, checks 240 longer examples, and verifies strict inclusion in the counterexample. Each automaton comparison covers words of every length for that pair.

The prior one-repeater proof is credited to savask, and the earlier commuting counterexample to Justin Blanchard. The paper uses insertion followed by realignment in its formula-fitting argument and proves a recovery theorem from three synchronized sample tapes. I found no prior resolution of the two proposed conditions in the sources checked. Independent review and Lean formalization are pending. [Project discussion](https://discuss.bbchallenge.org/t/186) · [Paper, Lemma 7.16 and Theorem 7.18](https://arxiv.org/abs/2504.20563)
