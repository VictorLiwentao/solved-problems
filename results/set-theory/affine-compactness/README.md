# Affine compactness and 2-SAT without choice

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](affine-compactness.pdf) · [LaTeX source](affine-compactness.tex) · [Finite verification](verify.py) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/affine-compactness/citation.bib)

If every finite part of a system of parity equations has a solution, must the whole system have one? ZFC says yes. It gives the same answer for 2-SAT. Over ZF, which omits the axiom of choice, each global assertion is a choice principle of its own. Li and coauthors showed that 2-SAT compactness does not imply parity compactness. They left the reverse implication open immediately after Theorem 5. [Original question and Boolean classification](https://arxiv.org/pdf/2609.33873)

The proposed proof constructs a model of pure ZF where every finitely satisfiable affine system over every finite abelian group has a solution, and one finitely satisfiable 2-SAT system has none. Together with the earlier result this completes the implication diagram for Boolean constraint templates, assuming ZF is consistent.

## Where the separation comes from

Start with a partially ordered set. Introduce a Boolean variable for the direction of each incomparable pair. Two directions that jointly close a cycle cannot both be selected. A linear extension solves all these constraints. Yet any choice of directions respecting the symmetries of the construction runs into a four-cycle.

For parity equations a signed average suffices. The proof puts integer weights of total one on the linear extensions of each finite poset with an auxiliary order. Deleting any point gives precisely the weights already chosen on the remaining poset. Jonsson and Welker’s shellability theorem supplies the compatible weights in every dimension. The signed average preserves affine equations. [Injective words and their commutation classes](https://arxiv.org/abs/0712.2143) · [Bodirsky’s exact Ramsey class, Corollary 1.4(3)](https://arxiv.org/abs/1204.3258)

## Passage to pure ZF

The second theorem transfers all finite-template compactness principles of a finite-support permutation model on countably many atoms to one model of pure ZF. Give each Cohen real a discrete label. A solution before hiding the labels gives answers conditional on every assignment of labels to its finite support. These answers form an ordinary constraint system in the model of unmarked reals. The proof obtains an invariant solution there and builds a hereditarily symmetric name for its evaluation on the actual labels. The opposite direction uses a finite obstruction in the quotient by each possible stabilizer. [Boolean prime ideal theorem in the Cohen model](https://arxiv.org/abs/2511.21684)

## Verification and priority

The checker builds and independently verifies 22,095 deletion marginals modulo two across all ordered posets with one through five vertices. It also checks that each of the two possible uniform directions violates a four-point constraint. The eight-page manuscript supplies the integral argument and the forcing proof.

The source search covered the 2017 compactness paper, the CSP dichotomy paper, Tardif’s 2026 paper, the September 2026 question and later records. I found no earlier proof of this direction. Independent proof and priority review and Lean formalization are pending. [Rorabaugh, Tardif and Wehlau](https://lmcs.episciences.org/2663) · [Kátay, Tóth and Vidnyánszky](https://arxiv.org/abs/2310.00514) · [Tardif](https://lmcs.episciences.org/18764)
