# When do models of Horn-clause expansions collapse?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

[Proof (PDF)](horn-expansion-collapse.pdf) · [LaTeX](horn-expansion-collapse.tex) · [Finite checks](verify.py)

Zhou, Heath and Harris define an expansion that replaces a relation in a system of logical rules by several copies. Appendix D, Lemma 1 of their HCVS 2018 paper states that intersecting the interpretations of the copies returns a model of the original system for every correspondence in Definition 6. The following four clauses give a counterexample. [Conference paper](https://doi.org/10.4204/EPTCS.278.3) · [Open manuscript](https://arxiv.org/abs/1705.03167)

| Original rule | Expanded rule |
| --- | --- |
| $x=0\implies P(x)$ | $x=0\implies P_0(x)$ |
| $x=1\implies P(x)$ | $x=1\implies P_1(x)$ |
| $P(x)\implies H(x)$ | $P_1(x)\implies H(x)$ |
| $H(x)\land P(x)\implies\bot$ | $H(x)\land P_0(x)\implies\bot$ |

The right column has the model $P_0=\{0\}$ and $P_1=H=\{1\}$. In the left column, substituting $x=0$ forces both $P(0)$ and $H(0)$ and forbids them from holding together. Every expanded rule projects to the original rule in its row. The two definitions of $P$ were split between its copies, so their intersection loses both required values.

**Repair.** Require every rule defining an original predicate to appear with every copy of that predicate as head. A single lift suffices for a query. The manuscript proves this condition sufficient with arbitrary background constraints and necessary for a structural guarantee when the guards can be independently enabled. The conclusion concerns the published lemma about all correspondences. The behavior of the authors’ solver depends on which correspondences its expansion procedure produces.

**Proof status.** The four-clause argument works over the integers. The Python checks enumerate models on the two named points and compare the repair with direct model checking on 8,192 small guarded systems. Independent review is pending.

**Priority status.** The statement being corrected is due to Qi Zhou, David Heath and William Harris (2017 preprint, 2018 proceedings). A search for corrections and later treatments did not identify this counterexample. Independent priority review is pending.

**Significance · 55/100.** This corrects a quantified lemma in a published verification argument and identifies the missing assumption. Its scope is model transfer under predicate splitting. [Scoring benchmark](../../scores-and-sources.md)
