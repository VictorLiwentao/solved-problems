# How hard is it to recognize a network that supports granular synchrony?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

[Proof (PDF)](granular-synchrony-recognition.pdf) · [LaTeX](granular-synchrony-recognition.tex) · [Reproduce the checks](verify.py)

Suppose some links between parties deliver messages within a known time bound. Which arrangements of these links suffice for secure multiparty computation with guaranteed output delivery? Giridharan, Abraham, Crooks, Nayak and Ren gave a graph condition for Byzantine agreement in 2024. Appan, Heath and Ren established its role for secure computation at ASIACRYPT 2025. This note asks how hard it is to **check that condition on a supplied network**. [DISC 2024, Theorem 13](https://doi.org/10.4230/LIPIcs.DISC.2024.30) · [ASIACRYPT 2025](https://doi.org/10.1007/978-981-95-5116-3_1)

**Result.** Fix any rational fault fraction from one third up to, but excluding, one half. Recognition is coNP-complete even when the parties split into two groups with every link inside each group synchronous. In particular, a polynomial-time test covering all such networks would imply P = NP. This is a bound on inspecting the topology before running a protocol.

**Proof idea.** With $n$ parties and a fault budget $f$, let $h=n-2f$. The condition fails exactly when deleting $f$ parties can separate two sets, each with at least $h$ parties. The reduction starts with a bipartite graph and asks for a complete $k$-by-$k$ subgraph. Copying vertices on one side and adding fully connected and isolated vertices lets the reduction prescribe the fault fraction while preserving the answer. It also proves W[1]-hardness for finding a failure with parameter $h$. For each fixed $h$, enumerating two terminal sets and testing minimum vertex cuts takes $n^{2h+O(1)}$ time. [Lin’s biclique hardness theorem](https://doi.org/10.1137/1.9781611973730.41)

**Proof status.** The manuscript gives the construction and both implications. The Python check compares reachability with the separator condition on 33,800 graph/budget pairs through six vertices. It separately tests 4,710 instances of the reduction. Independent review is pending.

**Priority status.** The graph condition and the connection to secure computation belong to the conference papers above. We formulated the recognition question. A search of work on granular synchrony, balanced separators and bicliques found related hardness theorems. Priority for the fixed-fraction and parameterized statements remains unverified. [Related work on vertex bisection](https://arxiv.org/abs/1312.7014)

**Significance estimate · 60/100.** The reduction classifies a prerequisite for several published protocols across the full range of nontrivial fixed fault fractions. Its scope is worst-case topology recognition. [Scoring benchmark](../../../docs/scores-and-sources.md)
