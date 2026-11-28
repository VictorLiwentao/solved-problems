# Pendant vertices and the parity of distances

Wentao Li · November 2026 · Prepared with assistance from OpenAI GPT-6.2 Astra

The parity correction in Graffiti.pc 432b reduces to a count of the two color classes. One leaf edge per support gives the inequality and characterizes equality for every connected bipartite graph in its domain.

[Proof (PDF)](pendant-distance-parity.pdf) · [LaTeX](pendant-distance-parity.tex) · [Exact checks](verify.py) · [Cite](citation.bib)

In December 2010 Ermelinda DeLaViña's Graffiti.pc proposed bound 432b for the minimum size $i(G)$ of a maximal independent set. For a connected simple graph of order $n>3$, let $P$ be the leaves and $S=N(P)$ their support vertices. Write $e(v),o(v)$ for the counts of vertices at even and odd distance from $v$, including $v$ at distance zero. With $B=1$ when $G$ is bipartite and $B=0$ otherwise, the statement is
$$i(G)\le n-|S|+B\min_v(e(v)-o(v)).$$
[Original catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Source statement 432b and date](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## Proof and equality

When $G$ is nonbipartite, the extra term vanishes. All leaves are pairwise nonadjacent because $G$ is connected and has more than two vertices. Extend the leaves to a maximal independent set. It avoids every support and therefore has size at most $n-|S|$. This also works when the leaf set is empty.

Now suppose $G$ is bipartite, with part sizes $a\le b$. Distances within a part are even and distances to the other part are odd. The minimum parity difference is $a-b$, so the proposed upper bound is $2a-|S|$. The smaller part itself is an independent dominating set, giving $i(G)\le a$.

Choose one incident leaf for each support. The resulting edges are vertex-disjoint: distinct supports have distinct leaves and no support is a leaf. They form a matching, so $|S|\le a$. Moreover, every dominating set must meet each of these edges to dominate its leaf. Consequently
$$|S|\le i(G)\le a\le 2a-|S|.$$
This proves the conjecture and shows that equality in its bipartite case holds exactly when $|S|=a$. Every star on at least four vertices attains equality. So does every graph obtained by attaching one new private leaf to every vertex of a connected bipartite graph on at least two vertices: the two new color classes have equal size, and the original vertices are precisely the supports.

## Verification and priority

The verifier enumerates connected labeled graphs of orders four through six, computes shortest-path parity counts and independent domination directly, and checks the equality criterion. The proof uses only the bipartition and a matching of leaf edges. These observations are elementary. The source lists the entry as open, and searches by number and statement in the literature, the DeepMind issue and pull-request lists, and public Graffiti logs located no earlier treatment of the exact conjecture. Independent review and Lean verification are pending.

The public logs used in the priority check include the [Graffiti verification archive](https://gitlab.com/ai-village-agents/village/graffiti-verification), the [archived conjecture worklog](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa), and [DeepMind’s Formal Conjectures issues](https://github.com/google-deepmind/formal-conjectures/issues).

## Significance

An elementary leaf matching proves a catalogue conjecture and identifies precisely when equality holds in bipartite graphs. [Scoring scale](../../../docs/scores-and-sources.md)
