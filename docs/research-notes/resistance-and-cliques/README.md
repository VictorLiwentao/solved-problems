# A bipartite graph and a graph with a 100-clique can look identical to resistance refinement

Wentao Li · November 27, 2026 · Prepared with assistance from OpenAI GPT-6.2 Astra

For every $m\ge 2$ there is one resistance-refinement signature shared by graphs with every chromatic number from 2 to $m$. In the example with chromatic number $k$, the largest clique has exactly $k$ vertices. All graphs in the family are simple, connected, have $2m^2$ vertices, and have average degree less than five. Taking $m=100$ gives the headline.

The observer updates each vertex by the multiset of the colors of the other vertices paired with their effective resistances to it. It can also receive an **adjacency bit in each message**. The signatures agree after every number of rounds, even when each corresponding two-vertex fiber has a unique initial color. A full labeled resistance matrix supplies a different observation model and determines the graph.

This is a corollary and strengthening of the archive’s earlier construction for the comparison posed by Zhang, Luo, Wang and He in 2022. The November 21 draft gave a 78-vertex bipartite-versus-triangles example and permitted arbitrary signs on the edges of a template. The argument below makes the color range explicit and proves the stronger joint-adjacency statement directly by series and parallel reduction. [Earlier proof](../../../results/learning-theory/resistance-blind-lifts/README.md) · [Original question, Section 6](https://openreview.net/forum?id=r9hNv76KoT3) · [Black et al., ICML 2024](https://proceedings.mlr.press/v235/black24b.html)

## The electrical construction

Start with two terminal copies $i_0,i_1$ for each vertex $i$ of the template $K_m$. For every pair $i<j$ choose a bit $s_{ij}$. For each $b\in\{0,1\}$ put a direct edge from $i_b$ to $j_{b\oplus s_{ij}}$. Between $i_b$ and the **other** copy of $j$, put two paths of length two. Each path gets its own new midpoint. Every edge has unit conductance. Two length-two paths in parallel have conductance one, exactly the conductance of the direct edge.

For each template pair the electrical network on its four terminals therefore reduces to $K_{2,2}$ with unit conductances, independently of the bit. It connects all four terminals. Counting the two direct edges and the eight edges of the four length-two paths gives $10\binom m2$ edges and $2m+4\binom m2=2m^2$ vertices.

## Why every round agrees

Pair the terminals in fibers $\{i_0,i_1\}$. For each pair $i<j$ and each of its two parallel path indices, the two midpoints indexed by $b=0,1$ are another fiber. Fix a source vertex and a target fiber. Retain in full the template gadgets containing the source and target midpoints, if either is a midpoint. If both are terminals with different template indices, retain their mutual gadget. Replace each remaining gadget by its electrically equivalent four-terminal network.

At most two distinct template edges have been retained. They form a forest. To compare two assignments $s,s'$, swap the terminal sheets at indices according to bits $h_i$ satisfying

$$ h_i\oplus h_j=s_{ij}\oplus s'_{ij} $$

on the retained edges. On a forest these equations can be solved from a root in every component. The root bit is free, so we can send the fixed source to either chosen sheet in its corresponding fiber. Each retained midpoint on the path from $i_b$ goes to the midpoint of the same path index from $i_{b\oplus h_i}$. Every reduced $K_{2,2}$ is invariant under independent sheet swaps.

This is an isomorphism of the reduced electrical networks. It preserves the resistances from the source to both target vertices, possibly exchanging them. It also preserves their original adjacency to the source. With two distinct terminal indices their gadget was retained, and adjacency involving a midpoint is decided by its own gadget. Thus the two-element multiset of **joint** resistance and adjacency values agrees fiber by fiber. If colors are paired on the fibers before an update, they are paired after it. Induction proves the claim for all depths.

## Realizing every clique and chromatic number

Fix $2\le k\le m$. Partition the $m$ indices into $k$ nonempty classes labeled modulo $k$. Choose $s_{ij}=0$ between different classes and $s_{ij}=1$ within a class. One sheet-zero representative from every class forms a $k$-clique.

Give terminal $i_b$ color $c(i)+b\pmod k$, where $c(i)$ labels its class. Every direct edge joins distinct colors. For $k\ge3$ there is a spare color for each midpoint, which has only two neighbors. For $k=2$, the endpoints of each length-two path have the same color: switching the target sheet from the direct edge reverses its color. Give the midpoint the opposite color. This produces a proper $k$-coloring and proves $\omega=\chi=k$.

In particular, no graph-level readout of these refinement signatures can approximate the chromatic number within any fixed multiplicative factor on all connected graphs. A common positive estimate within a two-sided factor $C$ of both $2$ and $m$ would require $m\le2C^2$.

**Proof and priority.** Written proof. The checker uses exact grounded Laplacian inverses on the original unreduced graphs and verifies each clique and coloring. The earlier signed-gadget result is the immediate precursor. Independent review and an exhaustive priority determination are pending. This companion counts as an extension of the existing catalogue entry. [Exact checker](verify.py)
