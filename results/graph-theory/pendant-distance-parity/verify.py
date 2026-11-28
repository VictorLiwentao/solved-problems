"""Check the distance-parity formula without substituting color-class sizes."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from small_graphs import connected_graphs, dominates, independent_masks


def check(graph):
    n = len(graph)
    support = 0
    for neighbors in graph:
        if neighbors.bit_count() == 1:
            support |= neighbors
    im = independent_masks(graph)
    i_dom = min(s.bit_count() for s in im if dominates(graph, s))
    differences = []
    for root in range(n):
        seen = frontier = 1 << root
        even = frontier
        depth = 0
        while frontier:
            reached = 0
            for v, neighbors in enumerate(graph):
                if frontier & (1 << v):
                    reached |= neighbors
            frontier = reached & ~seen
            depth += 1
            if depth % 2 == 0:
                even |= frontier
            seen |= frontier
        differences.append(2 * even.bit_count() - n)
        if root == 0:
            first = even
    bipartite = first in im and (((1 << n) - 1) ^ first) in im
    rhs = n - support.bit_count() + int(bipartite) * min(differences)
    assert i_dom <= rhs
    if bipartite:
        a = min(first.bit_count(), n - first.bit_count())
        assert (i_dom == rhs) == (support.bit_count() == a)


if __name__ == "__main__":
    count = 0
    for n in range(4, 7):
        for graph in connected_graphs(n):
            check(graph)
            count += 1
    assert count == 27470
    print(f"432b and bipartite equality checked on {count} connected labeled graphs.")
