"""Evaluate both unrounded conjecture parameters from the edge set."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from small_graphs import connected_graphs, dominates, independent_masks


def check(graph):
    independent = independent_masks(graph)
    i_dom = min(s.bit_count() for s in independent if dominates(graph, s))
    dom = min(s.bit_count() for s in range(1 << len(graph)) if dominates(graph, s))
    edge_bound = max((graph[u] | graph[v]).bit_count() for v in range(len(graph))
                     for u in range(v) if graph[v] & (1 << u))
    local = [max(s.bit_count() for s in independent if s & ~neighbors == 0)
             for neighbors in graph]
    largest = max(local)
    closed = 0
    for v, value in enumerate(local):
        if value == largest:
            closed |= graph[v] | (1 << v)
    assert i_dom <= dom * (edge_bound // 2 - 1)
    assert i_dom <= dom * (closed.bit_count() - 3)


if __name__ == "__main__":
    counts = []
    for n in range(4, 7):
        count = 0
        for graph in connected_graphs(n):
            check(graph)
            count += 1
        counts.append(count)
    assert counts == [38, 728, 26704]
    print(f"421b and 421c verified on all {sum(counts)} connected labeled graphs of orders 4–6.")
