"""Check the cyclic seed construction and recover its interchangeable groups."""

from itertools import combinations


def edge(u, v):
    return tuple(sorted((u, v)))


def seed(m, shifts):
    # Three rows; the first and last row form the optional pair.
    edges = set()
    for row in range(3):
        for x in range(m):
            edges.add(edge(row * m + x, row * m + (x + 1) % m))
            if row < 2:
                edges.add(edge(row * m + x, (row + 1) * m + x))
    for d in shifts:
        edges.update(edge(x, 2 * m + (x + d) % m) for x in range(m))
    return edges


def connected(n, edges):
    neighbours = [set() for _ in range(n)]
    for u, v in edges:
        neighbours[u].add(v)
        neighbours[v].add(u)
    seen = {0}
    queue = [0]
    while queue:
        for v in neighbours[queue.pop()] - seen:
            seen.add(v)
            queue.append(v)
    return len(seen) == n


def clique_expansion(n, edges, t):
    expanded = set()
    for u, v in combinations(range(n * t), 2):
        if u // t == v // t or (u // t, v // t) in edges:
            expanded.add((u, v))
    return expanded


def twin_groups(n, edges):
    neighbourhoods = [{v} for v in range(n)]
    for a, b in edges:
        neighbourhoods[a].add(b)
        neighbourhoods[b].add(a)
    groups = {}
    for v, neighbours in enumerate(neighbourhoods):
        groups.setdefault(frozenset(neighbours), set()).add(v)
    return sorted(groups.values(), key=min)


def run():
    checked = 0
    for m in (3, 4, 5):
        n = 3 * m
        translate = [row * m + (x + 1) % m for row in range(3) for x in range(m)]
        for mask in range(1 << m):
            graph = seed(m, [d for d in range(m) if mask & (1 << d)])
            assert connected(n, graph)
            assert all(connected(n, graph - {e}) for e in graph)
            assert {edge(translate[u], translate[v]) for u, v in graph} == graph
            original_groups = twin_groups(n, graph)
            for t in (2, 3):
                expanded = clique_expansion(n, graph, t)
                expected = [{u * t + index for u in group for index in range(t)}
                            for group in original_groups]
                assert twin_groups(n * t, expanded) == expected
            checked += 1
    print(f"Checked bridgelessness, cyclic symmetry and twin-class recovery on {checked} seeds.")


if __name__ == "__main__":
    run()
