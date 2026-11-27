"""Independently compare the fundamental coefficients of the two Hasse trees."""
from collections import Counter


def signature(k, common_top):
    # Core vertices 0,1,2. The 0--1 core edge is strict, 0--2 is weak.
    edges = [(1, 0, True), (2, 0, False)] if common_top else [(0, 1, True), (0, 2, False)]
    n = 3 * (k + 1)
    for core in range(3):
        parent = core
        for j in range(k):
            child = 3 + core * k + j
            edges.append((child, parent, False))
            parent = child
    before = [set() for _ in range(n)]
    predecessors = [set() for _ in range(n)]
    for a, b, strict in edges:
        predecessors[b].add(a)
        lower, upper = (b, a) if strict else (a, b)
        before[upper].add(lower)
    labels = {}
    while len(labels) < n:
        u = next(i for i in range(n) if i not in labels and before[i] <= labels.keys())
        labels[u] = len(labels)
    coefficients = Counter()

    def extend(used, word):
        if len(word) == n:
            coefficients[tuple(i for i in range(n - 1) if word[i] > word[i + 1])] += 1
            return
        for v in range(n):
            if v not in used and predecessors[v] <= used:
                extend(used | {v}, word + (labels[v],))

    extend(set(), ())
    return coefficients


if __name__ == "__main__":
    for k in (1, 2, 3):
        left, right = signature(k, True), signature(k, False)
        assert left == right
        print(f"{3 * (k + 1)} vertices: both have the same descent histogram on {sum(left.values())} extensions.")
