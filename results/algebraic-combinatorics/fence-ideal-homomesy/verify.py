"""Compute one fence rowmotion orbit using sets and the cover definition."""
from collections import Counter

# Eleven segments; internal chains have three edges, the end chains two each.
lengths = (2,) + (3,) * 9 + (2,)
size = 1 + sum(lengths)
predecessors = {i: set() for i in range(1, size + 1)}
vertex = 1
for i, length in enumerate(lengths):
    for _ in range(length):
        if i % 2 == 0:
            predecessors[vertex + 1].add(vertex)
        else:
            predecessors[vertex].add(vertex + 1)
        vertex += 1


def row(ideal):
    generators = {i for i, parents in predecessors.items() if i not in ideal and parents <= ideal}
    closure = set(generators)
    stack = list(generators)
    while stack:
        new = predecessors[stack.pop()] - closure
        closure.update(new)
        stack.extend(new)
    return frozenset(closure)


start = frozenset(i for i in predecessors if 4034920448 & (1 << (i - 1)))
assert all(predecessors[i] <= start for i in start)
current = start
seen = set()
histogram = Counter()
while current not in seen:
    seen.add(current)
    histogram[len(current)] += 1
    current = row(current)
total = sum(k * count for k, count in histogram.items())
assert current == start and (len(seen), total) == (237, 3774)
print("Initial ideal:", sorted(start))
print("Cardinality histogram from 0 through 32:", [histogram[i] for i in range(size + 1)])
print("Total and period:", total, len(seen))
