"""Exhaust the core decomposition and the caterpillar generating function on small trees."""

from fractions import Fraction
from itertools import product
from math import factorial


def prufer_tree(code, n):
    neighbours = [set() for _ in range(n)]
    degrees = [1] * n
    for v in code:
        degrees[v] += 1
    for v in code:
        u = next(i for i in range(n) if degrees[i] == 1)
        neighbours[u].add(v)
        neighbours[v].add(u)
        degrees[u] -= 1
        degrees[v] -= 1
    u, v = (i for i in range(n) if degrees[i] == 1)
    neighbours[u].add(v)
    neighbours[v].add(u)
    return neighbours


def branch_height(graph, root, core):
    stack = [(root, -1, 0)]
    answer = 0
    while stack:
        u, parent, depth = stack.pop()
        answer = max(answer, depth)
        stack.extend((v, u, depth + 1) for v in graph[u] if v != parent and v not in core)
    return answer


def check_core(graph, radius):
    n = len(graph)
    core = set(range(n))
    for _ in range(radius):
        core = {v for v in core if len(graph[v] & core) > 1}
    if len(core) <= 1:
        assert min(branch_height(graph, v, {v}) for v in range(n)) <= radius
        return True
    if max(len(graph[v] & core) for v in core) > 2:
        return False
    for v in core:
        height = branch_height(graph, v, core)
        assert height <= radius
        if len(graph[v] & core) == 1:
            assert height == radius
    return True


def product_series(first, second, limit):
    return [sum(first[j] * second[k - j] for j in range(k + 1)) for k in range(limit + 1)]


def caterpillar_counts(n):
    # K1, K2 and stars with at least two leaves, followed by oriented spines / 2.
    fringe = [Fraction(0)] + [Fraction(1, factorial(i)) for i in range(n)]
    end = fringe.copy()
    end[1] = Fraction(0)
    core = product_series(end, end, n)
    egf = [Fraction(0), Fraction(1), Fraction(1, 2)] + fringe[3:]
    for _ in range(2, n + 1):
        egf = [a + b / 2 for a, b in zip(egf, core)]
        core = product_series(core, fringe, n)
    return [a * factorial(i) for i, a in enumerate(egf)]


def main():
    maximum = 7
    counts = [0, 1]
    total = 1
    for n in range(2, maximum + 1):
        count = 0
        for code in product(range(n), repeat=n - 2):
            tree = prufer_tree(code, n)
            count += check_core(tree, 1)
            check_core(tree, 2)
            total += 1
        counts.append(count)
    assert counts == caterpillar_counts(maximum)
    print(f"Checked trimmed cores on {total} labelled trees and exact caterpillar counts {counts[1:]}.")


if __name__ == "__main__":
    main()
