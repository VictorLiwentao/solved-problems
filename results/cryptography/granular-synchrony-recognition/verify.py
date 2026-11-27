"""Finite checks of the reachability criterion and the padded biclique reduction."""

from itertools import combinations


def mask(vertices):
    return sum(1 << vertex for vertex in vertices)


def vertices(bits):
    while bits:
        bit = bits & -bits
        yield bit.bit_length() - 1
        bits ^= bit


def check_reachability(n, f):
    h = n - 2 * f
    full = (1 << n) - 1
    edges = list(combinations(range(n), 2))
    queries = []
    cross_masks = set()
    for fault_set in combinations(range(n), f):
        honest = full ^ mask(fault_set)
        for start in combinations(vertices(honest), h):
            queries.append((honest, mask(start)))
        for size in range(h, f + 1):
            for side in combinations(vertices(honest), size):
                left = mask(side)
                right = honest ^ left
                crossing = [i for i, (u, v) in enumerate(edges)
                            if ((left >> u & 1) and (right >> v & 1))
                            or ((left >> v & 1) and (right >> u & 1))]
                cross_masks.add(mask(crossing))

    def fails_by_reach(rows):
        for honest, start in queries:
            reached = start
            frontier = start
            while frontier:
                neighbors = 0
                for vertex in vertices(frontier):
                    neighbors |= rows[vertex]
                frontier = neighbors & honest & ~reached
                reached |= frontier
            if reached.bit_count() <= f:
                return True
        return False

    for graph in range(1 << len(edges)):
        rows = [0] * n
        for index in vertices(graph):
            u, v = edges[index]
            rows[u] |= 1 << v
            rows[v] |= 1 << u
        assert fails_by_reach(rows) == any(graph & cross == 0 for cross in cross_masks)
    return 1 << len(edges)


def common_neighbors(rows, chosen, right_size):
    common = (1 << right_size) - 1
    for i in chosen:
        common &= rows[i]
    return common.bit_count()


def make_slow_graph(rows, m, k, h, f):
    b = m - k + 1
    right_size = b * m + f - b * k
    new_right = ((1 << (f - b * k)) - 1) << (b * m)
    expanded = []
    for row in rows:
        twins = sum(((1 << b) - 1) << (b * j) for j in vertices(row))
        expanded.append(twins | new_right)
    expanded.extend([(1 << right_size) - 1] * (h - k))
    isolated = f - (b + 1) * (m - k)
    assert isolated >= 0 and len(expanded) + right_size + isolated == h + 2 * f
    return expanded, right_size


def check_reduction(m):
    comparisons = 0
    for graph in range(1 << (m * m)):
        rows = [(graph >> (m * i)) & ((1 << m) - 1) for i in range(m)]
        for k in range(1, m + 1):
            expected = any(common_neighbors(rows, side, m) >= k
                           for side in combinations(range(m), k))
            b = m - k + 1
            minimum_f = max(k, b * k, (b + 1) * (m - k))
            settings = [(k, minimum_f)]
            for p, q in [(1, 3), (2, 5)]:
                t = max((k + q - 2*p - 1) // (q - 2*p),
                        (minimum_f + p - 1) // p)
                settings.append(((q - 2*p) * t, p * t))
            for h, f in settings:
                expanded, right_size = make_slow_graph(rows, m, k, h, f)
                found = any(
                    common_neighbors(expanded, left, right_size) >= h + f - size
                    for size in range(h, min(f, len(expanded)) + 1)
                    for left in combinations(range(len(expanded)), size)
                )
                assert found == expected, (m, graph, k, h, f)
                comparisons += 1
    return comparisons


if __name__ == "__main__":
    graphs = sum(check_reachability(n, f) for n in range(3, 7)
                 for f in range((n + 2) // 3, (n - 1) // 2 + 1))
    reductions = sum(check_reduction(m) for m in range(1, 4))
    print(f"{graphs} graph/budget pairs passed the reachability check.")
    print(f"{reductions} padded biclique instances agreed with the original decision.")
