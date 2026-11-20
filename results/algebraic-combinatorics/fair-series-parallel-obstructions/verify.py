"""Compare recursive construction and forbidden patterns independently."""
from functools import lru_cache
from itertools import combinations, permutations, product


def all_orders(n):
    pairs = list(combinations(range(n), 2))
    orders = set()
    for present in product((False, True), repeat=len(pairs)):
        rel = {p for p, active in zip(pairs, present) if active}
        for k in range(n):
            rel.update((i, j) for i in range(k) for j in range(k + 1, n)
                       if (i, k) in rel and (k, j) in rel)
        orders.add(frozenset(rel))
    return orders


def constructible(n, order, edge_colors):
    @lru_cache(maxsize=None)
    def construct(vertices):
        if len(vertices) == 1:
            return True
        for size in range(1, len(vertices)):
            for left in combinations(sorted(vertices), size):
                right = vertices.difference(left)
                pairs = [(a, b) for a in left for b in right]
                separate = all((a, b) not in order and (b, a) not in order for a, b in pairs)
                ordinal = all(pair in order for pair in pairs)
                colors = {edge_colors[p] for p in pairs if p in edge_colors}
                if separate or (ordinal and len(colors) == 1):
                    if construct(frozenset(left)) and construct(right):
                        return True
        return False
    return construct(frozenset(range(n)))


if __name__ == "__main__":
    cases = 0
    for n in range(1, 6):
        for order in all_orders(n):
            covers = sorted((a, b) for a, b in order if not any(
                (a, k) in order and (k, b) in order for k in range(a + 1, b)))
            has_n = any(order.intersection(permutations((a, b, c, d), 2)) ==
                        {(a, b), (c, b), (c, d)} for a, b, c, d in permutations(range(n), 4))
            for colors in product((0, 1), repeat=len(covers)):
                edges = dict(zip(covers, colors))
                mixed = any(len({v for e, v in edges.items() if e[side] == vertex}) > 1
                            for side in (0, 1) for vertex in range(n))
                assert constructible(n, order, edges) == (not has_n and not mixed)
                cases += 1
    print(f"Verified recursive membership against the obstruction theorem on {cases} decorated orders.")
