"""Check the shattering and trace-nesting steps on all ordered posets up to six points."""

from itertools import combinations


def subsets(mask):
    subset = mask
    while subset:
        yield subset
        subset = (subset - 1) & mask
    yield 0


def verify_order(above):
    n = len(above)
    all_vertices = (1 << n) - 1
    below = [sum(1 << u for u in range(n) if above[u] >> v & 1) for v in range(n)]
    closed = [all_vertices ^ (above[v] | below[v]) for v in range(n)]
    for s in subsets(all_vertices):
        vertices = [v for v in range(n) if s >> v & 1]
        if len({mask & s for mask in closed}) == 1 << len(vertices):
            assert all((above[v] & s) == 0 or (below[v] & s) == 0 for v in vertices)
        if any(above[v] & s for v in vertices):
            continue
        for u, v in combinations(range(n), 2):
            if not (above[u] >> v & 1):
                continue
            if (below[u] & s and below[v] & s) or (above[u] & s and above[v] & s):
                a, b = closed[u] & s, closed[v] & s
                assert a & b in (a, b)


def main():
    count = 0
    for n in range(1, 7):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            above = [0] * n
            for i, (u, v) in enumerate(pairs):
                if mask >> i & 1:
                    above[u] |= 1 << v
            if any(above[v] & ~above[u] for u, v in pairs if above[u] >> v & 1):
                continue
            verify_order(above)
            count += 1
    print(f"Verified shattering and antichain trace nesting on {count} naturally labelled posets.")


if __name__ == "__main__":
    main()
