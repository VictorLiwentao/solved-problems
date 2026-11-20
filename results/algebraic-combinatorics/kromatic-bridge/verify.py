"""Compare the full induced-independence decks of two explicit graph pairs."""
from collections import Counter
from itertools import combinations


def graph(n, edges):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def complement(adj):
    full = (1 << len(adj)) - 1
    return [full ^ (1 << v) ^ neighbors for v, neighbors in enumerate(adj)]


def independence_deck(adj):
    # Encode I(G[S]) at a base larger than every coefficient. The ordinary
    # vertex recurrence then gives the entire polynomial as one integer.
    n = len(adj)
    base = (1 << n) + 1
    polynomials = [1] + [0] * ((1 << n) - 1)
    for subset in range(1, 1 << n):
        bit = subset & -subset
        v = bit.bit_length() - 1
        rest = subset ^ bit
        polynomials[subset] = polynomials[rest] + base * polynomials[rest & ~adj[v]]
    return Counter(polynomials)


def witness(m, root):
    # 0,...,7 are b0,c0,a1,b1,c1,a2,b2,c2. The three remaining
    # tree vertices are the original leaves at b0,b1,b2.
    tree = [(i, i + 1) for i in range(7)] + [(0, 8), (3, 9), (6, 10)]
    clique = list(combinations(range(11, 11 + m), 2))
    return complement(graph(11 + m, tree + clique + [(root, 11)]))


if __name__ == "__main__":
    for m in (3, 4, 5):
        first = independence_deck(witness(m, 2))
        second = independence_deck(witness(m, 5))
        assert first == second
        print(f"Order {11+m}: all {sum(first.values())} induced-subgraph polynomials match as multisets.")
