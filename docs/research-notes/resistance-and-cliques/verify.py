"""Check the resistance/adjacency multisets on unreduced graphs over rationals."""
from itertools import combinations, product

from sympy import Matrix


def graph(m, k):
    adjacency = [set() for _ in range(2*m)]
    colors = [(i % k + b) % k for i in range(m) for b in (0,1)]

    def edge(u, v):
        adjacency[u].add(v)
        adjacency[v].add(u)

    for i, j in combinations(range(m), 2):
        sign = int(i % k == j % k)
        for b in (0,1):
            edge(2*i+b, 2*j+(b ^ sign))
        for _ in range(2):
            for b in (0,1):
                u, v = 2*i+b, 2*j+(b ^ sign ^ 1)
                z = len(adjacency)
                adjacency.append(set())
                colors.append(next(c for c in range(k) if c not in (colors[u], colors[v])))
                edge(u, z)
                edge(z, v)
    assert len(adjacency) == 2*m*m
    assert sum(map(len, adjacency)) == 10*m*(m-1)
    assert all(colors[u] != colors[v] for u in range(len(adjacency)) for v in adjacency[u])
    assert all(2*j in adjacency[2*i] for i, j in combinations(range(k), 2))
    return adjacency


def joint_signatures(adj):
    size = len(adj)
    ground = size-1
    mat = Matrix(ground, ground, lambda i,j: len(adj[i]) if i == j else -int(j in adj[i]))
    inv = mat.inv()
    def entry(i,j):
        return 0 if ground in (i,j) else inv[i,j]
    def message(i,j):
        return (entry(i,i) + entry(j,j) - 2*entry(i,j), j in adj[i])
    return [tuple(sorted([message(i,j), message(i,j+1)]))
            for i,j in product(range(size), range(0,size,2))]


if __name__ == "__main__":
    for m in (2,3,4,5):
        baseline = joint_signatures(graph(m, 2))
        fibers = m*m
        for sheet_zero in range(0, 2*fibers, 2):
            start = sheet_zero*fibers
            assert baseline[start:start+fibers] == baseline[start+fibers:start+2*fibers]
        for k in range(3, m+1):
            assert joint_signatures(graph(m,k)) == baseline
    print("All clique/color certificates and exact joint resistance/adjacency signatures agree for m = 2 through 5.")
