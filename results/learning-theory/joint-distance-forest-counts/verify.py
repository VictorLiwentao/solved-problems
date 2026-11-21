"""Compare full distance pairs on two explicit cones with exact rational inverses."""
from fractions import Fraction as Q

def lifted_rim(twist):
    edges = []
    next_vertex = 3
    for side, (u, v) in enumerate(((0, 1), (1, 2), (2, 0))):
        flip = -1 if twist and side == 0 else 1
        edges.append((u, v, flip))
        for _ in range(21):
            a, b, c = range(next_vertex, next_vertex + 3)
            next_vertex += 3
            edges.extend(((u, a, 1), (a, b, 1), (b, c, 1), (c, v, -flip)))
    adj = [set() for _ in range(2 * next_vertex)]
    for u, v, sign in edges:
        for sheet in (0, 1):
            i, j = 2*u + sheet, 2*v + (sheet ^ (sign < 0))
            adj[i].add(j)
            adj[j].add(i)
    return adj

def inverse_columns(adj):
    # The cone hub is grounded. Eliminate low-degree interiors before terminals.
    order = list(range(6, len(adj))) + list(range(6))
    where = {v: i for i, v in enumerate(order)}
    rows = [{where[u]: Q(-1) for u in adj[v]} for v in order]
    for i, v in enumerate(order):
        rows[i][i] = Q(1 + len(adj[v]))
    factors = []
    for i, row in enumerate(rows):
        pivot = row[i]
        upper = [(j, value) for j, value in row.items() if j > i and value]
        factors.append((pivot, [(j, value/pivot) for j, value in upper]))
        for j, a in upper:
            for k, b in upper:
                rows[j][k] = rows[j].get(k, 0) - a*b/pivot
    columns = []
    for source in range(len(adj)):
        x = [Q(0)] * len(adj)
        x[where[source]] = Q(1)
        for i, (_, neighbors) in enumerate(factors):
            if x[i]:
                for j, value in neighbors:
                    x[j] -= value*x[i]
        for i, (pivot, _) in enumerate(factors):
            x[i] /= pivot
        for i in reversed(range(len(adj))):
            x[i] -= sum(value*x[j] for j, value in factors[i][1])
        col = [x[where[j]] for j in range(len(adj))]
        for j in range(len(adj)):
            assert (1 + len(adj[j]))*col[j] - sum(col[k] for k in adj[j]) == (j == source)
        columns.append(col)
    return columns

def distances(adj, inv, i, j):
    shortest = 0 if i == j else 1 if j in adj[i] else 2
    return shortest, inv[i][i] + inv[j][j] - 2*inv[i][j]

def triangles(adj):
    return sum(len(nbr & adj[v]) for nbr in adj for v in nbr) // 6

a, b = lifted_rim(False), lifted_rim(True)
ia, ib = inverse_columns(a), inverse_columns(b)
assert [ia[i][i] for i in range(len(a))] == [ib[i][i] for i in range(len(b))]
for i in range(len(a)):
    for v in range(0, len(a), 2):
        assert sorted(distances(a, ia, i, j) for j in (v, v+1)) == sorted(
            distances(b, ib, i, j) for j in (v, v+1))
# Every rim edge contributes exactly one additional triangle on coning.
assert len(a) == len(b) == 384
assert sum(map(len, a)) == sum(map(len, b))
assert triangles(a) == 2 and triangles(b) == 0
print("All paired distances agree exactly on the two 385-vertex cones. Triangle counts differ by two.")
