"""Exact sparse-polynomial implementation of Burghart's three recursions."""
from collections import Counter
from functools import cache


def add(*terms):
    result = Counter()
    for term in terms:
        result.update(term)
    return {key: value for key, value in result.items() if value}


ONE = {(0, 0, 0): 1}
X = {(1, 0, 0): 1}
Y = {(0, 1, 0): 1}
Z = {(0, 0, 1): 1}


def multiply(*terms):
    result = ONE
    for term in terms:
        out = Counter()
        for (a, b, c), v in result.items():
            for (i, j, k), w in term.items():
                out[a+i, b+j, c+k] += v * w
        result = {key: value for key, value in out.items() if value}
    return result


def complement(poly):
    return add(ONE, {key: -v for key, v in poly.items()})


@cache
def invariants(tree):
    if not tree:
        return Y, Z, ONE
    children = [invariants(branch) for branch in tree]
    parts = [a for a, p, m in children]
    admissible = add(Y, multiply(X, *parts))
    p_over_z = complement(multiply(*(complement(p) for a, p, m in children)))
    terms = [multiply(X, m, *parts[:i], *parts[i+1:]) for i, (_, _, m) in enumerate(children)]
    return admissible, multiply(Z, p_over_z), add(p_over_z, *terms)


leaf = ()
b, c = (leaf, leaf), (leaf,)
d = (leaf, c)
u, v = (b, (d,)), (c, (leaf, (b,)))
first, second = ((u, u), (v, v)), ((u, v), (u, v))
assert invariants(u)[0] == invariants(v)[0] and invariants(u)[2] != invariants(v)[2]
assert invariants(first) == invariants(second)
print("All coefficients of A, p and M agree on the two 39-vertex trees.")
