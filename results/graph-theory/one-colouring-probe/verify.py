"""Check the two leading coefficients independently on small test and base graphs."""
from collections import defaultdict
from itertools import combinations, product


def induced_count(n, edges, k, probe):
    words = [w for w in product(range(k), repeat=n) if all(w[a] != w[b] for a, b in edges)]
    # These checks use probes on two vertices. Count the unordered pairs by Hamming distance.
    adjacent = 0
    for i in range(n):
        fibres = defaultdict(int)
        for w in words:
            fibres[w[:i]+w[i+1:]] += 1
        adjacent += sum(s*(s-1)//2 for s in fibres.values())
    if probe == "edge":
        return adjacent
    return len(words)*(len(words)-1)//2 - adjacent


def differences(values):
    result = []
    while values:
        result.append(values[0])
        values = [b-a for a, b in zip(values, values[1:])]
    while result and result[-1] == 0:
        result.pop()
    return result


for probe in ("edge", "nonedge"):
    previous_degree = -1
    for n in range(1, 5):
        edges = list(combinations(range(n), 2))
        leading = {}
        degrees = set()
        for mask in range(1 << len(edges)):
            chosen = [e for i, e in enumerate(edges) if mask & (1 << i)]
            # All counts have degree at most 2n by the colour-partition expression.
            coeffs = differences([induced_count(n, chosen, k, probe) for k in range(2*n+1)])
            if not coeffs:
                assert probe == "nonedge" and n == 1
                continue
            degrees.add(len(coeffs)-1)
            top = tuple(coeffs[-2:])
            assert leading.setdefault(len(chosen), top) == top
        if degrees:
            degree, = degrees
            assert degree > previous_degree
            previous_degree = degree
            assert len(set(leading.values())) == len(leading)
print("For edge and nonedge probes, the two leading terms separate order and edge count through four vertices.")
