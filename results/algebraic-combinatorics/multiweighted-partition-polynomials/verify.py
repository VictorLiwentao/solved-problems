"""Compare the formula with Möbius inversion in the actual finite poset."""
from fractions import Fraction
from itertools import product
from math import comb, factorial


def partitions(n):
    if n == 0:
        yield ()
        return
    bit = 1 << (n - 1)
    for blocks in partitions(n - 1):
        yield blocks + (bit,)
        for i in range(len(blocks)):
            yield blocks[:i] + (blocks[i] | bit,) + blocks[i + 1:]


def weights(total, r):
    if r == 1:
        yield (total,)
        return
    for i in range(total + 1):
        for tail in weights(total - i, r - 1):
            yield (i,) + tail


def below(lower, upper):
    for big, capacity in upper:
        pieces = [w for small, w in lower if small & big]
        if any(small & big and small & ~big for small, _ in lower):
            return False
        if any(sum(entries) > limit for entries, limit in zip(zip(*pieces), capacity)):
            return False
    return True


def enumerate_poset(n, r):
    layers = [[] for _ in range(n)]
    for blocks in partitions(n):
        for colors in product(*(weights(b.bit_count() - 1, r) for b in blocks)):
            layers[n - len(blocks)].append(tuple(zip(blocks, colors)))
    previous = []
    totals = []
    for rank, layer in enumerate(layers):
        values = [(x, -sum(mu for y, mu in previous if below(y, x)) if rank else 1)
                  for x in layer]
        previous.extend(values)
        totals.append(sum(mu for _, mu in values))
    return totals, len(previous)


def formula(n, r):
    # Compute H=Q^(-n) by Q H' = -n Q' H, then multiply by exp(-nu).
    q = [Fraction(comb(r - 2, j), factorial(j + 1)) for j in range(r - 1)]
    h = [Fraction(1)]
    for k in range(1, n):
        terms = ((k + (n - 1) * j) * q[j] * h[k - j]
                 for j in range(1, min(k, len(q) - 1) + 1))
        h.append(-sum(terms, start=Fraction(0)) / k)
    return [Fraction(factorial(n - 1), factorial(n - 1 - k))
            * sum(h[k - j] * Fraction((-n)**j, factorial(j)) for j in range(k + 1))
            for k in range(n)]


if __name__ == "__main__":
    checks = elements = 0
    for n in range(1, 6):
        for r in range(2, 6):
            observed, count = enumerate_poset(n, r)
            assert observed == formula(n, r), (n, r, observed, formula(n, r))
            checks += 1
            elements += count
    print(f"{checks} complete posets, {elements} weighted partitions, all coefficients agree.")
