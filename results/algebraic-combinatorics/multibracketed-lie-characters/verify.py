"""Check the character sum against the Möbius function of permutation-fixed intervals."""
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial, prod
from pathlib import Path
from runpy import run_path

posets = run_path(str(Path(__file__).resolve().parent.parent
                      / "multiweighted-partition-polynomials" / "verify.py"))
weights = posets["weights"]


def partitions(n, least=1):
    if not n:
        yield ()
    for i in range(least, n + 1):
        for tail in partitions(n - i, i):
            yield (i,) + tail


def z(eta):
    return prod(j**m * factorial(m) for j, m in Counter(eta).items())


def profiles(lam):
    n = sum(lam)
    m = Counter(lam)
    possible = sorted({j for j in range(1, n + 1) if any(t % j == 0 for t in lam)})
    terms = [(i, e, i * (d - 1)) for i in possible for d in range(2, n//i + 1)
             for e in partitions(d) if all(i*j in possible for j in e)]

    def enumerate_counts(j, balance, counts):
        if balance == 0:
            roots = Counter({1: 1})
            total = m.copy()
            children = Counter()
            for (i, e), a in counts.items():
                total[i] += a
                children[i] += e.count(1) * a
                for s in e:
                    if s != 1:
                        roots[i*s] += a
            if any(roots[i] <= 0 or total[i] != roots[i] + children[i] for i in total):
                return
            if any(i not in total for i in roots):
                return
            factor = Fraction(z(lam))
            for i, size in total.items():
                factor *= Fraction(roots[i] * factorial(size - 1), factorial(m[i]))
            for (i, e), a in counts.items():
                factor *= Fraction((-1)**(a*len(e)), factorial(a)*z(e)**a)
            yield factor, dict(counts)
            return
        if j == len(terms):
            return
        i, e, cost = terms[j]
        yield from enumerate_counts(j + 1, balance, counts)
        for a in range(1, balance//cost + 1):
            counts[i, e] = a
            yield from enumerate_counts(j + 1, balance - a * cost, counts)
        counts.pop((i, e), None)

    return list(enumerate_counts(0, n - 1, {}))


def fixed_mobius(lam, colors):
    n = sum(lam)
    perm = []
    for length in lam:
        start = len(perm)
        perm.extend([*range(start + 1, start + length), start])
    def act(block):
        return sum(1 << perm[i] for i in range(n) if block & (1 << i))

    layers = [[] for _ in range(n)]
    for blocks in posets["partitions"](n):
        for choices in product(*(weights(b.bit_count() - 1, colors) for b in blocks)):
            element = tuple(zip(blocks, choices))
            if {(act(b), w) for b, w in element} == set(element):
                layers[n-len(blocks)].append(element)
    previous = []
    for rank, layer in enumerate(layers):
        values = [(a, -sum(mu for b, mu in previous if posets["below"](b, a)) if rank else 1)
                  for a in layer]
        previous.extend(values)
    return {a[0][1]: (-1)**(len(lam)-1)*mu for a, mu in values}


@cache
def homogeneous(i, degree, values):
    return sum(prod(v**(a*i) for v, a in zip(values, w))
               for w in weights(degree, len(values)))


if __name__ == "__main__":
    classes = 0
    components = 0
    for n in range(2, 6):
        for lam in partitions(n):
            terms = profiles(lam)
            expected = fixed_mobius(lam, 3)
            for a, b in product(range(n), repeat=2):
                # Homogeneity and interpolation certify every 3-color multidegree.
                x = (a, b, 1)
                actual = sum(f * prod(homogeneous(i, sum(e)-1, x)**s
                                      for (i, e), s in t.items()) for f, t in terms)
                target = sum(c * prod(v**d for v, d in zip(x, w))
                             for w, c in expected.items())
                assert actual == target, (lam, x, actual, target)
            classes += 1
            components += len(expected)
    print(f"{classes} cycle types, {components} character values, all agree with fixed-poset inversion.")
