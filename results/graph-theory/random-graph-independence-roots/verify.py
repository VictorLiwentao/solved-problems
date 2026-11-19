"""Exact checks for the random-graph independence-root argument."""

from fractions import Fraction
from itertools import combinations
from math import comb, factorial

from sympy import Matrix, expand, factor, integer_nthroot, simplify, symbols


def expected_count(n, s, q):
    return comb(n, s) * q**comb(s, 2)


def normalized_second_moment(n, s, q):
    """E[X_s^2] / E[X_s]^2 from the intersection size of two s-sets."""
    denominator = comb(n, s)
    return sum(
        Fraction(comb(s, overlap) * comb(n-s, s-overlap), denominator)
        / q**comb(overlap, 2)
        for overlap in range(s+1)
    )


def check_small_graphs(n, q):
    edges = list(combinations(range(n), 2))
    forbidden = [[] for _ in range(n+1)]
    for subset in range(1 << n):
        mask = sum(1 << i for i, (v, w) in enumerate(edges)
                   if subset & (1 << v) and subset & (1 << w))
        forbidden[subset.bit_count()].append(mask)

    first = [0] * (n+1)
    second = [0] * (n+1)
    total_weight = 0
    for graph in range(1 << len(edges)):
        present = graph.bit_count()
        weight = ((q.denominator - q.numerator)**present
                  * q.numerator**(len(edges)-present))
        total_weight += weight
        for s, masks in enumerate(forbidden):
            count = sum((mask & graph) == 0 for mask in masks)
            first[s] += weight * count
            second[s] += weight * count**2

    assert total_weight == q.denominator**len(edges)
    for s in range(n+1):
        mean = expected_count(n, s, q)
        assert Fraction(first[s], total_weight) == mean
        assert Fraction(second[s], total_weight) == mean**2 * normalized_second_moment(n, s, q)


def check_algebra():
    a0, a1, a2, a3, a4, a5 = symbols("a0:6")
    hu = Matrix([[a1, a3, a5], [a0, a2, a4], [0, a1, a3]])
    assert hu[:2, :2].det() == a1*a2-a0*a3
    assert expand(hu.det() - (a1*a2*a3-a1**2*a4-a0*a3**2+a0*a1*a5)) == 0

    q, lam, k, n = symbols("q lambda k n", positive=True)
    forward_k = (n-k+1) * q**(k-1) / k
    forward_k_minus_2 = (n-k+3) * q**(k-3) / (k-2)
    ratio = k*(n-k+3) / ((k-2)*(n-k+1)*q**2)
    assert simplify(forward_k_minus_2 / forward_k - ratio) == 0

    coefficients = [q**comb(i, 2) for i in range(6)]
    determinant = hu.det().subs(dict(zip((a0, a1, a2, a3, a4, a5), coefficients)))
    assert expand(determinant-q**4*(q**2-1)*(q**4+q**2-1)) == 0

    delta = symbols("delta")
    y = [1, lam, lam*q, lam*q**3]
    translated = [sum(delta**(j-i) * y[i] / factorial(j-i) for i in range(j+1))
                  for j in range(4)]
    shifted_d2 = translated[1]*translated[2]-translated[0]*translated[3]
    assert factor(shifted_d2.subs(delta, 0) - lam*q*(lam-q**2)) == 0


def check_finite_bound():
    # Exact instance of the elementary proof. No graph sampling is needed.
    q = Fraction(1, 2)
    k = 32
    n = int(integer_nthroot(factorial(k) * 2**(comb(k, 2)-3), k)[0])
    assert n == 555422
    epsilon = Fraction(1, 10)
    ratio = (expected_count(n, k-1, q) * expected_count(n, k-2, q)
             / expected_count(n, k-3, q))
    assert (1+epsilon)**2 / (1-epsilon) * ratio < 1

    exists = 1 / normalized_second_moment(n, k, q)
    larger = expected_count(n, k+1, q)
    deviations = sum(normalized_second_moment(n, k-j, q)-1 for j in (1, 2, 3))
    lower_bound = exists - larger - deviations / epsilon**2
    assert lower_bound > Fraction(1032, 10000)
    return n


if __name__ == "__main__":
    check_algebra()
    for absence_probability in (Fraction(1, 2), Fraction(2, 3)):
        check_small_graphs(5, absence_probability)
    order = check_finite_bound()
    print("Both Hurwitz minors, the mean ratio, and the translation at zero agree.")
    print("All moments agree on all 1,024 five-vertex graphs at two edge densities.")
    print(f"At p=1/2 and n={order:,}, the exact instability lower bound exceeds 10.32%.")
