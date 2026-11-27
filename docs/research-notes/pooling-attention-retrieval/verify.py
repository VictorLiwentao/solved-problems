"""Finite checks of combinatorial coefficients, Gram certificates and Gaussian chirps."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from math import comb, factorial, sqrt

import numpy as np
from numpy.polynomial.hermite_e import hermegauss, hermeval


def check_tag_coefficients():
    # Three tag values and two distinguishable tail values.
    rng = np.random.default_rng(2026)
    for k in [2, 3, 4]:
        phi = rng.integers(-30, 31, size=(5,) * k)
        for tags in combinations_with_replacement(range(3), 3):
            tokens = [*tags, 3, 4]
            counts = Counter(tokens)
            for replacement in [False, True]:
                tuples = product(range(5), repeat=k) if replacement else permutations(range(5), k)
                direct = sum(int(phi[tuple(tokens[i] for i in row)]) for row in tuples)
                expanded = 0
                for row in product(range(5), repeat=k):
                    multiplicity = 1
                    for symbol, repeat in Counter(row).items():
                        count = counts[symbol]
                        if replacement:
                            multiplicity *= count ** repeat
                        else:
                            multiplicity *= comb(count, repeat) * factorial(repeat)
                    expanded += multiplicity * int(phi[row])
                assert direct == expanded


def check_retrieval():
    for n in range(3, 13):
        for k in range(1, n // 2 + 1):
            m = n / (2 * sqrt(k * (n-k) * (n-1)) + n-2*k)
            alpha, beta = (1-m)/(2*k), (1+m)/(2*(n-k))
            rows = np.array([np.isin(np.arange(n), row) for row in combinations(range(n), k)])
            w = np.where(rows, alpha, -beta)
            y = np.where(rows, 1, -1)
            mean = np.ones((n, n)) / n
            centered = np.eye(n) - mean
            gram = 2*m*m/(alpha+beta)*centered + m*(n-2*k)*mean
            np.testing.assert_allclose(w.T @ w / len(w), m*m*np.eye(n)/n, atol=1e-12)
            np.testing.assert_allclose(w @ gram, m*m*y, atol=1e-12)
            np.testing.assert_allclose(np.diag(gram), 1, atol=1e-12)
            assert np.linalg.matrix_rank(gram, tol=1e-10) == n - (n == 2*k)


def check_gaussian_chirp():
    # Integrate two Gaussian coordinates independently. Remaining coordinates separate.
    nodes, weights = hermegauss(96)
    weights /= np.sqrt(2*np.pi)
    x, y = nodes[:, None], nodes[None, :]
    w = np.array([3/5, 4/5])
    for d in [5, 19, 73]:
        lam = 1/sqrt(d)
        z = 1 - 2j*lam
        factor = weights[:, None]*weights[None, :]*np.exp(1j*lam*(x*x+y*y))*z**(-(d-2)/2)
        for s in [2, 3]:
            k = 2*s+1
            coeffs = [0]*k+[1]
            labels = hermeval(w[0]*x+w[1]*y, coeffs)
            observed = np.array([np.sum(factor*labels*t) for t in [x, y]])
            constant = factorial(k)/factorial(s)*z**(-d/2-1)*(1j*lam/z)**s
            np.testing.assert_allclose(observed, constant*w, rtol=1e-10, atol=1e-10)


if __name__ == '__main__':
    check_tag_coefficients()
    check_retrieval()
    check_gaussian_chirp()
    print('Tuple multiplicities, retrieval Gram certificates and Gaussian chirp integrals verified.')
