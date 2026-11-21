"""Verify ordered contact counts and one finite-temperature comparison."""
from itertools import product
from math import exp, log1p, sqrt


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def restricted_scaled_loss(q, s, beta):
    sizes = [2] * (q-1) + [s+2]
    n = sum(sizes)
    return sum(m * log1p(exp(-beta) * ((n-m) + (m-1)*exp(-beta/(m-1))))
               * exp(beta) for m in sizes)


def competitor(q, s, beta):
    t = beta**(-0.75)
    points = []
    for i, sign in product(range(q), [-1, 1]):
        x = [0.0]*q + [-t]*s
        x[i] = sign*sqrt(1-s*t*t)
        points.append(x)
    for i in range(s):
        x = [0.0]*q + [1.0 if j == i else -t for j in range(s)]
        norm = sqrt(dot(x, x))
        points.append([v/norm for v in x])
    return points


for q, s in product(range(2, 12), range(1, 9)):
    sizes = [2] * (q-1) + [s+2]
    n = sum(sizes)
    contacts = sum(m * (n-m) for m in sizes)
    assert contacts - 4*q*(q-1) == 4*s*(q-1)
q, s, beta = 2, 2, 250.0
points = competitor(q, s, beta)
scaled = sum(log1p(sum(exp(beta*(dot(x, y)-1)) for j, y in enumerate(points) if j != i))
             * exp(beta) for i, x in enumerate(points))
assert scaled < restricted_scaled_loss(q, s, beta)
print("Verified 80 exact contact counts and a finite-temperature comparison in dimension four.")
