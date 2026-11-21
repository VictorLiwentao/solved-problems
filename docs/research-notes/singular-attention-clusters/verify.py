"""Enumerate a full sampled layer and verify the exit and variance formulas."""
from fractions import Fraction as F
from itertools import product


def mean(xs):
    return sum(xs) / len(xs)


def variance(xs):
    center = mean(xs)
    return mean([(x - center) ** 2 for x in xs])


groups = [0, 0, 1]
positions = list(map(F, [0, 3, 8]))
step = F(2, 5)
# Row weights of 2 inside a fiber and 1 outside (beta times the gap is log 2).
rows = []
for group in groups:
    weights = [2 if group == other else 1 for other in groups]
    rows.append([F(weight, sum(weights)) for weight in weights])

survival = F(0)
weighted_variance = F(0)
for choices in product(range(3), repeat=3):
    probability = rows[0][choices[0]] * rows[1][choices[1]] * rows[2][choices[2]]
    if all(groups[i] == groups[j] for i, j in enumerate(choices)):
        survival += probability
        updated = [(1 - step) * positions[i] + step * positions[j]
                   for i, j in enumerate(choices)]
        weighted_variance += probability * variance(updated[:2])

assert survival == F(4, 5) ** 2 * F(1, 2)
assert weighted_variance / survival == ((1 - step) ** 2 + step ** 2 / 2) * variance(positions[:2])
print("Exact one-layer survival and hidden-coordinate variance verified across 27 outcomes.")
