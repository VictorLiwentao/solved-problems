"""Exercise the finite-type capacity invariant, including late bursts of corruption."""
from collections import Counter
from fractions import Fraction
from itertools import product
import random


def exercise(seed):
    rng = random.Random(seed)
    types = list(product((0, 1), repeat=3))
    infinite = types[2:]
    delta = Fraction(1, 12)
    warmup = 400
    finite = types[:2] * 4
    rng.shuffle(finite)
    before, later, spent = Counter(), Counter(), Counter()
    errors = [0, 0, 0]

    def observe(counts, pattern):
        counts[pattern] += 1
        for i, bit in enumerate(pattern):
            errors[i] += 1 - bit

    for _ in range(warmup):
        observe(before, rng.choice(infinite[3:]))
    for n in range(warmup, 1500):
        capacities = {v: int(delta * before[v] + (1 + delta) * later[v]) for v in infinite}
        protected = [i for i, e in enumerate(errors) if e <= delta*n/(4*(1+delta)*3)]
        choices = [v for v in infinite if capacities[v] > spent[v] and all(v[i] for i in protected)]
        assert choices
        chosen = rng.choice(choices)
        spent[chosen] += 1
        for i in range(3):
            debits = sum(k for v, k in spent.items() if not v[i])
            allowed = sum(delta*before[v] + (1+delta)*later[v] for v in infinite if not v[i])
            assert debits <= allowed
        if n % 113 == 0 and finite:
            demo = finite.pop()
        elif n % 301 < 10:
            demo = rng.choice(infinite)
        else:
            demo = rng.choice(infinite[3:])
        observe(later, demo)


if __name__ == '__main__':
    for seed in range(8):
        exercise(seed)
    print('Capacity, eligibility and per-target debits verified over 8,800 post-switch rounds.')
