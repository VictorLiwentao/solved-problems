"""Check the finite charge, cyclicity, and threshold calculations."""

from itertools import combinations, product


def check_small_polymorphisms():
    checked = 0
    # For arity three, addition against singletons determines the
    # remaining four nonsingleton values. Vary each of those freely
    # in the small exhaustive two-input test as a separate check.
    for mass in range(2, 6):
        for arity in range(1, 4):
            length = 2**arity
            rows = [(i, j, i | j) for i, j in combinations(range(length), 2)
                    if not i & j]
            for weights in product(range(mass + 1), repeat=arity):
                if sum(weights) != mass:
                    continue
                values = [sum(w for j, w in enumerate(weights) if mask >> j & 1)
                          for mask in range(length)]
                assert all(values[i] + values[j] == values[k] for i, j, k in rows)
                rotated = [((mask << 1) % length) | (mask >> (arity - 1))
                           for mask in range(length)]
                assert all(values[i] == values[j] for i, j in enumerate(rotated)) == (
                    len(set(weights)) == 1)
                checked += 1
            if arity <= 2:
                for middle in product(range(mass + 1), repeat=length - 2):
                    values = (0, *middle, mass)
                    additive = all(values[i] + values[j] == values[k] for i, j, k in rows)
                    weights = [values[1 << j] for j in range(arity)]
                    predicted = [sum(w for j, w in enumerate(weights) if mask >> j & 1)
                                 for mask in range(length)]
                    assert additive == (list(values) == predicted)
    return checked


def check_thresholds():
    checked = 0
    for size in range(1, 101):
        if size % 3 == 0:
            continue
        for x in range(size + 1):
            for y in range(size - x + 1):
                marks = {3*t > size for t in (x, y, size - x - y)}
                assert marks == {False, True}
                checked += 1
    return checked


if __name__ == "__main__":
    print(f"Verified {check_small_polymorphisms()} weighted operations.")
    print(f"Verified {check_thresholds()} exact-one threshold triples.")
