"""Exact finite checks for the privacy mechanisms used in the column examples."""

from fractions import Fraction
from itertools import product


def check_response():
    checks = 0
    for count in range(2, 8):
        for ratio in map(Fraction, (1, "3/2", 2, 5)):
            for delta in map(Fraction, (0, "1/8", "1/3", 1)):
                # Independently assemble the mixture, then test the closed formula.
                laws = [
                    [
                        (1 - delta) * (ratio if i == j else 1) / (ratio + count - 1)
                        + delta * (i == j)
                        for j in range(count)
                    ]
                    for i in range(count)
                ]
                success = (ratio + (count - 1) * delta) / (ratio + count - 1)
                for i, law in enumerate(laws):
                    assert sum(law) == 1 and law[i] == success
                    for j, other in enumerate(laws):
                        if i == j:
                            continue
                        # For discrete laws the worst event is the set of
                        # coordinates with positive signed mass.
                        worst = sum(max(x - ratio * y, 0) for x, y in zip(law, other))
                        assert worst == delta
                assert success + (count - 1) * (success - delta) / ratio == 1
                checks += 1
    return checks


def check_uniform_record():
    checks = 0
    for length in range(1, 6):
        records = list(product(range(3), repeat=length))
        histograms = {record: [record.count(j) for j in range(3)] for record in records}
        for record, counts in histograms.items():
            for pos in range(length):
                for replacement in range(3):
                    if replacement == record[pos]:
                        continue
                    neighbor = record[:pos] + (replacement,) + record[pos + 1 :]
                    other_counts = histograms[neighbor]
                    # Total variation between empirical laws must be exactly 1/m.
                    assert sum(max(x - y, 0) for x, y in zip(counts, other_counts)) == 1
                    checks += 1
    return checks


if __name__ == "__main__":
    print(f"Verified {check_response()} sharp finite randomized-response channels.")
    print(f"Verified uniform-record release on {check_uniform_record()} ordered neighbor pairs.")
