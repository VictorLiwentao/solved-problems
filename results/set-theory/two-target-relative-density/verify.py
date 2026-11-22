"""Enumerate the finite top-level tie event used in the forcing manuscript.

The finite sum uses the probabilities of falling below the level, hitting it
with either mark, or landing above it. It never samples a forcing extension.
"""
from fractions import Fraction
from itertools import product


def enumerated_tie_probability(a_size, b_size, level):
    reach = Fraction(1, 2**level)
    probabilities = (1 - reach, reach / 4, reach / 4, reach / 2)
    total = Fraction(0)
    for states in product(range(4), repeat=b_size):
        left, right = states[:a_size], states[a_size:]
        if left.count(1) != 1 or right.count(2) != 1:
            continue
        if states.count(0) != b_size - 2:
            continue
        weight = Fraction(1)
        for state in states:
            weight *= probabilities[state]
        total += weight
    return total


def main():
    cases = 0
    for b_size in range(2, 8):
        level = b_size.bit_length() - 1
        reach = Fraction(1, 2**level)
        for a_size in range(1, b_size):
            event = enumerated_tie_probability(a_size, b_size, level)
            formula = a_size * (b_size - a_size) * (reach / 4)**2 * (1 - reach)**(b_size - 2)
            assert event == formula and event > 0
            cases += 1
    print(f"Verified the finite tie law exactly for {cases} splits.")


if __name__ == "__main__":
    main()
