"""Exact checks for labeled compositions. The limit calculator accepts clipped-size DFAs."""

from collections import Counter
from itertools import combinations
from math import comb, factorial

import sympy as sp


x, t = sp.symbols("x t")


def limit_function(transitions, accepting, start=0):
    """Return the rational function R(x) for a deterministic finite automaton.

    Column j-1 describes a block of size j. The final column includes all larger sizes.
    The limiting labeled probability is R(log(2)).
    """
    states = len(transitions)
    k = len(transitions[0])
    if k < 2 or any(len(row) != k for row in transitions):
        raise ValueError("use a rectangular transition table with at least two letters")
    weights = [x**j / factorial(j) for j in range(1, k)]
    weights.append(1 - sum(weights))
    p = sp.zeros(states)
    for state, row in enumerate(transitions):
        for target, weight in zip(row, weights):
            p[state, target] += weight
    f = sp.Matrix([int(state in accepting) for state in range(states)])
    # The Abel mean retains the stationary projections even for periodic states.
    series = ((sp.eye(states) - t*p).inv() * f)[start]
    return sp.factor(sp.cancel((1 - t)*series).subs(t, 1))


def labeled_counts(transitions, accepting, n):
    """Count accepted structures by choosing the labels of the first block."""
    table = [[int(state in accepting) for state in range(len(transitions))]]
    k = len(transitions[0])
    for size in range(1, n + 1):
        following = []
        for row in transitions:
            following.append(sum(comb(size, j) * table[size-j][row[min(j, k)-1]]
                                 for j in range(1, size + 1)))
        table.append(following)
    return [row[0] for row in table]


def ordered_partitions(n):
    """Generate by inserting the last label. Deleting that label gives a unique parent."""
    if n == 0:
        yield ()
        return
    for parent in ordered_partitions(n - 1):
        for i in range(len(parent) + 1):
            yield parent[:i] + ((n,),) + parent[i:]
        for i, block in enumerate(parent):
            yield parent[:i] + (block + (n,),) + parent[i+1:]


def check_automata():
    # Each direct predicate is evaluated independently on the actual block sizes.
    def first_nonsingleton_is_pair(sizes):
        return next((j for j in sizes if j > 1), 0) == 2

    def mixed_periodic(sizes):
        return bool(sizes) and (sizes[0] != 1 or len(sizes) % 2 == 1)

    cases = [
        ("all", [[0, 0]], {0}, 1, lambda sizes: True),
        ("first singleton", [[1, 2], [1, 1], [2, 2]], {1}, x,
         lambda sizes: bool(sizes) and sizes[0] == 1),
        ("last singleton", [[1, 0], [1, 0]], {1}, x,
         lambda sizes: bool(sizes) and sizes[-1] == 1),
        ("even blocks", [[1, 1], [0, 0]], {0}, sp.Rational(1, 2),
         lambda sizes: len(sizes) % 2 == 0),
        ("first nonsingleton is a pair", [[0, 1, 2], [1, 1, 1], [2, 2, 2]], {1},
         x*x / (2*(1-x)), first_nonsingleton_is_pair),
        ("multiple recurrent classes", [[1, 3], [2, 2], [1, 1], [3, 3]], {1, 3},
         1-x/2, mixed_periodic),
    ]
    exact = {}
    for name, matrix, accepting, expected, _ in cases:
        assert sp.cancel(limit_function(matrix, accepting) - expected) == 0, name
        exact[name] = labeled_counts(matrix, accepting, 32)
    for n in range(8):
        brute = Counter()
        for partition in ordered_partitions(n):
            sizes = tuple(map(len, partition))
            for name, _, _, _, predicate in cases:
                brute[name] += predicate(sizes)
        for name in exact:
            assert brute[name] == exact[name][n], (n, name)
    for n in range(33):
        assert 2*exact["even blocks"][n] - exact["all"][n] == (-1)**n
        if n:
            assert exact["first singleton"][n] == n * exact["all"][n-1]
    print("Six symbolic limits and 48 labeled enumeration comparisons passed.")
    print("The singleton and block-parity coefficient identities agree through size 32.")


def check_first_order_realization():
    # Realize 3/4 - x with K=3, using a pair as the marker.
    # The two other letters represent singleton and size-at-least-three blocks.
    # (3/4-x)*(11/8+x/2) = 1/32 + (1-x-x^2/2).
    v = sp.Symbol("v")
    good_terms = [(1, 0, 0), (32, 0, 1)]
    bad_terms = [(11, 0, 0), (48, 1, 0), (16, 2, 0)]
    tags = iter(combinations(range(9), 4))
    used_words = set()

    def words_and_weight(terms):
        counts = Counter()
        for multiplicity, singles, large in terms:
            for _ in range(multiplicity):
                tag_positions = set(next(tags))
                tag = tuple("s" if i in tag_positions else "L" for i in range(9))
                word = tag + ("s",) * singles + ("L",) * large
                assert word not in used_words
                used_words.add(word)
                counts[word.count("s"), word.count("L")] += 1
        return sum(count * x**a * v**b for (a, b), count in counts.items())

    good = words_and_weight(good_terms)
    bad = words_and_weight(bad_terms)
    probability = sp.cancel((good / (good + bad)).subs(v, 1-x-x*x/2))
    assert sp.cancel(probability - (sp.Rational(3, 4) - x)) == 0
    print(f"{len(used_words)} distinct gap words realize the limit 3/4 - log(2).")


if __name__ == "__main__":
    check_automata()
    check_first_order_realization()
