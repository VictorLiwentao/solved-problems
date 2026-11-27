"""Compare linear-extension descent tests with independently enumerated colored chains."""
from functools import lru_cache
from itertools import combinations, permutations, product


def all_orders(n):
    pairs = list(combinations(range(n), 2))
    orders = set()
    for present in product((False, True), repeat=len(pairs)):
        relation = {p for p, active in zip(pairs, present) if active}
        for k in range(n):
            relation.update((i, j) for i in range(k) for j in range(k + 1, n)
                            if (i, k) in relation and (k, j) in relation)
        orders.add(frozenset(relation))
    return orders


def chain_language(n, covers, labels):
    language = set()

    def follow(v, word):
        for length in range(len(word) + 1):
            language.update(tuple(word[i] for i in positions)
                            for positions in combinations(range(len(word)), length))
        for a, b in covers:
            if a == v:
                follow(b, word + (labels[a] > labels[b],))

    for vertex in range(n):
        follow(vertex, ())
    return language


@lru_cache(maxsize=None)
def cut_possible(descents, schedule):
    # A letter False is an increasing block, True a decreasing block.
    n = len(descents) + 1
    stops = {0}
    for direction in schedule:
        next_stops = set(stops)
        for start in stops:
            for end in range(start + 1, n + 1):
                if end > start + 1 and descents[end - 2] != direction:
                    break
                next_stops.add(end)
        stops = next_stops
    return n in stops


if __name__ == "__main__":
    cases = schedules_tested = 0
    for n in range(1, 5):
        words = list(permutations(range(n)))
        schedules = [s for k in range(n + 1) for s in product((False, True), repeat=k)]
        for order in all_orders(n):
            covers = [(a, b) for a, b in sorted(order)
                      if not any((a, i) in order and (i, b) in order for i in range(a + 1, b))]
            extensions = [w for w in words if all(w.index(a) < w.index(b) for a, b in covers)]
            for labels in words:
                support = {tuple(labels[a] > labels[b] for a, b in zip(w, w[1:])) for w in extensions}
                language = chain_language(n, covers, labels)
                for s in schedules:
                    feasible = any(cut_possible(descents, s) for descents in support)
                    assert feasible == (tuple(not direction for direction in s) not in language)
                cases += 1
                schedules_tested += len(schedules)
    print(f"Verified {schedules_tested} schedules over {cases} orders with vertex labelings, through four vertices.")
