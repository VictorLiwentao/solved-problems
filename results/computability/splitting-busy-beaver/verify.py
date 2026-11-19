"""Check finite runtime recovery and the restraint rule on small tabulations."""

from itertools import product


def runtime(table, limit):
    ones = set()
    state = position = 0
    for step in range(1, limit + 1):
        transition = table[2 * state + (position in ones)]
        if transition is None:
            return step
        state, move, write = transition
        if write:
            ones.add(position)
        else:
            ones.discard(position)
        position += move
    return 0


def assign_colors(arrivals, requirements):
    """Each finite test computation queries a fixed set of negative bits."""
    colors = {}
    active = [False] * len(requirements)
    seen = [set() for _ in requirements]
    cancellations = 0
    for x in arrivals:
        for r, (_, queries) in enumerate(requirements):
            active[r] = not bool(queries & seen[r])
        eligible = [
            i for (i, queries), on in zip(requirements, active)
            if on and i <= x <= max(queries)
        ]
        selected = eligible[0] if eligible else 0
        colors[x] = selected
        for r, (i, queries) in enumerate(requirements):
            if i != selected:
                seen[r].add(x)
                if x in queries and active[r]:
                    active[r] = False
                    cancellations += 1
        assert selected <= x
    for r, (i, queries) in enumerate(requirements):
        assert seen[r] == {x for x, j in colors.items() if i != j}
        assert active[r] == (not bool(seen[r] & queries))
    return colors, cancellations


def run():
    tables = []
    for states in (1, 2):
        operations = [None, *product(range(states), (-1, 1), (0, 1))]
        tables.extend((states, table) for table in product(operations, repeat=2 * states))
    # The test dataset consists of the halts seen within six steps.
    times = {k: t for k, (_, table) in enumerate(tables) if (t := runtime(table, 6))}
    arrivals = sorted(times, key=lambda k: (times[k], k))
    requirements = [
        (2, {4, 17}), (1, {1, 7, 300}), (3, {20, 44}),
        (0, {24, 87}), (1, {2222, 5000}), (3, {5500, 5501}),
    ]
    colors, cancellations = assign_colors(arrivals, requirements)
    assert cancellations > 0 and len(set(colors.values())) >= 3
    for order, known in ((1, 1), (2, 6)):
        by_color = [
            max((t for k, t in times.items() if tables[k][0] <= order and colors[k] == i), default=0)
            for i in range(4)
        ]
        assert max(by_color) == known
        for mask in range(16):
            group = {i for i in range(4) if mask & (1 << i)}
            expected = max((by_color[i] for i in group), default=0)
            complement = max((t for i, t in enumerate(by_color) if i not in group), default=0)
            assert max(expected, complement) == known
            for slack in (0, 1, 4):
                bound = expected + slack
                recovered = 0
                for k, (states, table) in enumerate(tables):
                    if states <= order:
                        t = runtime(table, bound)
                        if t and colors[k] in group:
                            recovered = max(recovered, t)
                assert recovered == expected
    print(f"{len(tables)} tables, {len(times)} observed halts, 96 bound-recovery checks.")


if __name__ == "__main__":
    run()
