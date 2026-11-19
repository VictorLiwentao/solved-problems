"""Finite marker construction with one argument function and one delay."""

from dataclasses import dataclass, field
from heapq import heappop, heappush
from itertools import combinations, count, product


def finite_orders(n):
    pairs = list(combinations(range(n), 2))
    for choices in product((-1, 0, 1), repeat=len(pairs)):
        order = set()
        for pair, direction in zip(pairs, choices):
            if direction:
                order.add(pair if direction == 1 else pair[::-1])
        if all((a, d) in order for a, b in order for c, d in order if b == c):
            yield order


def extension(vertices, order):
    return sorted(vertices, key=lambda v: sum(b == v for a, b in order))


def budgets(orders):
    versions, capacities = {}, {}
    for level, order in enumerate(orders):
        for row in reversed(extension(range(level + 1), order)):
            versions[row, level] = 1 + sum(
                versions[w, j]
                for j in range(1, level + 1) for q, w in orders[j] if q == row
            )
    for k in range(len(orders)):
        upper = orders[k + 1] if k + 1 < len(orders) else set()
        for p in extension(range(k + 1), upper):
            lower = sum(
                capacities[q, r] + versions[q, r] + 1
                for q, w in upper if w == p for r in range(q, k + 1)
            )
            capacities[p, k] = versions.get((p, k + 1), 0) * (1 + lower)
    return versions, capacities


@dataclass
class Block:
    capacity: int
    starts: list = field(default_factory=list)
    spent: int = 0

    @property
    def marker(self):
        return self.starts[-1] + self.capacity + 2


def experiment(orders, mask):
    limits, capacities = budgets(orders)
    blocks = {key: Block(cap) for key, cap in capacities.items()}
    entries = [[] for _ in orders]
    watchers, events = [], []
    sequence = count()
    clock, largest = 0, 0

    def schedule(time, kind, key, version=0):
        heappush(events, (time, next(sequence), kind, key, version))

    def write(row, position):
        assert all(pos != position for pos, time in entries[row])
        entries[row].append((position, clock))
        for owner, earlier, cutoff, activated in watchers:
            if clock > activated and row in earlier and position <= cutoff:
                schedule(clock + 3, 'response', owner)

    def assign(key):
        nonlocal largest
        row, k = key
        block = blocks[key]
        start = max(clock, largest) + 1
        block.starts.append(start)
        largest = block.marker
        if k:
            schedule(largest + 3 + (row % 2), 'signal', key, len(block.starts))

    def datum(key):
        row, k = key
        return (mask + row + 2 * k) % 3 == 0

    for key in sorted(blocks, key=lambda key: key[::-1]):
        assign(key)
        if datum(key):
            schedule(3 + 13 * sum(key), 'data', key)

    while events:
        time, _, kind, key, version = heappop(events)
        block = blocks[key]
        p, level = key
        clock = max(clock + 1, time)
        if kind == 'response':
            assert block.spent < block.capacity
            write(p, block.starts[-1] + 2 + block.spent)
            block.spent += 1
        elif kind == 'data':
            write(p, block.starts[-1] + 1)
        elif version == len(block.starts):
            cutoff = block.marker + 1
            earlier = {q for q, w in orders[level] if w == p}
            for q in sorted(earlier):
                for r in range(level, len(orders)):
                    moved = blocks[q, r]
                    write(q, moved.starts[-1])
                    assign((q, r))
            if p < level:
                owner = (p, level - 1)
                watchers.append((owner, earlier, cutoff, clock))
                schedule(clock + 3, 'response', owner)

    intervals = 0
    for (p, k), block in blocks.items():
        assert len(block.starts) <= limits[p, k]
        oracle = {pos for pos, time in entries[p]}
        # Decode all versions using the old flag and then read the data.
        index = 0
        while block.starts[index] in oracle:
            index += 1
        assert index == len(block.starts) - 1
        assert any(start + 1 in oracle for start in block.starts[:index + 1]) == datum((p, k))
        if k + 1 == len(orders):
            continue
        left, right = block.marker, blocks[p, k + 1].marker
        assert left < right
        for q, w in orders[k + 1]:
            if w != p:
                continue
            # Both moduli are step functions. These are all their breakpoints.
            xs = {left} | {a for a, _ in entries[p]} | {a - 1 for a, _ in entries[q]}
            for x in xs:
                if left <= x < right:
                    mp = max((t for a, t in entries[p] if a <= x), default=0)
                    mq = max((t for a, t in entries[q] if a <= x + 1), default=0)
                    assert mp > mq + 2
            intervals += 1
    return intervals


if __name__ == '__main__':
    examined = intervals = 0
    for poset in finite_orders(4):
        orders = [{(a, b) for a, b in poset if max(a, b) <= level} for level in range(4)]
        intervals += experiment(orders, examined)
        examined += 1
    assert examined == 219
    for shift in range(6):
        orders = []
        for level in range(5):
            ranking = sorted(range(level + 1), key=lambda q: (q + shift + level) % (level + 1))
            orders.append(set(combinations(ranking, 2)))
        intervals += experiment(orders, shift)
    print(f"{examined} labelled four-point orders and six varying schedules; "
          f"verified every breakpoint on {intervals} settling intervals.")
