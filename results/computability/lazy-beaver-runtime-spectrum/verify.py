"""Finite checks for the accessibility and unused-instruction arguments."""

from itertools import product
from math import comb

HALT = -1


def reachable_states(table):
    reached = {0}
    queue = [0]
    for state in queue:
        for target in table[2 * state : 2 * state + 2]:
            if target != HALT and target not in reached:
                reached.add(target)
                queue.append(target)
    return reached


def decode_breadth_first(word):
    n = len(word) // 2
    table = [HALT] * len(word)
    queue = [0]
    listed = {0}
    for i in range(n):
        if i == len(queue):
            restart = min(set(range(n)) - listed)
            queue.append(restart)
            listed.add(restart)
        state = queue[i]
        for bit in range(2):
            target = word[2 * i + bit]
            table[2 * state + bit] = target
            if target != HALT and target not in listed:
                queue.append(target)
                listed.add(target)
    return tuple(table)


def check_accessibility():
    connected_counts = {}
    rotation_checks = 0
    for n in range(1, 4):
        decoded = set()
        accessible_weight = 0
        covered_weight = 0
        for word in product(range(HALT, n), repeat=2 * n):
            table = decode_breadth_first(word)
            decoded.add(table)
            if not set(range(1, n)).issubset(word):
                continue
            weight = 4 ** (2 * n - word.count(HALT))
            covered_weight += weight
            if len(reachable_states(table)) == n:
                accessible_weight += weight
            rotations = (word[i:] + word[:i] for i in range(0, 2 * n, 2))
            assert any(len(reachable_states(decode_breadth_first(r))) == n for r in rotations)
            rotation_checks += 1

        # Count all labeled tables independently by the size of the rooted component.
        total = (4 * n + 1) ** (2 * n)
        smaller = sum(
            comb(n - 1, k - 1) * count * (4 * n + 1) ** (2 * (n - k))
            for k, count in connected_counts.items()
        )
        assert len(decoded) == (n + 1) ** (2 * n)
        assert accessible_weight == total - smaller
        assert n * accessible_weight >= covered_weight
        connected_counts[n] = accessible_weight
    print(f"Checked the rotation argument on {rotation_checks} covered destination words.")
    print(f"Accessible labeled table counts at one to three states: {list(connected_counts.values())}")


def forced_paths(table):
    incoming = [[] for _ in range(len(table) // 2)]
    for slot, target in enumerate(table):
        if target != HALT:
            incoming[target].append(slot)
    paths = []
    for w in range(1, len(incoming)):
        if len(incoming[w]) != 1 or HALT in table[2 * w : 2 * w + 2]:
            continue
        second = incoming[w][0]
        v = second // 2
        if v == 0 or len(incoming[v]) != 1:
            continue
        first = incoming[v][0]
        if len({first // 2, v, w}) == 3:
            paths.append((first, second, w))
    return paths


def trace(table, moves, writes, tape, limit):
    head = state = 0
    ones = set(tape)
    steps = []
    for _ in range(limit):
        slot = 2 * state + (head in ones)
        target = table[slot]
        steps.append((state, head, slot, target))
        if target == HALT:
            break
        if writes[slot]:
            ones.add(head)
        else:
            ones.discard(head)
        head += moves[slot]
        state = target
    return steps, ones


def check_unreadable_slots():
    # All reachable three-state successor graphs, both reversing orientations and
    # both first-arrow writes. Other entries use deterministic sample decorations.
    inputs = [
        {i - 1 for i in range(3) if mask & (1 << i)}
        for mask in range(8)
    ]
    comparisons = witnessed = 0
    for table in product(range(HALT, 3), repeat=6):
        if len(reachable_states(table)) != 3:
            continue
        for first, second, w in forced_paths(table):
            for direction, bit in product((-1, 1), (0, 1)):
                moves = [1 if i % 2 else -1 for i in range(6)]
                writes = [i % 2 for i in range(6)]
                moves[first], moves[second] = direction, -direction
                writes[first] = bit
                unreadable = 2 * w + (1 - bit)
                alternate = writes.copy()
                alternate[unreadable] ^= 1
                for tape in inputs:
                    steps, ones = trace(table, moves, writes, tape, 14)
                    assert trace(table, moves, alternate, tape, 14) == (steps, ones)
                    assert all(slot != unreadable for _, _, slot, _ in steps)
                    witnessed += any(state == w for state, _, _, _ in steps)
                    comparisons += 1
    assert witnessed > 0
    print(f"Compared {comparisons} paired traces through 14 steps or halting.")
    print(f"In {witnessed} cases the machine actually visited the forced-read state.")


def check_simultaneous_changes():
    # Two disjoint forced paths, 0->1->2 and 3->4->5, on the same blank-tape run.
    table = (1, HALT, 2, HALT, 3, 3, 4, HALT, 5, HALT, 0, 0)
    moves = (1, 1, -1, 1, 1, 1, 1, 1, -1, 1, -1, 1)
    writes = [1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]
    paths = [p for p in forced_paths(table) if moves[p[0]] != moves[p[1]]]
    assert len(paths) == 2
    forbidden = [2 * w + (1 - writes[first]) for first, _, w in paths]
    blank_steps, _ = trace(table, moves, writes, set(), 14)
    assert [state for state, _, _, _ in blank_steps] == [0, 1, 2, 3, 4, 5, 0]
    assert blank_steps[-1][-1] == HALT
    for mask in range(32):
        tape = {i - 2 for i in range(5) if mask & (1 << i)}
        expected = trace(table, moves, writes, tape, 14)
        for bits in product((0, 1), repeat=len(forbidden)):
            changed = writes.copy()
            for slot, bit in zip(forbidden, bits):
                changed[slot] = bit
            assert trace(table, moves, changed, tape, 14) == expected
    print("Checked four simultaneous completions on each of 32 initial tapes.")


if __name__ == "__main__":
    check_accessibility()
    check_unreadable_slots()
    check_simultaneous_changes()
