"""Exhaustively compare the two graph criteria with truth tables on up to three wires."""
from itertools import permutations, product


def input_masks(n):
    return [sum(1 << x for x in range(1 << n) if x & (1 << i)) for i in range(n)]


def gate_data(table, n, wire):
    """Return fixed assignments, essential arcs, and signed arcs (None if nonunate)."""
    edges = signs = 0
    unate = True
    for source in range(n):
        up = down = False
        for x in range(1 << n):
            if x & (1 << source):
                continue
            low = (table >> x) & 1
            high = (table >> (x | (1 << source))) & 1
            up |= low < high
            down |= high < low
        place = wire * n + source
        if up or down:
            edges |= 1 << place
            signs += (1 if up else 2) * 3**place
        unate &= not (up and down)
    universe = (1 << (1 << n)) - 1
    fixed = universe ^ (table ^ input_masks(n)[wire])
    return fixed, edges, signs if unate else None


def stalls(tables, masks, universe):
    cube = universe
    while True:
        before = cube
        for table, ones in zip(tables, masks):
            possible_ones = cube & table
            if possible_ones == cube:
                cube &= ones
            elif not possible_ones:
                cube &= universe ^ ones
        if cube == before:
            return cube.bit_count() > 1


def upward_closure(witnesses, base, edge_count):
    """Any larger permitted topology also admits the same witness."""
    for i in range(edge_count):
        digit = base**i
        for graph in range(len(witnesses)):
            if witnesses[graph] and (graph // digit) % base == 0:
                for sign in range(1, base):
                    witnesses[graph + sign * digit] = 1


def observed(n):
    masks = input_masks(n)
    universe = (1 << (1 << n)) - 1
    tables = range(universe + 1)
    gates = [[gate_data(t, n, i) for t in tables] for i in range(n)]
    unsigned = bytearray(2 ** (n * n))
    signed = bytearray(3 ** (n * n))

    def enumerate_gates(prefix, fixed, graph, signs):
        if len(prefix) == n:
            if fixed.bit_count() != 1:
                return
            if unsigned[graph] and (signs is None or signed[signs]):
                return
            if stalls(prefix, masks, universe):
                unsigned[graph] = 1
                if signs is not None:
                    signed[signs] = 1
            return
        for t, (stable, arcs, polarities) in enumerate(gates[len(prefix)]):
            if fixed & stable:
                new_signs = None if signs is None or polarities is None else signs + polarities
                enumerate_gates(prefix + (t,), fixed & stable, graph | arcs, new_signs)

    enumerate_gates((), universe, 0, 0)
    upward_closure(unsigned, 2, n * n)
    upward_closure(signed, 3, n * n)
    return unsigned, signed


def predicted(graph, n, signed):
    base = 3 if signed else 2
    adjacency = [[(graph // base**(v * n + u)) % base for v in range(n)] for u in range(n)]
    reach = [[u == v or bool(adjacency[u][v]) for v in range(n)] for u in range(n)]
    for k, u, v in product(range(n), repeat=3):
        reach[u][v] |= reach[u][k] and reach[k][v]

    cycles = []
    for size in range(1, n + 1):
        for cycle in permutations(range(n), size):
            if cycle[0] != min(cycle):
                continue
            arcs = [adjacency[u][v] for u, v in zip(cycle, cycle[1:] + cycle[:1])]
            if all(arcs):
                cycles.append((cycle, arcs.count(2) % 2))

    # Two distinct cycles meeting or linked is equivalent to the unsigned SCC obstruction.
    for i, (first, first_sign) in enumerate(cycles):
        for j, (second, second_sign) in enumerate(cycles):
            if i != j and (not signed or (first_sign == 0 and second_sign == 1)):
                if reach[first[0]][second[0]]:
                    return True
    return False


def main():
    for n in (1, 2, 3):
        for flag, actual in zip((False, True), observed(n)):
            for graph, witness in enumerate(actual):
                assert predicted(graph, n, flag) == bool(witness), (n, flag, graph)
            kind = "signed" if flag else "unsigned"
            print(f"{n} wire(s), {kind}: {sum(actual)} of {len(actual)} graphs admit a witness.")
    for x in (0, 1):
        solutions = [(a, b, c) for a, b, c in product(range(2), repeat=3)
                     if a == b ^ x and b == c ^ x and c == a ^ b]
        assert solutions == [(x, 0, x)]
    print("Both criteria passed, as did the three-XOR example on both inputs.")


if __name__ == "__main__":
    main()
