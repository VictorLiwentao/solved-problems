"""Check the exact construction and output-only simulator on finite instances."""

from collections import Counter
from itertools import product


def slices(table, sizes, owner):
    """Evaluate zero-anchored unary summands and check their proposed XOR."""
    inputs = list(product(*(range(q) for q in sizes)))
    terms = []
    for s in range(sizes[owner]):
        origin = [0] * len(sizes)
        origin[owner] = s
        constant = table[tuple(origin)]
        unary = []
        for i, q in enumerate(sizes):
            row = []
            for value in range(q):
                x = origin.copy()
                x[i] = value
                row.append(0 if i == owner else table[tuple(x)] ^ constant)
            unary.append(row)
        terms.append((constant, unary))
    for x in inputs:
        total, unary = terms[x[owner]]
        for i, value in enumerate(x):
            total ^= unary[i][value]
        if total != table[x]:
            return None
    return terms


def local_gates(terms, x, owner, shift):
    """Return (reset, unmasked value) pairs in public order."""
    q = len(terms)
    gates = []
    for j in range(q):
        a = (shift + j) % q
        b = (a + 1) % q
        has_next = j + 1 < q
        gates.append((a == x[owner], 0))
        left, right = terms[a], terms[b]
        gates.append((False, left[0] ^ (right[0] if has_next else 0)))
        for i, value in enumerate(x):
            if i != owner:
                next_bit = right[1][i][value] if has_next else 0
                gates.append((False, left[1][i][value] ^ next_bit))
    return gates


def real_view(gates, inner_masks):
    state = before = fields = 0
    for j, (reset, value) in enumerate(gates):
        after = (inner_masks >> j) & 1  # last mask vanishes by the loop bound
        sent = value ^ after ^ (0 if reset else before)
        state = sent if reset else state ^ sent
        fields |= (2 * reset + sent) << (2 * j)
        before = after
    return fields, state


def simulator(q, block, output):
    length = q * block
    counts = Counter()
    for selected in range(q):
        for interior in range(1 << (length - 1)):
            previous = fields = 0
            for j in range(length):
                current = output if j == length - 1 else (interior >> j) & 1
                reset = j == selected * block
                value = current if reset else previous ^ current
                fields |= (2 * reset + value) << (2 * j)
                previous = current
            counts[fields] += 1
    return counts


def check_protocol(table, sizes, owner, terms, simulated):
    q = sizes[owner]
    for x, output in table.items():
        counts = Counter()
        for shift in range(q):
            gates = local_gates(terms, x, owner, shift)
            for masks in range(1 << (len(gates) - 1)):
                fields, decoded = real_view(gates, masks)
                assert decoded == output
                counts[fields] += 1
        assert counts == simulated[output]


def main():
    sizes = (2, 2, 2)
    inputs = list(product(range(2), repeat=3))
    simulated = [simulator(2, 4, z) for z in (0, 1)]
    admitted = symmetric = 0
    for mask in range(256):
        table = {x: (mask >> j) & 1 for j, x in enumerate(inputs)}
        for owner in range(3):
            terms = slices(table, sizes, owner)
            if terms is not None:
                check_protocol(table, sizes, owner, terms, simulated)
                admitted += 1
                if all(table[x] == table[y] for x in inputs for y in inputs if sum(x) == sum(y)):
                    symmetric += 1
                break
    assert (admitted, symmetric) == (112, 4)
    sizes = (3, 2, 2)
    table = {(s, y, z): (y, z, 1 ^ y ^ z)[s]
             for s, y, z in product(range(3), range(2), range(2))}
    simulated = [simulator(3, 4, z) for z in (0, 1)]
    terms = slices(table, sizes, 0)
    assert terms is not None
    check_protocol(table, sizes, 0, terms, simulated)
    print("Exact transcript counts match for all 112 admitted three-bit functions")
    print("Four symmetric functions admitted; ternary-selector example also checked")


if __name__ == "__main__":
    main()
