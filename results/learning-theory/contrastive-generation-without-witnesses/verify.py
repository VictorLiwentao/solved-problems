"""Check the four-cut membership and crossing claims on finite representatives."""
from itertools import product


def check(m, count):
    # Distinct representatives of each infinite block suffice for the cell tests.
    labels = ['S', 'T', 'D', *(f'X{j}' for j in range(1, count + 1)),
              *(f'Y{j}' for j in range(1, count + 1))]
    core = [(name, i) for i, name in product(range(1, m + 2), labels)]
    prefix = set(core[:m])
    points = set(core) | {'A1', 'A2', 'B1', 'B2'}
    outside = {(sign, j) for sign, j in product('+-', range(1, count + 1))}
    points |= outside

    def supports(j):
        shared = {'A1', 'B1'} | set(core[:j])
        s = shared | {x for x in core if x[0] in {'S', f'X{j}'} or x[0].startswith('Y') and x[0] != f'Y{j}'}
        t = shared | {x for x in core if x[0] in {'T', f'Y{j}'} or x[0].startswith('X') and x[0] != f'X{j}'}
        return s | {('+', k) for k in range(1, count + 1) if k != j}, t | {('-', k) for k in range(1, count + 1) if k != j}

    a = set(core) | {'A1', 'A2'}
    b = set(core) | {'B1', 'B2'}
    s, t = supports(m)
    assert a & b & s & t == prefix
    masks = {x: tuple(x in h for h in (a, b, s, t)) for x in points}
    occupied = set(masks.values())
    covered = {x for x, mask in masks.items() if tuple(not v for v in mask) in occupied}
    assert s | t | prefix | {'A1', 'A2', 'B1', 'B2'} <= covered
    assert all(x not in covered for x in core if x[0] == 'D' and x not in prefix)
    for j in range(1, count + 1):
        sj, tj = supports(j)
        if j != m:
            assert ('+', m) in sj and ('-', m) in tj
            assert {x for x in core if x[0] == f'X{m}'} <= s & tj
            assert {x for x in core if x[0] == f'Y{m}'} <= t & sj


if __name__ == '__main__':
    for size in range(2, 9):
        for index in range(1, size + 1):
            check(index, size)
    print('Checked common cells, witness partners, and the two safe output branches.')
