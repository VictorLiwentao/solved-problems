"""Exhaustive finite checks of the four-clause example and guarded lifting criterion."""

from itertools import product


def checks_example():
    domain = {0, 1}
    subsets = [set(), {0}, {1}, domain]
    original = [(p, h) for p, h in product(subsets, repeat=2)
                if domain <= p and p <= h and not h & p]
    expanded = [(p0, p1, h) for p0, p1, h in product(subsets, repeat=3)
                if 0 in p0 and 1 in p1 and p1 <= h and not h & p0]
    assert not original and ({0}, {1}, {1}) in expanded
    assert all((p0 & p1, h) not in original for p0, p1, h in expanded)
    print(f"Two-point universe: {len(original)} original and {len(expanded)} expanded models.")


def model(rules, enabled, state):
    return all(not (enabled >> label & 1 and state & body == body)
               or bool(state & head) for label, body, head in rules)


def entails(rules, enabled, facts, head):
    state = facts
    while True:
        old = state
        for label, body, result in rules:
            if enabled >> label & 1 and state & body == body:
                if result == 0:
                    return True
                state |= result
        if state == old:
            return bool(state & head)


def check_guarded_lifts():
    # Two copies of P occupy bits 0,1. Two copies of H occupy bits 2,3.
    ps, hs = (1, 2), (4, 8)
    universe = ([(0, 0, p) for p in ps] + [(1, p, h) for p in ps for h in hs]
                + [(2, p | h, 0) for p in ps for h in hs])
    originals = [(0, 0, 1), (1, 1, 2), (2, 3, 0)]
    all_copies = [(0, 0, p) for p in ps] + [(1, 3, h) for h in hs] + [(2, 15, 0)]
    for selection in range(1 << len(universe)):
        rules = [rule for i, rule in enumerate(universe) if selection >> i & 1]
        coverage = {(label, head) for label, _, head in rules}
        covers_heads = all((label, head) in coverage for label, _, head in all_copies)
        uniform = True
        for enabled in range(8):
            sound = True
            for state in range(16):
                if model(rules, enabled, state):
                    collapsed = int(state & 3 == 3) + 2 * int(state & 12 == 12)
                    if not model(originals, enabled, collapsed):
                        sound = False
                        break
            closure_test = all(entails(rules, enabled, body, head)
                               for label, body, head in all_copies if enabled >> label & 1)
            assert sound == closure_test
            uniform &= sound
        assert uniform == covers_heads
    print("1,024 lift selections and 8,192 guarded systems passed the equivalence checks.")


if __name__ == "__main__":
    checks_example()
    check_guarded_lifts()
