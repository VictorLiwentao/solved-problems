"""Compare the structural tape-inclusion test with exact binary DFA inclusion."""

from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from random import Random


@dataclass(frozen=True)
class Formula:
    walls: tuple[str, ...]
    blocks: tuple[str, ...]

    def aligned_and_separated(self):
        return (len(self.walls) == len(self.blocks) + 1
                and all(self.walls[1:-1]) and all(self.blocks)
                and all(not wall.startswith(block[0])
                        for block, wall in zip(self.blocks, self.walls[1:])))


def exponent_map(source, target):
    """Return (offset, stride) for each block, or None for non-inclusion."""
    if (len(source.blocks) != len(target.blocks)
            or not source.aligned_and_separated() or not target.aligned_and_separated()):
        raise ValueError("expected two aligned, separated formulas of the same rank")
    if source.walls[-1] != target.walls[-1]:
        return None
    result = []
    for j, block in enumerate(target.blocks):
        fixed = target.walls[j]
        if not source.walls[j].startswith(fixed):
            return None
        extra = source.walls[j][len(fixed):]
        stride_word = source.blocks[j]
        offset = len(extra) // len(block)
        stride = len(stride_word) // len(block)
        if extra != block * offset or stride_word != block * stride:
            return None
        result.append((offset, stride))
    return tuple(result)


class WordDFA:
    """Construct a binary DFA by determinizing the concatenation of literals and stars."""

    def __init__(self, formula):
        edges = defaultdict(set)
        next_state = 1
        state = 0
        for i, wall in enumerate(formula.walls):
            for letter in wall:
                edges[state, letter].add(next_state)
                state = next_state
                next_state += 1
            if i < len(formula.blocks):
                start = state
                for letter in formula.blocks[i]:
                    edges[state, letter].add(next_state)
                    state = next_state
                    next_state += 1
                edges[state, ""].add(start)
                edges[start, ""].add(next_state)
                state = next_state
                next_state += 1
        final = state

        def closure(seed):
            reached = set(seed)
            pending = list(reached)
            while pending:
                new = edges[pending.pop(), ""] - reached
                reached.update(new)
                pending.extend(new)
            return frozenset(reached)

        start_set = closure([0])
        number = {start_set: 0}
        pending = [start_set]
        self.moves = []
        self.accepting = set()
        for subset in pending:
            if final in subset:
                self.accepting.add(number[subset])
            moves = []
            for letter in "01":
                dest = closure(v for q in subset for v in edges[q, letter])
                if dest not in number:
                    number[dest] = len(pending)
                    pending.append(dest)
                moves.append(number[dest])
            self.moves.append(tuple(moves))


def included(source, target):
    """Search the full product for a source-accepting, target-rejecting state."""
    pending = [(0, 0)]
    seen = set(pending)
    while pending:
        a, b = pending.pop()
        if a in source.accepting and b not in target.accepting:
            return False
        for pair in zip(source.moves[a], target.moves[b]):
            if pair not in seen:
                pending.append(pair)
                seen.add(pair)
    return True


def main():
    wall_choices = ("", "0", "1")
    blocks = ("0", "1", "00", "01", "10", "11")
    comparisons = 0
    for k in range(3):
        formulas = []
        for walls in product(wall_choices, repeat=k + 1):
            for repeats in product(blocks, repeat=k):
                f = Formula(walls, repeats)
                if f.aligned_and_separated():
                    formulas.append((f, WordDFA(f)))
        for (g, dg), (f, df) in product(formulas, repeat=2):
            assert (exponent_map(g, f) is not None) == included(dg, df), (g, f)
            comparisons += 1
    print(f"{comparisons} exhaustive formula comparisons agree with exact DFA inclusion.")

    rng = Random(186)
    for _ in range(120):
        k = rng.randint(3, 8)
        repeats = tuple(rng.choice(blocks) for _ in range(k))
        walls = [rng.choice(wall_choices)]
        for block in repeats:
            walls.append(("1" if block[0] == "0" else "0") + rng.choice(wall_choices))
        f = Formula(tuple(walls), repeats)
        params = tuple((rng.randrange(3), rng.randint(1, 3)) for _ in repeats)
        g = Formula(tuple(w + r * a for w, r, (a, _) in zip(walls, repeats, params))
                    + (walls[-1],),
                    tuple(r * b for r, (_, b) in zip(repeats, params)))
        assert exponent_map(g, f) == params and included(WordDFA(g), WordDFA(f))
        changed = Formula(g.walls[:-1] + (g.walls[-1] + "0",), g.blocks)
        assert exponent_map(changed, f) is None and not included(WordDFA(changed), WordDFA(f))
    print("120 longer substitutions and 120 altered final walls agree with exact DFA inclusion.")

    f = Formula(("", "", ""), ("001", "011"))
    g = Formula(("0", "11", ""), ("010", "011"))
    assert included(WordDFA(g), WordDFA(f)) and not included(WordDFA(f), WordDFA(g))
    for r, s in (f.blocks, g.blocks):
        assert r + s != s + r
    print("DFA inclusion is strict in the noncommuting empty-wall counterexample.")


if __name__ == "__main__":
    main()
