"""Exhaust all block-level generator moves on a finite quota board."""
from functools import cache
from itertools import product


def verify(lengths, quotas):
    @cache
    def play(free, remaining):
        # State just after an adversary claim. Repeats and out-of-board
        # generator outputs have the same effect as a pass.
        assert all(u >= 2 * r for u, r in zip(free, remaining) if r)
        if not any(remaining):
            return
        for hit in [None, *(i for i, u in enumerate(free) if u)]:
            after = list(free)
            if hit is not None:
                after[hit] -= 1
            endangered = [i for i, r in enumerate(remaining) if r and after[i] < 2 * r]
            assert len(endangered) <= 1
            pick = endangered[0] if endangered else next(i for i, r in enumerate(remaining) if r)
            assert after[pick] > 0
            after[pick] -= 1
            need = list(remaining)
            need[pick] -= 1
            play(tuple(after), tuple(need))

    # Allow a generator move even before the first adversary move.
    play(tuple(lengths), tuple(quotas))
    return play.cache_info().currsize


if __name__ == '__main__':
    board = (4, 5, 6, 7)
    states = sum(verify(board, quota) for quota in product(*(range((size - 1) // 2 + 1) for size in board)))
    print(f'Checked quota preservation through {states} finite game states.')
