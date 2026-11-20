"""Exhaust the two-block, two-position symmetric Cantor class and its partial samples."""
from itertools import permutations, product

MASKS = range(4)
PERMUTATIONS = list(permutations(MASKS))


def classifier(masks, labels):
    return tuple(labels[mask if mask & (1 << position) else 0]
                 for mask in masks for position in range(2))


def consistent(hypothesis, history):
    return all(label is None or label == guess for label, guess in zip(history, hypothesis))


def decode(observations, labels):
    masks = [0, 0]
    for point, observed in observations:
        block = point // 2
        mask = labels.index(observed)
        if mask:
            masks[block] = mask
    return classifier(masks, labels)


def main():
    hypotheses = {classifier(masks, labels) for masks in product(MASKS, repeat=2)
                  for labels in PERMUTATIONS}
    for h in hypotheses:
        for labels in PERMUTATIONS:
            assert tuple(labels[x] for x in h) in hypotheses
    count = 0
    for history in product([None, *MASKS], repeat=4):
        if not any(consistent(h, history) for h in hypotheses):
            continue
        count += 1
        observations = [(point, label) for point, label in enumerate(history) if label is not None]
        for labels in PERMUTATIONS:
            h = decode(observations, labels)
            if consistent(h, history):
                representatives = {}
                for point, label in observations:
                    if label != labels[0]:
                        representatives[point // 2] = (point, label)
                assert decode(representatives.values(), labels) == h
                break
        else:
            raise AssertionError('No consistent candidate decoded')
        if all(label in (0, None) for label in history):
            unseen = [sum(1 << j for j in range(2) if history[2*b+j] is None) for b in range(2)]
            bad = classifier(unseen, tuple(MASKS))
            assert consistent(bad, history)
            assert all((bad[i] != 0) == (history[i] is None) for i in range(4))
    print(f'{len(hypotheses)} classifiers and {count} realizable partial samples verified.')


if __name__ == '__main__':
    main()
