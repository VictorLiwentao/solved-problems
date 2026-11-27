"""Check the two compression formats on blocks with eight or twelve points."""
from collections import Counter
from itertools import combinations


def encode(sample, hole_size, row_count):
    size = hole_size * row_count
    rows = {x // hole_size for x in sample}
    if len(rows) < row_count:
        return [next(x for x in sorted(sample) if (x // hole_size + 1) % row_count not in rows)]
    message = []
    for x in sorted(sample):
        distance = 1
        while (x + distance) % size not in sample and len(message) < hole_size:
            message.append(x)
            distance += 1
    return message


def decode(message, hole_size, row_count):
    size = hole_size * row_count
    if len(message) == 1:
        row = (message[0] // hole_size + 1) % row_count
        holes = set(range(row * hole_size, (row + 1) * hole_size))
    else:
        holes = {(x + j) % size for x, count in Counter(message).items()
                 for j in range(1, count + 1)}
    return set(range(size)) - holes


def main():
    checked = 0
    for hole_size, row_count in [(2, 4), (3, 4)]:
        size = hole_size * row_count
        for length in range(1, size - hole_size + 1):
            for entries in combinations(range(size), length):
                sample = set(entries)
                message = encode(sample, hole_size, row_count)
                reconstructed = decode(message, hole_size, row_count)
                assert set(message) <= sample <= reconstructed
                assert len(reconstructed) == size - hole_size
                assert len(message) == 1 or row_count <= length
                checked += 1
    print(f"Checked compression and reconstruction on {checked} nonempty samples.")


if __name__ == "__main__":
    main()
