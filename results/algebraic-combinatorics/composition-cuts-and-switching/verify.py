"""Check the substring multisets and the switching obstruction directly."""
from collections import Counter


def substring_compositions(word):
    return Counter((j - i, word[i:j].count("1"))
                   for i in range(len(word)) for j in range(i + 1, len(word) + 1))


def composition(word):
    cuts = [0] + [i for i, bit in enumerate(word, 1) if bit == "1"] + [len(word) + 1]
    return tuple(right - left for left, right in zip(cuts, cuts[1:]))


def coarsening_polynomial(parts):
    coefficients = Counter()
    for mask in range(1 << (len(parts) - 1)):
        blocks = [parts[0]]
        for i, size in enumerate(parts[1:]):
            if mask & (1 << i):
                blocks.append(size)
            else:
                blocks[-1] += size
        coefficients[tuple(sorted(blocks))] += 1
    return coefficients


words = ("01000101010000100011001", "01010100010000110010001")
assert substring_compositions(words[0]) == substring_compositions(words[1])
witness = (1, 1, 2, 2, 2, 4, 5, 7)
assert [coarsening_polynomial(composition(w))[witness] for w in words] == [0, 1]
print("All substring compositions agree. The coarsening coefficient is 0 versus 1.")
