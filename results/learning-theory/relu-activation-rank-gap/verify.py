"""Check every itinerary and the corresponding diagonal minor at depth six."""
from fractions import Fraction
from itertools import product

def verify_minor(depth, sample_count):
    batch = {}
    for word in list(product(range(2), repeat=depth))[:sample_count]:
        x = Fraction(1,2)
        for bit in reversed(word):
            x = x/2 if bit == 0 else 1-x/2
        t = x
        observed = []
        for _ in word:
            activations = (1-2*t, 2*t-1)
            assert activations[0]*activations[1] < 0
            observed.append(int(activations[1]>0))
            t = 1-sum(max(0,a) for a in activations)
        assert tuple(observed) == word and t == Fraction(1,2)
        batch[word] = x, tuple(observed)
    for word, (x, observed) in batch.items():
        for path in batch:
            entry = x if all(a == b for a,b in zip(observed,path)) else 0
            assert (entry > 0) == (word == path)
    assert len(set(x for x,_ in batch.values())) == sample_count

verify_minor(6,64)
verify_minor(5,22)
assert 21 < 22 < 31
print("Verified the 64-by-64 path minor at depth six and a 22-by-22 minor at depth five.")
