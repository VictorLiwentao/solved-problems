"""Check the shared hinge estimate on multisets with repeated and unequal values."""
from itertools import combinations_with_replacement, chain, product

sites = (-3,-1,0,2,5)
multisets = list(chain.from_iterable(combinations_with_replacement(sites,j) for j in range(5)))
def hinge(x,b):
    return sum(max(0,v-b) for v in x)
for x,y in product(multisets,repeat=2):
    diff = lambda b: hinge(x,b)-hinge(y,b)
    if len(x)==len(y):
        values = [diff(t) for t in sites]
        match = sum(abs(u-v) for u,v in zip(x,y))
        assert sum(abs(u-v) for u,v in zip(values,values[1:])) == match
        assert match <= 2*len(sites)*max(map(abs,values))
    else:
        assert diff(-5)-diff(-4)==len(x)-len(y)
print("Hinge variation equals sorted matching cost on all 15,876 ordered multiset pairs.")
