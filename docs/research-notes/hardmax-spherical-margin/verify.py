"""Rational arithmetic for unequal midpoint lengths and the symmetric octahedron."""
from fractions import Fraction as F
from itertools import combinations, product

def circle(t):
    return ((1-t*t)/(1+t*t),2*t/(1+t*t))

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))

U = [(1,0),(0,1),(-1,0),(0,-1)]
cases = 0
for tilts in product((F(-1,9),F(0),F(1,8)), repeat=4):
    W, H, radii = [], [], []
    for (x,y), tilt in zip(U,tilts):
        r,s = circle(tilt)
        W.append((r*x-s*y,r*y+s*x))
        H.append((r*x+s*y,r*y-s*x))
        radii.append(r)
    margin = min(dot(H[i],sub(W[i],W[j])) for i in range(4) for j in range(4) if i!=j)
    assert margin>0
    for i,j in combinations(range(4),2):
        assert radii[i]*radii[j]*(1-dot(U[i],U[j])) >= margin
        if radii[i]<1 or radii[j]<1:
            assert 1-dot(U[i],U[j]) > margin
    cases += 1
octahedron = [tuple(sign*int(i==k) for i in range(3)) for k in range(3) for sign in (-1,1)]
assert min(1-dot(x,y) for x,y in combinations(octahedron,2)) == 1
print(f"Checked {cases} rational hardmax configurations and the aligned octahedron.")
