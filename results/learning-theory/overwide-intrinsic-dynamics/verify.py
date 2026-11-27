"""Exact checks of the pseudo-orthogonal Gram orbit dimension."""
from fractions import Fraction as F

def multiply(a, b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]

def transpose(a):
    return list(zip(*a))

def diagonal(entries):
    return [[F(x if i == j else 0) for j in range(len(entries))] for i,x in enumerate(entries)]

def rank(rows):
    rows = [list(map(F,row)) for row in rows]
    pivots = 0
    for j in range(len(rows[0])):
        k = next((k for k in range(pivots,len(rows)) if rows[k][j]),None)
        if k is None:
            continue
        rows[pivots],rows[k] = rows[k],rows[pivots]
        v = [x/rows[pivots][j] for x in rows[pivots]]
        for k in range(pivots+1,len(rows)):
            if rows[k][j]:
                rows[k] = [x-rows[k][j]*y for x,y in zip(rows[k],v)]
        pivots += 1
    return pivots

def orbit_dim(n, h):
    d = len(h)
    generators = []
    for i in range(d):
        for j in range(i):
            xi = diagonal([0]*d)
            xi[i][j] = 1
            xi[j][i] = -1 if (i<n) == (j<n) else 1
            z = multiply(xi,h)
            generators.append([z[i][j]+z[j][i] for i in range(d) for j in range(i+1)])
    return rank(generators)

for n,m in ((1,1),(1,3),(2,2),(3,2)):
    d = n+m
    for p,q in ((2,5),(4,4)):
        h = diagonal([p]*n+[q]*m)
        assert orbit_dim(n,h) == n*m
        g = diagonal([1]*d)
        g[0][0] = g[n][n] = F(5,3)
        g[0][n] = g[n][0] = F(4,3)
        boosted = multiply(multiply(g,h),transpose(g))
        assert orbit_dim(n,boosted) == n*m
    assert orbit_dim(n,diagonal(range(1,d+1))) == d*(d-1)//2
# Gram with a shared hidden direction, rank three, both diagonal blocks positive.
T = [[1,0,0],[0,1,0],[0,0,1],[0,1,0]]
assert orbit_dim(2,multiply(T,transpose(T))) > 4
print('Exact orbit dimensions verified for isotropic, distinct and rank-deficient Grams.')
