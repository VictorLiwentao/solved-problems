"""Joint run/return counts for rational Dyck paths by a binomial formula."""
from math import comb


def flagged_count(bounds):
    """Hessenberg determinant for weakly increasing positive integers u_i <= b_i."""
    tail = [0]*len(bounds) + [1]
    for i in reversed(range(len(bounds))):
        tail[i] = sum((-1)**(length-1) * comb(bounds[i], length) * tail[i+length]
                      for length in range(1, min(bounds[i], len(bounds)-i)+1))
    return tail[0]


def segment(m, n, start, end, required, forbidden):
    left, bottom = start
    right, top = end
    mandatory = sum(x in required for x in range(left, right))
    extra = top-bottom-mandatory
    if extra < 0:
        return 0
    fixed = allowed = 0
    bounds = []
    for x in range(left, right):
        fixed += x in required
        allowed += x != forbidden
        needed = ((x+1)*n+m-1)//m - bottom - fixed
        if needed > extra:
            return 0
        if needed > len(bounds):
            bounds.extend([allowed]*(needed-len(bounds)))
    bounds.extend([allowed]*(extra-len(bounds)))
    return flagged_count(bounds)


def distribution(m, n, run, stride=1):
    """Entry l gives the count with the requested run value and l returns."""
    if not 1 <= n <= m or not 1 <= stride <= m//n or not 1 <= run <= n:
        raise ValueError("expected m >= n >= run >= 1 and 1 <= stride <= floor(m/n)")
    required = set(range(0, stride*run, stride))
    forbidden = stride*run
    points = [(i*m//n, i) for i in range(n)] + [(m, n)]
    kernel = [[0]*(n+1) for _ in points]
    for i, first in enumerate(points):
        for j in range(i+1, n+1):
            kernel[i][j] = segment(m, n, first, points[j], required, forbidden)
    # Multiply a row vector by successive powers of the strictly upper triangular kernel.
    row = [1]+[0]*n
    answer = [0]*(n+1)
    for s in range(n):
        row = [sum(row[i]*kernel[i][j] for i in range(j)) for j in range(n+1)]
        for l in range(1, s+2):
            answer[l] += (-1)**(s-l+1) * comb(s, l-1) * row[n]
    return answer
