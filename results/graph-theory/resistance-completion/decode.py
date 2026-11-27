"""Exact rational decoder for partial effective-resistance observations.

Vertices are numbered 0,...,n-1. Omitted known pairs have conductance zero.
The order of 'missing' is the coordinate order of both readings and output.
Inputs may be integers or exact rationals. Requires SymPy.
"""
from math import isqrt

from sympy import Matrix, Rational, eye, zeros


def resistances(n, known, missing, weights):
    """Return the readings on missing, or None if the graph is disconnected."""
    # Ground the last vertex. Incidence vectors of edges to ground have one entry.
    grounded = zeros(n - 1)
    directions = []
    edges = list(known.items()) + list(zip(missing, weights))
    for index, ((u, v), value) in enumerate(edges):
        vector = zeros(n - 1, 1)
        if u < n - 1:
            vector[u] = 1
        if v < n - 1:
            vector[v] = -1
        grounded += value * vector * vector.T
        if index >= len(known):
            directions.append(vector)
    if grounded.det() == 0:
        return None
    inverse = grounded.inv()
    return [(v.T * inverse * v)[0] for v in directions]


def first_component(n, known, missing, x):
    neighbors = [set() for _ in range(n)]
    for (u, v), weight in list(known.items()) + list(zip(missing, x)):
        if weight > 0:
            neighbors[u].add(v)
            neighbors[v].add(u)
    seen, stack = {0}, [0]
    while stack:
        new = neighbors[stack.pop()] - seen
        seen.update(new)
        stack.extend(new)
    return seen


def optimal_certificate(n, known, missing, levels, readings, lam, proposal):
    actual = resistances(n, known, missing, proposal)
    if actual is None:
        return False
    for value, observed, computed in zip(proposal, readings, actual):
        index = levels.index(value)
        residual = observed - computed
        if index > 0 and residual > lam * (value - levels[index - 1]):
            return False
        if index + 1 < len(levels) and residual < -lam * (levels[index + 1] - value):
            return False
    return True


def rounded_central_cut(center, shape, normal, radius_floor):
    """Enclose the retained half-ellipsoid with rational center and shape."""
    k = len(center)
    displacement = shape * normal
    squared_length = (normal.T * displacement)[0]
    numerator, denominator = map(int, squared_length.as_numer_denom())
    scale = 128 * k * k
    root_upper = Rational(isqrt(scale * scale * numerator * denominator) + 1,
                          scale * denominator)
    delta = Rational(1, 64 * k * k)
    next_floor = radius_floor / 2
    center_grid = delta * next_floor / (2 * k)
    next_center = center - displacement / ((k + 1) * root_upper)
    next_center = next_center.applyfunc(lambda v: (v // center_grid) * center_grid)
    ideal = Rational(k*k, k*k - 1) * (
        shape - Rational(2, k + 1) * displacement * displacement.T / squared_length
    )
    # The ideal minor semiaxis is at least next_floor. Center error has
    # ideal-ellipsoid norm <= delta (root approximation <= 1/(scale*k),
    # then grid error <= delta/2). Enlarge before rounding the shape.
    padded = (1 + delta)**2 * ideal
    grid = delta * next_floor**2 / k
    rounded = padded.applyfunc(lambda v: (v // grid) * grid) + k * grid * eye(k)
    # Entrywise errors have operator norm <= k*grid. Thus padded <= rounded
    # <= (1+2*delta)*padded. Extra log-volume <= 2*k*delta per step.
    return next_center, rounded, next_floor


def decode(n, known, missing, alphabet, readings, eta=0):
    """Return exact conductances under the noise promise of the theorem."""
    levels = sorted(set(map(Rational, alphabet)))
    y = list(map(Rational, readings))
    known = {edge: Rational(w) for edge, w in known.items()}
    k = len(missing)
    if k == 0 or len(levels) == 1:
        return [levels[0]] * k
    W = max([levels[-1], *known.values()])
    lam = 1 / (n * W)**2
    gap = min(b - a for a, b in zip(levels, levels[1:]))
    margin = lam * gap - Rational(eta)
    if margin <= 0:
        raise ValueError("The certified error bound must be strictly below the threshold.")
    lo, hi = levels[0], levels[-1]
    width = hi - lo
    H = 1 + 2*n + k*width*(max(map(abs, y)) + lam*width)
    protected = min(Rational(1, 2), margin*gap/(4*H)) * width / 4
    radius = k*(W + 1)
    ratio = radius / protected
    bits = max(1, int(ratio.p).bit_length() - int(ratio.q).bit_length() + 2)
    limit = 8*k*(k + 1)*(bits + 1)
    center, shape = zeros(k, 1), radius**2 * eye(k)
    low, high = -radius, radius  # the one-dimensional ellipsoid
    for _ in range(limit):
        normal = zeros(k, 1)
        outside = next((i for i, v in enumerate(center) if not lo <= v <= hi), None)
        if outside is not None:
            normal[outside] = 1 if center[outside] > hi else -1
        else:
            proposal = [min(levels, key=lambda a: abs(a - v)) for v in center]
            if optimal_certificate(n, known, missing, levels, y, lam, proposal):
                return proposal
            actual = resistances(n, known, missing, center)
            if actual is None:
                part = first_component(n, known, missing, center)
                normal = Matrix([-int((u in part) != (v in part)) for u, v in missing])
            else:
                for i, v in enumerate(center):
                    a, b = next((a, b) for a, b in zip(levels, levels[1:]) if a <= v <= b)
                    normal[i] = y[i] - actual[i] + lam*(a + b - 2*v)
        if not any(normal):
            raise ValueError("Zero cut at an uncertified point. Check the input promise.")
        if k == 1:
            if normal[0] > 0:
                high = center[0]
            else:
                low = center[0]
            center[0] = (low + high) / 2
        else:
            center, shape, radius = rounded_central_cut(center, shape, normal, radius)
    raise ValueError("No certified completion within the iteration bound. Check the noise promise.")
