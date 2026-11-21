"""Exact two-block membership for rational matrices, plus reproducible examples."""
from itertools import combinations_with_replacement, product

from sympy import Matrix, eye, zeros


def normal_forms(d, budgets):
    """Yield canonical subspace triples as lists of row basis vectors."""
    rows = [eye(d).row(j) for j in range(d)]
    for planes in range(min(d // 2, *budgets) + 1):
        num_lines = d - 2 * planes
        for bits in combinations_with_replacement(range(8), num_lines):
            dimensions = [planes + sum(bool(b & (1 << i)) for b in bits) for i in range(3)]
            if any(dim > bound for dim, bound in zip(dimensions, budgets)):
                continue
            spaces = [[], [], []]
            for row, membership in zip(rows, bits):
                for index, space in enumerate(spaces):
                    if membership & (1 << index):
                        space.append(row)
            for i in range(num_lines, d, 2):
                spaces[0].append(rows[i])
                spaces[1].append(rows[i+1])
                spaces[2].append(rows[i] + rows[i+1])
            yield spaces


def membership(X, Y, budgets):
    """Decide if X=A+C, Y=B+C with the three prescribed rank bounds."""
    if X.shape != Y.shape or not X.rows or not X.cols:
        raise ValueError("Expected two nonempty matrices of the same shape")
    if len(budgets) != 3 or any(type(b) is not int or b < 0 for b in budgets):
        raise ValueError("Expected three nonnegative integer budgets")
    if not all(z.is_Rational for matrix in (X, Y) for z in matrix):
        raise ValueError("Use exact rational matrix entries")
    d = X.cols
    blank = zeros(1, d)
    for P, Q, R in normal_forms(d, budgets):
        srows = ([p.row_join(blank) for p in P] + [blank.row_join(q) for q in Q]
                 + [r.row_join(r) for r in R])
        S = Matrix.vstack(*srows) if srows else zeros(0, 2*d)
        constraints = []
        for vector in S.nullspace():
            left, right = vector[:d, :], vector[d:, :]
            for i in range(X.rows):
                constraints.append([X[i,j]*left[k] + Y[i,j]*right[k]
                                    for j in range(d) for k in range(d)])
        H = Matrix(constraints) if constraints else zeros(0, d*d)
        basis = [v.reshape(d, d) for v in H.nullspace()]
        if not basis:
            continue
        # A degree-d determinant polynomial vanishes identically iff it
        # vanishes on this grid. Shortcut cheap witnesses before the full test.
        if any(M.det() != 0 for M in basis) or sum(basis, zeros(d)).det() != 0:
            return True
        for coeffs in product(range(d+1), repeat=len(basis)):
            G = sum((c*M for c, M in zip(coeffs, basis)), zeros(d))
            if G.det() != 0:
                return True
    return False


if __name__ == "__main__":
    I = eye(2)
    assert not membership(I, 2*I, (1,1,1))
    assert membership(I, Matrix.diag(1,2), (1,1,1))
    assert membership(zeros(1,2), zeros(1,2), (0,0,0))
    assert not membership(I, zeros(2), (1,0,0))
    assert membership(I, zeros(2), (2,0,0))
    # A simultaneous invertible change of row and column coordinates
    # preserves feasibility.
    left = Matrix([[1,2],[1,3]])
    right = Matrix([[2,3],[1,2]])
    assert not membership(left * I * right, left * (2*I) * right, (1,1,1))
    assert membership(left * I * right, left * Matrix.diag(1,2) * right, (1,1,1))
    # One row pair in each possible coordinate configuration is enough
    # to exhaust the one-dimensional case, including the shared budget.
    for x, y in product(range(3), repeat=2):
        for a, b, c in product(range(2), repeat=3):
            expected = any((a or x == z) and (b or y == z) and (c or z == 0)
                           for z in {0,x,y})
            assert membership(Matrix([[x]]), Matrix([[y]]), (a,b,c)) == expected
    print("Passed 72 scalar cases and seven matrix cases, including an unattained boundary pair.")
