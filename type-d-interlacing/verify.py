"""Exact checks of consecutive type-D root interlacing. Requires SymPy."""
from itertools import permutations, product
from fractions import Fraction
from sympy import Poly, Rational, symbols

x = symbols("x")


def rows(q, last):
    """Yang and Zhang's refinement, divided throughout by 1+q."""
    one = Poly(1, x, domain="QQ")
    t = Poly(x, x, domain="QQ")
    row = [one, t, q*t, q*t*t]
    yield sum(row, one*0)
    for n in range(3, last + 1):
        total = sum(row, one*0)
        prefixes = [one*0]
        for entry in row:
            prefixes.append(prefixes[-1] + entry)
        row = []
        for i in range(2*n):
            cut = (i*(n-1) + n-1)//n
            p = total + (t-one)*prefixes[cut]
            row.append(q*p if i >= n else p)
        yield sum(row, one*0)


def signed_group(n, q):
    coefficients = [Fraction(0)] * (n+1)
    for perm in permutations(range(1, n+1)):
        for signs in product((1, -1), repeat=n):
            word = [sgn*a for sgn, a in zip(signs, perm)]
            descents = int(word[0]+word[1] < 0) + sum(a>b for a, b in zip(word, word[1:]))
            coefficients[descents] += q**signs.count(-1)
    return Poly.from_list([v/(1+q) for v in reversed(coefficients)], gens=x, domain="QQ")


def main():
    group_checks = interlacing_checks = 0
    for q in (Rational(1, 3), Rational(1), Rational(2), Rational(3)):
        polys = list(rows(q, 16))
        for n, p in enumerate(polys[:4], start=2):
            assert p == signed_group(n, Fraction(q))
            group_checks += 1
        for n, (small, large) in enumerate(zip(polys, polys[1:]), start=2):
            if q == 1 and n == 2:
                assert small == Poly((1+x)**2, x, domain="QQ")
                assert large == Poly((1+x)*(1+10*x+x*x), x, domain="QQ")
            else:
                # A positive-leading signed remainder chain with every degree
                # present is a Sturm certificate. Backward sign alternation
                # gives one root of each predecessor in every intervening gap.
                a = large.clear_denoms(convert=True)[1].primitive()[1]
                b = small.clear_denoms(convert=True)[1].primitive()[1]
                while b.degree() > 0:
                    assert a.LC() > 0 and b.LC() > 0
                    c = (-a.prem(b)).primitive()[1]
                    assert c.degree() == b.degree()-1 and c.LC() > 0
                    a, b = b, c
                assert all(v > 0 for v in large.all_coeffs()+small.all_coeffs())
            interlacing_checks += 1
    print(f"{group_checks} signed-group comparisons and {interlacing_checks} exact interlacing checks passed.")


if __name__ == "__main__":
    main()
