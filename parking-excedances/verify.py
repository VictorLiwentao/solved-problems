"""Two independent integer computations of the parking-function counterexample."""
from math import comb, factorial


def ferrers_sum(n, x):
    # After each preference value, h is the number of assigned entries minus
    # the number of preference values already processed.
    states = [1]
    for i in range(1, n+1):
        states = [sum(count * comb(x+h+1, h+1-prev)
                      for prev, count in enumerate(states[:h+2]))
                  for h in range(n-i+1)]
    return states[0]


def coefficients(n):
    values = [ferrers_sum(n, x) for x in range(n+1)]
    return [sum((-1)**j * comb(n+1, j)*values[k-j] for j in range(k+1))
            for k in range(n)]


def evaluations(poly):
    numbers = []
    for _ in range(3):
        d = len(poly)-1
        numbers.append(sum((-1)**i * 5**(d-i) * c for i, c in enumerate(poly)))
        poly = [i*poly[i] for i in range(1,len(poly))]
    return numbers


def labeled_subsets(n):
    """First three coefficients of 5^n P_n((z-1)/5) by assigning labeled cars."""
    size = 1<<n
    a, b, c = ([0]*size for _ in range(3))
    a[0] = 1
    for value in range(1,n+1):
        for car in range(1,n+1):
            bit = 1<<(car-1)
            # Process each pair of subsets with and without this car.
            for begin in range(0, size, 2*bit):
                if value > car:
                    for m in range(begin, begin+bit):
                        dest = m+bit
                        a[dest] -= a[m]
                        b[dest] += a[m]-b[m]
                        c[dest] += b[m]-c[m]
                else:
                    for m in range(begin, begin+bit):
                        dest = m+bit
                        a[dest] += 5*a[m]
                        b[dest] += 5*b[m]
                        c[dest] += 5*c[m]
        for m in range(size):
            if m.bit_count() < value:
                a[m] = b[m] = c[m] = 0
    return a[-1], b[-1], c[-1]


def main():
    n = 17
    p = coefficients(n)
    assert sum(p) == (n+1)**(n-1) and p[0] == factorial(n) and p[-1] == 1
    A, B, C = evaluations(p)
    a, b, c = labeled_subsets(n)
    assert (a, b, 2*c) == (5*A, 5*B, 5*C)
    delta = B*B-A*C
    expected = -1177338341095610033551509654796761547971187113984
    assert delta == expected
    print("Independent counts agree.")
    print("Scaled P, P', P'' =", (A, B, C))
    print("B^2 - AC =", delta)


if __name__ == "__main__":
    main()
