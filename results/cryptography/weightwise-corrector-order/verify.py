"""Check the compressed Littlewood certificate and the slice-to-Walsh identity."""
from itertools import product
from math import comb

# Left halves from Buhler et al., Table 5 of arXiv:1912.03491v1.
HALVES = {
    (48, 6): "C27D8C",
    (144, 8): "A962D5AF05357231CD",
    (192, 9): "C1BE1E21CD63D295A7887A59",
    (208, 8): "C5A2CB6B945B28BC43ADB6586C",
    (272, 8): "D0EC315B66B4DE6110D339D63B4CD61BC4",
}
# Positive exponents in the first half of Berend and Golan's antisymmetric P(112,7).
POSITIVE_112 = {0,2,5,7,8,11,12,15,17,20,21,23,24,26,27,30,
                32,35,36,38,39,41,45,47,48,50}


def finite_certificate(length, order, left):
    assert len(left) == length // 2
    signs = left + [(-1) ** order * v for v in reversed(left)]
    for k in range(order + 1):
        coefficient = sum(sign * comb(i, k) for i, sign in enumerate(signs))
        if k < order:
            assert coefficient == 0
    assert coefficient != 0
    return (length, order, coefficient)


def tensor(factors):
    length, order, leading = 1, 0, 1
    for new_length, new_order, new_leading in factors:
        leading *= new_leading * length ** new_order
        length *= new_length
        order += new_order
    return length, order, leading


def check_seed():
    pieces = {}
    for (length, order), word in HALVES.items():
        bits = format(int(word, 16), f"0{length//2}b")
        pieces[length] = finite_certificate(length, order, [1 if bit == "1" else -1 for bit in bits])
    pieces[112] = finite_certificate(112, 7, [1 if i in POSITIVE_112 else -1 for i in range(56)])
    for length in (16, 8192):
        pieces[length] = tensor([(2, 1, -1)] * (length.bit_length() - 1))
    blocks = [
        [144] * 2 + [192] * 4,
        [48] * 3 + [112] + [192] * 3,
        [16] + [112] * 2 + [208, 272] + [192] * 2,
        [112] + [208] * 4 + [8192],
    ]
    certificates = [tensor([pieces[key] for key in block]) for block in blocks]
    assert sum(length for length, _, _ in certificates) == 2**51
    assert all(order == 52 for _, order, _ in certificates)
    # Orient each block so its degree-52 Taylor coefficient is positive.
    assert sum(abs(leading) for _, _, leading in certificates) > 0
    print("Six finite witnesses and two Thue–Morse factors give four blocks of total length 2^51 and exact order 52.")


def check_walsh():
    cases = 0
    for n in range(1, 9):
        slices = [[x for x in range(1 << n) if x.bit_count() == k] for k in range(n+1)]
        odd = [k for k, xs in enumerate(slices) if len(xs) % 2]
        for bits in product((-1, 1), repeat=len(odd)):
            imbalances = dict(zip(odd, bits))
            if sum(bits):
                continue
            signs = [0] * (1 << n)
            for k, xs in enumerate(slices):
                positive = (len(xs) + imbalances.get(k, 0)) // 2
                for i, x in enumerate(xs):
                    signs[x] = 1 if i < positive else -1
            size = 1
            while size < len(signs):
                for start in range(0, len(signs), 2 * size):
                    for i in range(start, start + size):
                        u, v = signs[i], signs[i + size]
                        signs[i], signs[i + size] = u + v, u - v
                size *= 2
            walsh_order = next(k for k, xs in enumerate(slices) if sum(signs[a] for a in xs))
            zero_order = next(k for k in range(n+1) if sum(v * comb(i, k) for i, v in imbalances.items()))
            assert walsh_order == zero_order
            cases += 1
    print(f"Direct Walsh transforms agree with the moment criterion for {cases} balanced slice profiles.")


if __name__ == "__main__":
    check_seed()
    check_walsh()
