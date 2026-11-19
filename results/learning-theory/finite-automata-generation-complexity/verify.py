"""Test unary table lookup, reset transitions, and finite intersections for small alphabets."""
from functools import cache
from itertools import product


def encode(address):
    return "".join("a" * i + "b" + "a" * value + "c"
                   for i, value in enumerate(address, 1)) + "p"


def table_comparison(text, table):
    remaining = index = 0
    phase = "index"
    order = 0
    for token in text:
        if token == "p":
            return order
        if order:
            continue
        if token == "a":
            if phase == "index":
                index += 1
            elif remaining:
                remaining -= 1
            else:
                order = 1
        elif token == "b":
            remaining = table[index - 1]
            phase = "value"
        elif token == "c":
            order = -int(remaining > 0)
            index = 0
            phase = "index"
    raise ValueError("missing payload")


def next_state(flags, address):
    if flags & (1 << address):
        return None
    return (flags & ((1 << address) - 1)) | (1 << address)


def legal(addresses):
    for i, address in enumerate(addresses):
        for other in addresses[i + 1:]:
            if other < address:
                break
            if other == address:
                return False
    return True


def main():
    comparisons = 0
    for k in (2, 3):
        tables = list(product(range(1, k + 1), repeat=k))
        for actual, target in product(tables, repeat=2):
            expected = (actual > target) - (actual < target)
            assert table_comparison(encode(actual), target) == expected
            comparisons += 1
    words = 0
    for length in range(8):
        for addresses in product(range(4), repeat=length):
            flags = 0
            for address in addresses:
                flags = next_state(flags, address)
                if flags is None:
                    break
            assert (flags is not None) == legal(addresses)
            words += 1

    for n in range(1, 8):
        @cache
        def totals(flags):
            children = [state for i in range(n)
                        if (state := next_state(flags, i)) is not None]
            if not children:
                return 0, 1
            # Reading each instruction strictly increases the binary number whose
            # most significant digit is the flag of the least address.
            below = [totals(state) for state in children]
            return 1 + max(h for h, _ in below), 1 + 2 * sum(c for _, c in below)

        height, count = totals(0)
        assert height == (1 << n) - 1
        assert count >= 1 << height
    print(f"Checked {comparisons} table comparisons, {words:,} words, "
          "and exact maximum lengths and counts for 1 through 7 addresses.")


if __name__ == "__main__":
    main()
