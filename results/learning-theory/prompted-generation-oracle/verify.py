"""Finite checks for the prefix coding, bounded selection, and SAT self-reduction."""

from itertools import product


def binary_words(length):
    return ("".join(bits) for bits in product("01", repeat=length))


def subsets(words):
    for mask in range(1 << len(words)):
        yield frozenset(word for i, word in enumerate(words) if mask & (1 << i))


def check_stage_encoding():
    # A finite enumeration emitting e at the indicated time. The infinite
    # word language still has arbitrarily long continuations for each emission.
    emitted_at = {0: 4, 2: 19, 3: 1, 6: 8}

    def member(word):
        index = len(word) - len(word.lstrip("1"))
        suffix = word[index:]
        if not suffix:
            return True
        return (
            "1" not in suffix
            and index in emitted_at
            and emitted_at[index] <= len(suffix) - 1
        )

    checks = 0
    for length in range(8):
        for prompt in binary_words(length):
            index = len(prompt) - len(prompt.lstrip("1"))
            suffix = prompt[index:]
            expected = not suffix or ("1" not in suffix and index in emitted_at)
            # Every possible continuation here can be taken to append just
            # zeros, or the empty suffix if the prompt is already a member.
            witnesses = [prompt + "0" * k for k in range(max(emitted_at.values()) + 3)]
            assert any(member(word) for word in witnesses) == expected
            checks += 1
    print(f"Checked {checks} prefix queries in a finite-stage enumeration example.")


def select_candidate(family, sample, prompt, bound):
    eligible_traces = []
    chosen = None
    for language in family:
        if not sample <= language:
            continue
        trace = {word for word in language if len(word) <= bound}
        matches = {word for word in trace - sample if word.startswith(prompt)}
        if not matches:
            continue
        if all(trace <= earlier for earlier in eligible_traces):
            chosen = min(matches, key=lambda word: (len(word), word))
        eligible_traces.append(trace)
    return chosen


def check_critical_selection():
    # Labels are ordered, so all choices of earlier/later competing candidates occur.
    universe = ("0", "10", "11")
    languages = list(subsets(universe))
    checks = 0
    for family in product(languages, repeat=3):
        for index, target in enumerate(family):
            for sample in subsets(sorted(target)):
                if not sample:
                    continue
                if any(sample <= prev and not target <= prev for prev in family[:index]):
                    continue
                for prompt in ("", "0", "1", "10", "11"):
                    for bound in (1, 2):
                        valid = {w for w in target - sample if w.startswith(prompt) and len(w) <= bound}
                        if valid:
                            assert select_candidate(family, sample, prompt, bound) in valid
                            checks += 1
    assert checks
    print(f"Checked {checks} eligible-target instances of the critical-language rule.")


def recover_witness(assignments, prefix, seen):
    """Use only the nonemptiness decision query in the recovery loop."""
    def exists(lead):
        return any(a.startswith(lead) and a not in seen for a in assignments)

    if not exists(prefix):
        return None
    length = len(next(iter(assignments)))
    while len(prefix) < length:
        prefix += "0" if exists(prefix + "0") else "1"
    return prefix


def check_witness_recovery():
    assignments = list(binary_words(2))
    checks = 0
    for satisfying in subsets(assignments):
        for seen in subsets(assignments):
            for size in range(3):
                for prefix in binary_words(size):
                    legal = {a for a in satisfying - seen if a.startswith(prefix)}
                    witness = recover_witness(satisfying, prefix, seen)
                    assert (witness is None and not legal) or witness in legal
                    checks += 1
    print(f"Checked {checks} witness searches including previously seen assignments.")


if __name__ == "__main__":
    check_stage_encoding()
    check_critical_selection()
    check_witness_recovery()
