# A finite automaton for bounded jumps and arbitrary forbidden permutation patterns

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](bounded-jump-automaton.pdf) · [LaTeX source](bounded-jump-automaton.tex) · [Result catalogue](../../../README.md)

## Original question

Fix a maximum adjacent jump $m$. Nadler gave a finite-state enumeration for permutations avoiding 123 and asked which other patterns allow such an enumeration. He also asked for a counting algorithm with running time $f(m,k)n^{O(1)}$ when the longest increasing subsequence has length less than $k$. [Original paper, §9.2](https://arxiv.org/pdf/2610.02526#page=47)

## Result

**Every finite set of forbidden classical patterns admits such an enumeration.** There is an effectively constructible finite automaton for each jump bound $m$ and pattern set $B$. Its accepted histories correspond one-to-one to the permutations. The ordinary generating function by length is rational. Once the transitions are built, computing all counts through length $n$ takes $O_{m,k}(n)$ additions, where $k$ is the largest pattern length. The state bound can grow rapidly with $m$ and $k$.

The algorithm inserts values in increasing order. A slot marks a nonempty run of entries still to come. At most $2m$ slots can stay open, since an entry on an open boundary must be among the last $m$ values inserted. To recognize patterns, the algorithm records the relative order of each subsequence of length less than $k$ and which slots separate its entries. This information determines exactly where a new largest value can occur in a forbidden pattern.

The note also gives a second proof by encoding each value's successor as a signed offset and expressing pattern avoidance in monadic second-order logic on words. The two proofs use classical insertion encoding and the classical finite-word theorem. [Albert, Linton, and Ruškuc](https://doi.org/10.37236/1944) · [Elgot](https://doi.org/10.1090/S0002-9947-1961-0139530-9)

## Running the algorithm

From this directory, the following example counts permutations with jumps at most two and no increasing subsequence of length four.

~~~py
from verify import counts

print(counts(m=2, patterns=[(1, 2, 3, 4)], n=10))
# [1, 1, 2, 6, 11, 13, 17, 26, 40, 60, 88]
~~~

Running the checker compares the algorithm with direct enumeration at each length from zero through seven for 39 combinations of jump bound and pattern set, including mixed lengths.

~~~sh
python3 verify.py
~~~

A search found no prior general solution to the two questions in §9.2. Earlier work gives finite-state descriptions for individual patterns. Independent review and Lean formalization are pending. [Earlier 132 case](https://arxiv.org/abs/2605.23519) · [Algorithm and checker](verify.py)
