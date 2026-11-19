# Constant advice between successive prefix-free Busy Beaver records

Wentao Li · Prepared with assistance from GPT-6.2 Astra.

[Read the proof (PDF)](prefix-free-busy-beaver-advice.pdf) · [LaTeX source](prefix-free-busy-beaver-advice.tex)

## What one more program bit can tell us

Fix an optimal self-delimiting programming language and its step counter. Let $B(n)$ be the longest running time of any halting program of at most $n$ bits. In §5.5 of *The Busy Beaver Frontier*, Scott Aaronson asked if a constant number of advice bits suffices to compute $B(n+1)$ given only $B(n)$. His survey gave a logarithmic bound. In 2025 Trevor Terris gave a doubly logarithmic bound for a set of lengths of asymptotic density one. [Aaronson's question](https://doi.org/10.1145/3427361.3427369) · [Terris's result](https://tkterris.github.io/2025/03/13/evolving-busy-beavers.html)

**Yes.** There is a constant, depending only on the fixed machines, that works at every length. The decoder gets the current runtime and a short piece of correct advice. It can recover the next record even when the length $n$ is omitted. More generally, for an advance of $h\ge1$ program bits, the number of bits of prefix-free conditional information satisfies

$$ h-O(1)\ \le\ K(B(n+h)\mid B(n))\ \le\ h+K(h)+O(1). $$

Here $K(h)$ is the prefix complexity of the integer $h$. The leading term is one bit per additional program bit, uniformly in the starting length.

## What the advice can say

Only a bounded number of programs of length exactly $n+1$ can halt later than $B(n)$. The constant is uniform in $n$. The advice specifies their count and a bounded correction that recovers $n$ from the record time. Simulate all programs at the new length and wait until that many late halts have appeared. The last halt, or the old record if the count is zero, gives the answer. An incorrect count can make the wait run forever. Selecting correct advice uniformly would compute the Busy Beaver function.

The counting proof groups same-length halts into batches. Every completed batch generates a request for a short description of a string still missing when the batch finished. Prefix-freeness bounds the combined cost of these requests. For a sufficiently large fixed batch size, optimality forces each completed batch to finish before the old record, leaving at most one incomplete batch of late programs.

## The classical two-symbol machine

Write $S(n)$ for the longest halting runtime of a binary machine with at most $n$ states. The average of $K(S(n+1)\mid S(n))$ over $1\le n<N$ is $\Theta(\log N)$. The proof uses the known estimate $K(S(n))=n\log_2 n+O(n)$, the fact that a later record lets one reconstruct earlier records, and a telescoping sum. The note also shows that a logarithmic bound at *every* state count is equivalent to a pointwise logarithmic upper bound on the increase of $K(S(n))$. That pointwise question remains open in the sources checked. [Aaronson's Theorem 21 and follow-up question](https://docs.bbchallenge.org/papers/Aaronson2020.pdf)

## What this says about a single bit

The note also examines Dan Brumleve's suggestion to extract an algorithmically random sequence by applying a computable bit rule to successive records. For the usual binary **state-count** Busy Beaver, a total computable rule can extract the successive bits of a universal halting probability, up to a finite initial segment. For **prefix-free program-length** records, every computable one-bit rule fails to give a Martin-Löf random sequence, even when supplied the index. These statements concern designed bit rules. The computability of ordinary parity for the state-count Busy Beaver remains open in the sources checked. [Brumleve's suggestion](https://math.stackexchange.com/questions/271834/what-properties-of-busy-beaver-numbers-are-computable) · [Drucker's parity question, §5.11](https://docs.bbchallenge.org/papers/Aaronson2020.pdf)

## Proof and priority

The five-page note gives two arguments for the constant one-step bound. The first deduces it from Tadaki's 2009 runtime-complexity estimate and the standard addition theorem for prefix complexity. The second proves the bound on the number of individual late halts by Kraft–Chaitin coding. I found no earlier explicit resolution of Aaronson's constant-advice question in the sources checked. Independent review and Lean formalization are pending. [Tadaki, Theorem 3.9](https://arxiv.org/abs/0904.1149) · [Proof PDF](prefix-free-busy-beaver-advice.pdf)
