# How often does a random network fail the granular-synchrony condition?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

[Proof (PDF)](random-granular-synchrony.pdf) · [LaTeX](random-granular-synchrony.tex) · [Finite checks](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/random-granular-synchrony/citation.bib)

Some links between parties can deliver messages within a known time bound. Giridharan and coauthors characterized which arrangements of those links support agreement. Appan, Heath and Ren established the role of the same condition in secure multiparty computation. We ask how likely it is that a random arrangement fails this test, allowing the fault set to be chosen after the network is drawn. [DISC 2024](https://doi.org/10.4230/LIPIcs.DISC.2024.30) · [ASIACRYPT 2025](https://eprint.iacr.org/2025/1327)

**Result.** Suppose the synchronous links are independent, each has probability at least $p_*$, and $np_*/\log n$ tends to infinity. Let $f$ be the fault budget, with $n/3\le f<n/2$ and $h=n-2f$ at least a fixed positive fraction of $n$. Conditional on failure, with probability tending to one there is **one separating partition**, up to exchanging its sides. In particular, the expected number of separating partitions gives the failure probability to relative error tending to zero, even when link probabilities differ.

For example, if each link is synchronous with probability $p$ and $f/n$ tends to a constant strictly between one third and one half, the failure probability is asymptotic to

$$
\frac{n!}{h!(f!)^2}(1-p)^{hf}.
$$

Here the two separated groups have $h$ and $f$ parties, and $f$ further parties are excluded. At exactly $n=3f$ there is an additional factor of one half because the two groups have equal size.

**Proof idea.** Condition on the absence of links across one candidate partition. Any competing partition has to suppress additional independent links. Counting these by the number of parties that change groups makes the probability of a competitor tend to zero. The manuscript also identifies a sparser regime where many partitions describe the same failure and the first-moment estimate overcounts by an unbounded factor.

**Proof status.** The asymptotic statements have written proofs. The accompanying check enumerates 33,800 small weighted networks and verifies the overlap estimates on 16,237 pairs of partitions. Independent review is pending.

**Priority status.** We formulated the random-network question. Karger studied the relation between expected cut counts and failure probabilities for ordinary network disconnection. Here faults can exclude an entire third set of vertices. Priority for this granular-synchrony result remains unverified. [Karger, STOC 2020](https://people.csail.mit.edu/karger/Papers/lastrel-stoc.pdf)

**Significance · 58/100.** The theorem gives a relative-error probability and identifies the typical obstruction in a failing network. Its applicability depends on independent link assignments and the stated density regime. [Scoring benchmark](../../../docs/scores-and-sources.md)
