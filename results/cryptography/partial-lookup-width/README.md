# How many bits must a shared lookup emit for XOR decoding?

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

[Proof (PDF)](partial-lookup-width.pdf) · [LaTeX](partial-lookup-width.tex) · [Finite checks](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/partial-lookup-width/citation.bib)

In a lookup table with several outputs, some output bits may only be used on particular addresses. Suppose the table emits one shared word for an address, and each output must be recovered from that word with XORs and constants. We ask for the smallest possible width of the shared word. This is a preprocessing question motivated by Heath, Kolesnikov and Ng’s garbled lookup tables. [EUROCRYPT 2024](https://eprint.iacr.org/2024/369)

**Where XOR decoding costs extra.** If each output specifies a bit on at most **three** addresses, XORs and constants always attain the same minimum width as unrestricted output functions. At **four**, a gap appears. On four addresses, include an output column for each possible four-bit labeling. An unrestricted decoder can use a two-bit address. All four addresses must have distinct encodings. On the four two-bit words, any affine function takes the value one on zero, two or four addresses, so it cannot recover the column with exactly one one. Three shared bits suffice.

**General result.** Connect two addresses if an output requires different bits on them, and let $k$ be the chromatic number of this conflict graph. Unrestricted output decoding costs $\lceil\log_2 k\rceil$ bits. With at most $s$ specified addresses per output, the worst affine width for fixed $s\ge2$ is $\lfloor s/2\rfloor\log_2 k+O_s(1)$. The manuscript also gives an exact test and counting formula for each individual table.

**Proof idea.** An affine decoder can fit the specified bits unless an even set of encoded addresses sums to zero while their required bits sum to one. For three or fewer addresses only pairwise conflicts can occur. For larger sets, counting distinct subset sums gives a lower bound and classical binary BCH codes attain its leading term.

**Proof status.** The manuscript proves the per-instance criterion and the worst-case theorem for every fixed column size. Checks include 5,913 direct interpolation comparisons and 3,072 counts of admissible encodings. Independent review is pending.

**Priority status.** We formulated the partial-lookup question. Zero-error graph coloring, the matroid critical problem and the BCH construction supply established ingredients. Priority for this lookup formulation remains unverified. [Witsenhausen](https://doi.org/10.1109/TIT.1976.1055607) · [Matroid critical problem](https://www.sciencedirect.com/science/article/pii/S0195669881800054) · [Bose and Ray-Chaudhuri](https://www.sciencedirect.com/science/article/pii/S0019995860902874)

**Significance · 52/100.** The exact breakpoint and worst-case bound quantify the cost of a restricted output layer. The resource measured is emitted word width, one component of the cost of a garbled lookup. [Scoring benchmark](../../../docs/scores-and-sources.md)
