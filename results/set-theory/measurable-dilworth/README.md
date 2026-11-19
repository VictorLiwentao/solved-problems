# When measurable Dilworth decompositions exist

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](measurable-dilworth.pdf) · [LaTeX source](measurable-dilworth.tex)

Bosek, Grytczuk and Lonc asked whether a measurable poset of width $k$ can be partitioned into $k$ measurable chains after deleting a null set. This draft gives a counterexample of width two in which every measurable chain has measure zero. It uses the definition of ordered probability space cited in the question. [Conjecture 3](https://arxiv.org/abs/2004.02162) · [Definition 1.3 of Hladký, Máthé, Patel and Pikhurko](https://doi.org/10.1090/S0002-9947-2015-06299-0)

## The example and its boundary

Choose two points on each vertical line of the unit square, arranging that every positive-area compact set contains a chosen pair on the same line. Give the resulting space its trace Borel probability measure and order the points by first coordinate. Two independent points are comparable with probability one. Yet every positive measurable subset contains an incomparable pair. The space is separable metric, its order is open, and the conclusion persists under completion of its measure.

On a perfect probability space the manuscript gives a criterion. A finite-width measurable order admits the required chain partition precisely when a countable family of measurable sets separates the points of some conull set. This includes standard Lebesgue spaces with the order measurable in the ordinary product sigma algebra. The positive direction uses the earlier Borel chain theorem of Kada and Carroy, Miller and Vidnyánszky. [Definable Dilworth theorem](https://doi.org/10.1142/S0219061321500057)

The paper also gives a counterexample on the usual Lebesgue square if only the completed product is required. It proves the almost-every-pair version on every atomless space.

## Proof and priority status

The proof uses a transfinite construction, measurable envelopes, and the published Borel theorem. The planar construction follows a classical method. A finite simulation cannot test the measure-theoretic conclusion. Independent proof and priority review and Lean formalization are pending. [Sierpiński’s planar construction](https://doi.org/10.4064/fm-1-1-112-115)
