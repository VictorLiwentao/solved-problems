# One induced colouring-graph polynomial for each graph

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](one-colouring-probe.pdf) · [LaTeX](one-colouring-probe.tex) · [Citation](citation.bib) · [Exact check](verify.py)

## Original problem

Can each individual graph be distinguished from every other graph by the induced-copy polynomial for one suitably chosen test graph? [Shamil Asgarli, Sara Krehbiel, Howard W. Levinson and Heather M. Russell, 2024](https://arxiv.org/abs/2401.12883) (Section 6, discussion preceding the colouring-graph reconstruction conjectures).

## Result

For each finite simple graph G, a single connected test graph of polynomial size distinguishes G from every other graph. Two leading coefficients recover the order and edge count, and an induced embedding of the chosen test graph forces spanning containment.

Hogan, Scott, Tamitegama and Tan proved reconstruction from the whole colouring graph at a sufficiently large palette and ruled out a fixed finite family of test graphs. Here a single induced-copy polynomial is chosen for the particular graph. [Their paper](https://arxiv.org/abs/2402.04237)

**Significance 69/100.** Answers the graph-dependent reconstruction question for every finite simple graph. A fixed finite family of probes for all graphs is already known to be insufficient. Independent proof and priority review is pending.
