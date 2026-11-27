# Generic and transversal ReLU parameters need not form an open set

Wentao Li · Prepared with assistance from OpenAI Codex · November 20, 2026

A curve of layer-generic parameters fails transversality at vertices escaping to infinity and converges to a generic, transversal parameter.

**Original question.** Is the full set of generic and transversal ReLU parameters open in the Euclidean parameter topology? [J. Elisenda Grigsby, Kathryn Lindsey, Robert Meyerhoff and Chenxi Wu, 2022, Conjecture following Lemma 5.6](https://arxiv.org/abs/2209.04036)

**Significance estimate.** 48/100. Disproves a specific topology conjecture and locates the failure on the unbounded input domain. The original paper already supplied the underlying escaping-intersection idea.

**Proof status.** Written argument awaiting independent review. **Priority status.** A targeted search through November 20, 2026 found the following related results. Independent priority review is pending.

Remark 5.4 of the source exhibits combinatorial instability of a transversal parameter. An added active feature and final threshold turn that geometric change into a loss of node transversality.

[Read the proof (PDF)](relu-transversality-at-infinity.pdf) · [LaTeX source](relu-transversality-at-infinity.tex) · [BibTeX](citation.bib)

**Reproducible check.** Checks 32 rational perturbations and verifies the vertex and threshold identities exactly. [Python script](verify.py)

## Sources

- [J. Elisenda Grigsby, Kathryn Lindsey, Robert Meyerhoff and Chenxi Wu (2022), Conjecture following Lemma 5.6](https://arxiv.org/abs/2209.04036)
- [Grigsby and Lindsey, On transversality of bent hyperplane arrangements, Definition 8.1](https://arxiv.org/abs/2008.09052)
- [Masden, Algorithmic determination of the combinatorial structure of the linear regions of ReLU neural networks](https://arxiv.org/abs/2207.07696)
