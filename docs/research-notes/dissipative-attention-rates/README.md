# Sharp collapse rates for dissipative softmax attention

Wentao Li · Prepared with assistance from OpenAI Codex · November 2026

Strict dissipation in the positive-definite key geometry sends every token to zero at worst on the inverse square-root time scale. Opposite rotating tokens attain that rate, and purely skew values admit periodic motion.

**Original question.** For what further classes of query, key and value matrices can the limiting token configuration be identified? [Geshkovski et al., 2023, Problem 5 and Table 1](https://arxiv.org/abs/2312.10794)

**Scope and prior work.** The source treats the negative identity value matrix. Here constants depend on the initial finite configuration and the fixed matrices. The full classification of triples remains open.

**Significance estimate.** 63/100. It gives a sharp uniform exponent in time for an entire matrix class, including nonnormal values, and exhibits failure of convergence of the rescaled direction.

**Review status.** Written argument. Independent proof and priority review are pending.

[Read the proof (PDF)](dissipative-attention-rates.pdf) · [LaTeX source](dissipative-attention-rates.tex)

## Sources

- [Borjan Geshkovski, Cyril Letrouit, Yury Polyanskiy and Philippe Rigollet (2023), Problem 5 and Table 1](https://arxiv.org/abs/2312.10794)
- [Geshkovski et al., The emergence of clusters, NeurIPS 2023](https://papers.neurips.cc/paper_files/paper/2023/file/b2b3e1d9840eba17ad9bbf073e009afe-Paper-Conference.pdf)
- [Castin et al., gradient structure for continuous attention](https://arxiv.org/abs/2501.18322)
