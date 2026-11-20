# Contrastive generation without compatible positive witnesses

Wentao Li · Prepared with assistance from OpenAI Codex

A countable class admits a generator that uses only the observed edge set, yet defeats every assignment of the proposed finite positive witnesses.

Two fixed targets and a countable family of auxiliary targets share finite sets of positives. The negative partner of one observed point tells the generator which infinite block is safe. Finite lists of positive witnesses cannot record that partner.

**Original question.** Xiaoyu Li, Andi Han, Jiaojiao Jiang and Junbin Gao (2026), §8(i) and Definition 6.21. [Primary source](https://arxiv.org/abs/2605.06211v2)

**Significance estimate: 57/100.** Refutes a proposed necessity condition that holds on every finite class.

**Proof status.** Written research draft awaiting independent review. **Priority status.** A targeted literature check found the original question and related work. Priority awaits independent review.

The checker verifies the membership patterns, crossing partners and output branches on finite representatives of the construction. [Run the finite check](verify.py)

[Read the proof (PDF)](contrastive-generation-without-witnesses.pdf) · [LaTeX source](contrastive-generation-without-witnesses.tex) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/learning-theory/contrastive-generation-without-witnesses/citation.bib)

## Lean formalization

A countable family of infinite proper supports admits a generator depending only on the observed edge set, yet every assignment of finite positive witnesses fails compatibility. The construction exhausts the common core by finite squares. The generator chooses a fresh point shared by all consistent targets when one exists. Its fallback handles the satellite targets. The comparator checks `PositiveWitness.separation`. [Lean proof](../../../lean/SolvedProblems/PositiveWitness.lean) · [Reference statements](../../../lean/Challenge.lean)
