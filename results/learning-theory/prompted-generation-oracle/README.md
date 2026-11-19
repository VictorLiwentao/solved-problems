# The halting threshold for prompted language generation

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](prompted-generation-oracle.pdf) · [LaTeX source](prompted-generation-oracle.tex) · [Finite checks](verify.py) · [Research catalogue](../../../README.md) · [Cite this draft (BibTeX)](https://github.com/VictorLiwentao/solved-problems/blob/577ce01c676fcd75a05a8c36bf36246363219d93/citations.bib#L201-L207)

## Can a learner eventually complete every valid prompt?

Imagine that you can check whether a finished string belongs to any named candidate language. You see examples from one unknown candidate, and eventually every word of that language will appear. After each example you receive a prefix. You must return a previously unseen target word starting with that prefix. The promise is that at least one such word exists. You can make mistakes early on, but you must return an answer every round.

**In general this task requires a halting oracle.** Two fixed languages with polynomial-time membership tests already attain that threshold. Kleinberg and Mullainathan posed the question about nontrivial prompts in §7.2 of their full paper and proved that extra regular-subset queries suffice. Their conference paper also proves that membership tests suffice when the prompt has arbitrarily long completions in every candidate. [Full paper, §7.2](https://arxiv.org/pdf/2404.06757v1) · [NeurIPS 2024 paper](https://proceedings.neurips.cc/paper_files/paper/2024/hash/7988e9b3876ad689e921ce05d711442f-Abstract-Conference.html)

## Two languages suffice

One candidate accepts every binary word. The other accepts all strings of ones, plus words of the form $1^e0^{s+1}$ if program index $e$ has appeared in a fixed enumeration of the halting set within its first $s$ steps. Checking a finished word costs only a bounded simulation. But the prompt $1^e0$ has a completion in the second language exactly when program $e$ halts.

Why do early mistakes fail to help? Fix any finite history on the smaller target and present the next example. The learner must respond to *every* proposed prompt because that history could still have come from the all-strings language. If its responses were correct on all prompts that admit a completion in the smaller language, checking those responses would decide which programs halt. This argument lets an adversary force a deterministic learner to miss every round. For randomized learners, a single stream chosen independently of the coins can make the total expected number of correct rounds finite.

## What the proof characterizes

- **Two candidates.** For any infinite decidable language $K$ paired with the all-strings language, the exact oracle needed is the one that decides whether a prefix extends to some word of $K$. Every computably enumerable Turing degree occurs.
- **Arbitrary countable indexed families with computable membership.** A generator exists precisely when there is one effective bound on fresh answer length, valid for each target after some finite target-dependent set of words has been observed. The bound receives the current sample and prompt and must return on every possible input. Randomization gives the same characterization.
- **Polynomial time.** For a separate fixed pair that encodes satisfying assignments, a deterministic polynomial-time generator exists exactly when $\mathsf{P}=\mathsf{NP}$. With randomization and almost-sure eventual correctness, the corresponding condition is $\mathsf{RP}=\mathsf{NP}$. These are equivalences for the generation task.

## Proof and priority

The 6-page draft proves the results for arbitrary stream lengths. The checker exercises 255 stage-code prefix queries, 6,714 instances of the finite candidate-selection rule, and 1,792 witness searches with excluded samples. Independent review and formalization are pending.

The worst-case upper bound follows from Kleinberg and Mullainathan's Theorem 7.5. The proposed contributions are the matching lower bound, the family-level length criterion, and the randomized and polynomial-time consequences. I checked the original papers, searched for prior results on prefix completion, and screened citing preprints for work on prompts. The closest prompted characterization I found uses labeled examples for each prompt. The finite-witness characterization concerns unprompted generation. I found no earlier matching resolution. [Original question and upper bound](https://arxiv.org/pdf/2404.06757v1) · [Raman, Li and Tewari](https://proceedings.mlr.press/v291/raman25a.html) · [Charikar and Pabbaraju](https://proceedings.mlr.press/v291/charikar25a.html) · [Li, Han, Jiang and Gao](https://arxiv.org/abs/2609.10525)
