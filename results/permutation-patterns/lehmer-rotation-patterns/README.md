# Which permutation pattern counts are homomesic under Lehmer rotation?

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](lehmer-rotation-patterns.pdf) · [LaTeX](lehmer-rotation-patterns.tex) · [Citation](citation.bib) · [Exact check](verify.py)

## Original problem

Which individual permutation patterns have the same average number of occurrences on every orbit of Lehmer code rotation for every permutation size? [Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker and Amanda Welch, 2023](https://arxiv.org/abs/2206.13409) (Problem 4.36, added in the March 2023 revision).

## Result

The classification covers ordinary patterns, required position adjacencies and either endpoint anchor. No pattern of length at least four qualifies. At length three, the possible bonds depend on whether the pattern is monotone.

The result classifies individual patterns in the positional sense used in Section 4.4. Linear combinations of counts and additional constraints on values are distinct questions.

**Significance 58/100.** Completes the classification for individual position-vincular patterns, including endpoint anchors. The original paper had already established several positive and negative cases. Independent proof and priority review is pending.
