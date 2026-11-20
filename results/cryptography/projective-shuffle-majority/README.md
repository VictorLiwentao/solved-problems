# A projective shuffle for private majority and three-party predicates

Wentao Li · Prepared with assistance from OpenAI Codex

[Proof (PDF)](projective-shuffle-majority.pdf) · [LaTeX](projective-shuffle-majority.tex) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/cryptography/projective-shuffle-majority/citation.bib)

One uniform permutation from a 60-element group suffices. Turning over all six cards reveals exactly the majority bit. Over larger projective lines, the same construction realizes precisely the three-party predicates expressible as an XOR of pairwise terms, with one marked point per sender.

**Original question.** Shizuru Iino, Shota Ikeda, Kazumasa Shinagawa, Yang Li, Kazuo Sakiyama and Daiki Miyahara, 2025. [§4, second open problem (CANS 2025)](https://daikimiyahara.github.io/pdf/cans2025.pdf)

## Argument

Label the six positions by the projective line over the five-element field. The shuffle preserves the square class of a determinant product and mixes all triples with the same class uniformly. The three standard input pairs can be placed so this class gives majority.

## Status and significance

**Proof.** The PDF contains the written argument. Independent review is pending. The check constructs all 60 permutations and verifies correctness and complete transcript multiplicities for every input. [Run the check](verify.py)

**Priority.** Independent priority review is pending. Toyoda, Miyahara and Mizuki gave a six-card majority protocol using two elementary shuffles at INDOCRYPT 2021. The CANS authors asked about one uniform subgroup shuffle. The projective group and the Paley graph extension theorem are classical. [Prior majority protocol](https://www.tains.tohoku.ac.jp/netlab/mizuki/conf/card3maj_indocrypt2021_web.pdf) · [Paley graph theorem](https://doi.org/10.1002/jgt.3190050414)

**Significance · 53/100.** Answers a concrete secure-computation question and gives a structural extension to finite input alphabets. The resource bound counts an ideal group shuffle as a single operation. [Scoring benchmark](../../../docs/scores-and-sources.md)
