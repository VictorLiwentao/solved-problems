# Independent proof checks

Each per-draft configuration names a standalone Challenge and a Solution. In the local protected replay, Palomar’s verifier tools checked the Challenge imports and compiled the statements under a fresh module name. The comparator checked the separately built Solution against those statements. Lean, NanoDa and con-ron accepted each Solution export. The hashes below identify the proof exports from that run.

| Draft and configuration | Compared targets | Declarations replayed by con-ron | Solution export SHA-256 |
| --- | ---: | ---: | --- |
| [bounded-displacement-set-density](bounded-displacement-set-density/comparator.json) | 1 | 2,181 | `5a7dd606c84978688846c80db0574d62017a32bd698f672489599fb5f9610fb8` |
| [computable-online-learning-certificates](computable-online-learning-certificates/comparator.json) | 2 | 5,042 | `39b1d64db0fe7f821f532a4e14dabe51887bdbd208d1672a594d3eeeb3e7939e` |
| [packing-cutoff](packing-cutoff/comparator.json) | 1 | 1,583 | `be6edeac3556f3054025f20e2dda1b50fe16f06004dd1d2059f5ebf619d0b5fe` |
| [packing-powers](packing-powers/comparator.json) | 1 | 1,905 | `6ccdc4c68b05edd3d7e54347905eadc1602d994bda314c0b046cfd0d85c514e8` |
| [selected-disagreement-dimension](selected-disagreement-dimension/comparator.json) | 2 | 7,533 | `70bd56cc7c3ab14abd4adcf6047339a1886fae41ac258751ca51d4dfa8993c2b` |

All seven new targets use `propext`, `Classical.choice`, and `Quot.sound`. The Solution library contains the complete proofs. Each paper directory includes the scope, source revisions and alignment with the mathematical text in `formalization.yaml`.

The checks used Lean and Mathlib v4.35.0, the NanoDa bundled with that Lean release, and con-ron v4.36.0-rc1 selected by Palomar for this toolchain. [Reproduce the checks](../README.md#reproduce-the-checks) · [Verifier revision](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7)
