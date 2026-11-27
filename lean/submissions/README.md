# Independent proof checks

Each per-draft configuration names a standalone Challenge and a Solution. In the local protected replay, Palomar’s verifier tools checked the Challenge imports and compiled the statements under a fresh module name. The comparator checked the separately built Solution against those statements. Lean, NanoDa and con-ron accepted each Solution export. Each hash identifies the exact Solution export that passed the three kernels.

## First five individual projects

| Draft and configuration | Compared targets | Declarations replayed by con-ron | Solution export SHA-256 |
| --- | ---: | ---: | --- |
| [bounded-displacement-set-density](bounded-displacement-set-density/comparator.json) | 1 | 2,181 | `5a7dd606c84978688846c80db0574d62017a32bd698f672489599fb5f9610fb8` |
| [computable-online-learning-certificates](computable-online-learning-certificates/comparator.json) | 2 | 5,042 | `39b1d64db0fe7f821f532a4e14dabe51887bdbd208d1672a594d3eeeb3e7939e` |
| [packing-cutoff](packing-cutoff/comparator.json) | 1 | 1,583 | `be6edeac3556f3054025f20e2dda1b50fe16f06004dd1d2059f5ebf619d0b5fe` |
| [packing-powers](packing-powers/comparator.json) | 1 | 1,905 | `6ccdc4c68b05edd3d7e54347905eadc1602d994bda314c0b046cfd0d85c514e8` |
| [selected-disagreement-dimension](selected-disagreement-dimension/comparator.json) | 2 | 7,533 | `70bd56cc7c3ab14abd4adcf6047339a1886fae41ac258751ca51d4dfa8993c2b` |

All seven targets in the first table use `propext`, `Classical.choice`, and `Quot.sound`. The Solution library contains the complete proofs. Each paper directory includes the scope, source revisions and alignment with the mathematical text in `formalization.yaml`.

## Five more proofs from the original catalogue

The verifier built each standalone Challenge under a fresh module name. Lake Comparator compared it with the exported Solution, and all three kernels accepted the proof. The Challenge, Solution and their imported project modules matched the corresponding repository files byte for byte.

| Draft and configuration | Compared targets | Declarations replayed by con-ron | Solution export SHA-256 |
| --- | ---: | ---: | --- |
| [ramsey-finite-partition-model](ramsey-finite-partition-model/comparator.json) | 1 | 5,807 | `a1c4878e6a971ba57ea687198eed1f72571b399faaa25c6f94d07c38802c4dda` |
| [singleton-core-density](singleton-core-density/comparator.json) | 1 | 8,690 | `304544b874478debd46743f9d66801029ec03c1fd0363a5972eb6293c13b4e2e` |
| [packing-separators](packing-separators/comparator.json) | 6 | 2,079 | `ec9bb27a08fbee9cd8e5484123f7ba630a34a259c6e30a289baa818eb3bdaf35` |
| [bounded-jump-automaton](bounded-jump-automaton/comparator.json) | 1 | 11,789 | `a71ed6c84f419828db4dff013c371c08ce1f5a32486a6bbb8391954fa761153a` |
| [private-language-identification](private-language-identification/comparator.json) | 2 | 18,749 | `c9992a9addb65b001b2fa62cb48984f1665d8aecad67498353078835469def23` |

Of these 11 targets, 10 use all three standard axioms. `PackingSeparator.physical_iff` uses `propext` and `Quot.sound`.

## Packing, lattice paths, private generation and algebraic closures

The five protected comparisons cover 13 targets. Every target depends on `propext`, `Classical.choice`, and `Quot.sound`. The Challenge, Solution and their imported project sources matched the repository files byte for byte.

| Draft and configuration | Compared targets | Declarations replayed by con-ron | Solution export SHA-256 |
| --- | ---: | ---: | --- |
| [fuss-dyck-peaks](fuss-dyck-peaks/comparator.json) | 1 | 47,854 | `445c5eb71d3006e1e46d9c1717cbcbf78dfda74d7423e70ced6dc89cd10dfc00` |
| [packing-factorization](packing-factorization/comparator.json) | 3 | 5,126 | `707ce269d1a0774558620121cf03065a549a37b638b1d4fa83d3e9c6c8df3b11` |
| [private-generation-without-witness-bound](private-generation-without-witness-bound/comparator.json) | 1 | 14,740 | `bd3f422f9c23fb651e22d4f955f533bf8b3a55c793b5878caab9e3f99d6c42dd` |
| [private-generation-uncountable](private-generation-uncountable/comparator.json) | 7 | 29,171 | `bb4e5b2d83a3ce1e801ecd325748d2a3fd23f0931b09b8656d0bd7737429b133` |
| [algebraic-closures-partition-model](algebraic-closures-partition-model/comparator.json) | 1 | 22,170 | `eda717c65d7270e229f28f4e8fa56ca0e39661167d06e8c9a43ad0dc69121c25` |

## Rational Dyck paths, partition models and learning

The five protected comparisons cover 8 targets. Every target depends on `propext`, `Classical.choice`, and `Quot.sound`. The Challenge, Solution and their imported project sources matched the repository files byte for byte.

| Draft and configuration | Compared targets | Declarations replayed by con-ron | Solution export SHA-256 |
| --- | ---: | ---: | --- |
| [rational-dyck-run-return](rational-dyck-run-return/comparator.json) | 2 | 9,820 | `7fa6b9e522b6c92634e9e554396496e6f94e3292b1acd17d014cb4031406032f` |
| [amorphous-sets-finite-partition-model](amorphous-sets-finite-partition-model/comparator.json) | 1 | 5,842 | `a9b640f57064f19e09cd289a6dca71b681e64e20e527064cc3b807455bcfab02` |
| [well-orderable-unions-partition-model](well-orderable-unions-partition-model/comparator.json) | 1 | 7,808 | `91b133710ed767a7cfbd150dfae420a03f1087d65476a1b6af35c304a381637b` |
| [universal-multiclass-processes](universal-multiclass-processes/comparator.json) | 2 | 17,179 | `2d827a706e96ef4fa98a7639d58ca0fd554a46aaaf51bb6ee46d0f0f379ce7ed` |
| [prompted-generation-oracle](prompted-generation-oracle/comparator.json) | 2 | 28,758 | `4db9b723ccb8c9ead42fc85e9219e60d34857c20ca7f8f42a7179124a5a765db` |

## Formalizations from the expanded catalogue

Each reference in this group compiles independently with a checked proof body. The exported solution was replayed in Lean, NanoDa and con-ron. The metadata records the manuscript statement and its scope.

| Draft and configuration | Compared targets | Declarations replayed by con-ron | Solution export SHA-256 |
| --- | ---: | ---: | --- |
| [projective-amorphous-powers](projective-amorphous-powers/comparator.json) | 4 | 8,343 | `f00c2acc707dd3eb3d51414232e51bea1c1530ed609a7c1200a9057abdc73b1e` |
| [rigidity-ordinal-cubes](rigidity-ordinal-cubes/comparator.json) | 3 | 1,749 | `1d445819f58a6c0881ae6ed4dffbdc64d9ed5137430941db05a5029f398606bb` |
| [symmetric-erm](symmetric-erm/comparator.json) | 1 | 10,390 | `a5deec008cce24912324dcfb7fe75c42025f9c6e0af8b8ed64e9206a596b8cf0` |
| [binary-bandit-independence](binary-bandit-independence/comparator.json) | 10 | 32,841 | `ba0da73e0ce6c04714304859e475127428ea23ae62a408cbf53e2b39861a1a1c` |
| [resistance-blind-lifts](resistance-blind-lifts/comparator.json) | 1 | 34,387 | `4c7e9e1e1b91818be199d93da90168655ed69e5c8c263d2459ae910349ba444e` |
| [joint-distance-forest-counts](joint-distance-forest-counts/comparator.json) | 3 | 11,253 | `f41cf446b25ffb06e1199fbee538c9e03b99c8fce8af25f2c8e539bfc2e2af8c` |
| [rado-prime-ideal](rado-prime-ideal/comparator.json) | 2 | 4,873 | `5c226573564d97ec88e644026dd6b9e77fa21d218219b557b9a4c88a5529b0f7` |
| [finite-choice-frucht](finite-choice-frucht/comparator.json) | 3 | 2,110 | `911eacd4f020c55ac513856f19837fecf5dbf8262f5e4b975d574165a4de812a` |
| [domination-cobipartite-obstructions](domination-cobipartite-obstructions/comparator.json) | 4 | 5,744 | `2d8e11e18cede27449caeb53c82a4eb29a977de63e6548c7c901126c5b2109c4` |
| [emx-without-monotone-compression](emx-without-monotone-compression/comparator.json) | 2 | 35,007 | `fe3f27d070110f687db91839a654a533e0b3aa2062e6e1a844e185ea9748d500` |
| [projective-amorphous-powers-pregeometry](projective-amorphous-powers-pregeometry/comparator.json) | 2 | 7,118 | `a06f77369b1151d2493c1a12a2b4182cc38fa047a2c5a70340d98728f9dc3d20` |
| [finite-choice-frucht-principles](finite-choice-frucht-principles/comparator.json) | 2 | 2,389 | `6ecfd1b4c90eb9f3bbe127f61053b84bd7eb6972a9cdf05aba7db6849c79c91d` |
| [rado-prime-ideal-atoms](rado-prime-ideal-atoms/comparator.json) | 1 | 2,025 | `3cbb687fff8678e24fbdb660e23c4af30882dee04c833817c8199e8596f02beb` |

The checks used Lean and Mathlib v4.35.0, the NanoDa bundled with that Lean release, and con-ron v4.36.0-rc1 selected by Palomar for this toolchain. [Reproduce the checks](../README.md#reproduce-the-checks) · [Verifier revision](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7)
