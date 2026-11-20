# Lean formalizations

[Result catalogue](../README.md) · [Python verification](../docs/verification.md)

**10 of 67 drafts have at least one main result proved end to end.** Four further drafts have partial coverage. The comparator checks 24 declarations. A draft can have several main results, so the table names the statement covered in each case.

| Coverage | What a reader can verify |
| --- | --- |
| Partial | A named theorem checks a specified lemma, special case, or certificate. The entry identifies the remaining mathematical step. |
| Complete | A named theorem checks the note’s main statement with its stated hypotheses. The entry points to the declaration, reproducible build, and axiom report. |

## Checked declarations

| Note | Declaration and scope | Remaining steps |
| --- | --- | --- |
| [Bounded-displacement identification](../results/learning-theory/bounded-displacement-identification/) | A learner identifies the target on every full repetition-free text meeting the rank deadlines exactly when every target and starting time admit the paper’s finite witness. [Proof](SolvedProblems/Displacement.lean) | The proof covers every nondecreasing integer deadline $D(t) \ge t$, including $D(t)=\lfloor Mt\rfloor$ for $M\ge1$. |
| [Contrastive progress and corruption](../results/learning-theory/contrastive-progress-and-corruption/) | Under the divergent honest-progress surplus promise, a countable family of at least two distinct infinite proper supports is identifiable exactly when the holes are finite and pairwise disjoint. [Proof](SolvedProblems/Progress.lean) | The indexed theorem counts each distinct honest positive once and each corrupt observation with multiplicity. The necessity proof constructs one honestly covering stream for two rival targets. |
| [Set-driven contrastive generation](../results/learning-theory/set-driven-contrastive-generation/) | For countably many infinite supports, every successful generator has a rule that uses only the set of observed edges. A second equivalence characterizes success by finite witnesses indexed by the target and its covering edge set. [Proof](SolvedProblems/SetDriven.lean) | Both equivalences quantify over full honest presentations with repeated observations allowed. |
| [Contrastive generation without compatible positive witnesses](../results/learning-theory/contrastive-generation-without-witnesses/) | A countable family of infinite proper supports admits a generator depending only on the observed edge set, yet every assignment of finite positive witnesses fails compatibility. [Proof](SolvedProblems/PositiveWitness.lean) | The construction exhausts the common core by finite squares. The generator chooses a fresh point shared by all consistent targets when one exists. Its fallback handles the satellite targets. |
| [Packing-preserving lift](../results/permutation-patterns/packing-catalan-lift/) | For every admissible seed and number of windows, the lifted packing order is the ordinal sum of a fresh chain and the original packing order. Inserting the chain induces a bijection of the packing permutations. [Proof](SolvedProblems/PackingLift.lean) | The general lift theorem and bijection are complete. [Window position check](SolvedProblems/PackingLayout.lean). The separate closed-form Catalan count for the 1324 seed remains outside this verification. |
| [Corrupted contrastive pairs](../results/learning-theory/robust-contrastive-closure/) | [`uniformCriterion`, `deletionCriterion`, `nonuniformCriterion`](SolvedProblems/GenerationThreshold.lean) give the exact distinct-edge threshold for every budget, its deletion interpretation, and the increasing-union criterion. [`unknownBudget`](SolvedProblems/ThreeSupports.lean) gives a single generator for every prefix with fewer than one-third violations in the three-support example. | Main uniform and nonuniform criteria complete. The example’s impossibility at the boundary is outside these proofs. |
| [Uniform list generation](../results/learning-theory/uniform-list-generation/) | [`listThresholdCriterion`](SolvedProblems/GenerationThreshold.lean) characterizes every admissible threshold for every positive list length, including threshold zero. [`twoGuessSeparation`](SolvedProblems/TwoGuess.lean) proves that two guesses can succeed from the first observation while a single part of every finite colouring has arbitrarily large exhausted intersections. | Exact threshold theorem complete. The separation uses the two-guess block construction on its countable word alphabet. Unary encoding, general list-size separation and randomized utility remain. |
| [Prompted generation](../results/learning-theory/prompted-generation-by-fibers/) | [`fiberReduction` and `countablePrompts`](SolvedProblems/PromptGeneration.lean) prove both directions of the reduction to ordinary fiber generation and construct a generator for countably indexed hypotheses over arbitrary labels with infinite fibers. | Fiber equivalence and countable-class result complete. The separate combinatorial witness characterization for arbitrary classes remains. |
| [Bouncer tapes](../results/computability/bouncer-tape-inclusion/) | [`emptyWallCounterexample`](SolvedProblems/TapeInclusion.lean) proves strict inclusion for every exponent, alignment, width three, primitivity, noncommutation, and distinct first repeaters. | Empty-wall counterexample complete. The general aligned, separated classification remains. |
| [Integer weights and promise compactness](../results/set-theory/promise-compactness/) | [`cyclicSpectrum`](SolvedProblems/PromiseMass.lean) proves exactly which arities admit cyclic and symmetric polymorphisms of the endpoint-preserving addition template. | Operation spectrum complete. The ZF compactness equivalence and model-theoretic conclusions remain. |
| [Last-guess identification](../results/learning-theory/last-guess-identification/) | [`LastGuess.oneBitSeparation`](SolvedProblems/LastGuess.lean) proves the deterministic impossibility on repetition-free texts and exact identification with one extra bit on arbitrary texts. It uses `propext`, `Classical.choice`, and `Quot.sound`. The singleton telltale theorem in the same module uses no axioms. | Deterministic main theorem complete. The randomized bound and the classification of nested families remain open formalization tasks. |
| [Oracle-free sound coverage](../results/learning-theory/oracle-free-sound-coverage/) | [`SoundCoverage.finiteWitnessCriterion`](SolvedProblems/SoundCoverage.lean) proves both directions of the finite-witness characterization for a countable family. The [definitions](SolvedProblems/SoundCoverageModel.lean) quantify over every full positive enumeration and allow arbitrary history-dependent learners. The proof uses `propext`, `Classical.choice`, and `Quot.sound`. | Complete. The theorem also applies to nonempty finite targets. |
| [Parking-function polynomial](../results/algebraic-combinatorics/parking-excedances/) | [`ParkingExcedances.signedCertificate`](SolvedProblems/ParkingExcedances.lean) proves the exact signed integer identity and strict negativity for the three printed values, with no hypotheses or axioms. | Derive the values from the polynomial and its derivatives, then apply the Laguerre inequality to prove the nonreal-root conclusion. |
| [Splitting the Busy Beaver runtime](../results/computability/splitting-busy-beaver/) | [`BusyBeaver.record_split`](SolvedProblems/RuntimeRecords.lean) proves the maximum identity for any finite list, natural-valued runtime function, and Boolean colouring. Either colour class can be empty. The proof uses `propext` and `Quot.sound`. | Instantiate the table with the halting machines at each state bound and formalize the splitting construction and its computability properties. |

## Reproduce the checks

Use Linux with Bubblewrap, Python 3, and the Lean release pinned in this directory. The Lake manifest pins Mathlib v4.35.0 and its dependencies. The Challenge imports `Std` and `Mathlib.Data.Set.Defs`. The sound-coverage and prompted-generation models represent a language as Mathlib’s `Set Nat`. [Toolchain](lean-toolchain) · [Dependency revisions](lake-manifest.json)

From the repository root, run

```sh
cd lean
lake build SolvedProblems Challenge
python3 check_proofs.py
```

The script runs Lake Comparator on all 24 names, replays the proof export with Lean’s kernel and NanoDa, and asks Lean for each theorem’s transitive axiom dependencies. For a con-ron replay, pass `--con-ron /path/to/con-ron`. Palomar publishes the checker revision and digest it uses for each Lean release. [Check script](check_proofs.py) · [Palomar checker revisions](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/checker-revisions.json)

On Lean 4.35.0, Lean’s kernel, NanoDa, and Palomar’s selected con-ron v4.36.0-rc1 accepted the proof export. Of the 24 theorems, 20 use all three permitted axioms. `BusyBeaver.record_split` and `PromiseMass.cyclicSpectrum` use only `propext` and `Quot.sound`. `ParkingExcedances.signedCertificate` and `LastGuess.singletonTelltale` are axiom-free.

## Palomar project

The standalone Challenge contains the definitions and 24 reference statements. Its theorem placeholders are intentional. The corresponding proofs compile in the separate Solution library. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. [Challenge](Challenge.lean) · [Solution](SolvedProblems.lean) · [Comparator configuration](comparator.json)

Use project path `lean`, comparator path `lean/comparator.json`, and metadata path `lean/formalization.yaml` for this batch. The metadata matches each declaration to a versioned draft and gives its scope. The combined Challenge exceeds Palomar’s preferred review size and fits its hard limits of 1,000 lines and 100 KiB. Registry review and registration require a public GitHub commit and the submitter’s attestation. [Metadata](formalization.yaml) · [Repository license](../LICENSE) · [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
