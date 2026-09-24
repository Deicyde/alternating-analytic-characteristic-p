# Alternating precomposition in positive characteristic

Private repository: [Deicyde/alternating-analytic-characteristic-p](https://github.com/Deicyde/alternating-analytic-characteristic-p).

Lean formalization of **Precomposition on continuous alternating maps is not analytic in positive characteristic**, from the supplied `charp.pdf` (round 24).

## Main result

For every prescribed nontrivially normed field K of prime characteristic p, including incomplete fields, and every k ≥ p, there are K-Banach spaces E and F such that:

- E′ = E;
- F admits no equivalent ultrametric norm;
- degree-k alternating precomposition is analytic at no point;
- the same spaces work for every finite index type of cardinality k.

The theorem is `AlternatingAnalytic.exists_banach_counterexample_full` in [MainTheorem.lean](AlternatingAnalytic/MainTheorem.lean). It also explicitly includes the equivalent absence of a bounded multilinear lift and failure of `ContDiffAt K ω` at every point. The underlying construction remains in [Main.lean](AlternatingAnalytic/Main.lean).

The complete factorial classification is `AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic`: precomposition is analytic for all Banach spaces exactly when k! is nonzero in K. See [FactorialClassification.lean](AlternatingAnalytic/Analysis/FactorialClassification.lean).

## Build and check

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The cache step is an optional speedup; `lake build` is the source build. The locked toolchain is Lean **4.34.0-rc2**. Mathlib is pinned to `2b73d9821d297b80d92eecc54cc09bfc263e0098` in [Deicyde/mathlib4](https://github.com/Deicyde/mathlib4/tree/2b73d9821d297b80d92eecc54cc09bfc263e0098). This commit contains the alternating-map calculus and closed-range linear-isometry results used by the proof. All transitive revisions are locked in `lake-manifest.json`.

The default target builds every module. Import `AlternatingAnalytic` for the whole library, or import `AlternatingAnalytic.MainTheorem` for the complete main theorem.

`verify.py` checks source hashes, builds the entire library and audits the axioms of every owned declaration. Its inspection program lives outside the proof library. The proof library and comparator solution use no `sorry`, `admit`, new axiom, or `native_decide`; their only logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Comparator challenge and solution

[`challenge.lean`](challenge.lean) follows the simple contradiction format of the [earlier characteristic-two challenge](https://github.com/Deicyde/alternating-analytic-counterexample/blob/main/Challenge.lean). It imports only Mathlib; the statements use Mathlib's existing definitions directly, with no custom helpers, aliases or bundles.

It contains exactly two challenge theorems:

- `AlternatingAnalyticChallenge.false_of_contDiff_omega_compContinuousLinearMapCLM`: assuming alternating precomposition is `ContDiff K ω` for every nontrivially normed field, every triple of normed spaces and every finite index type gives `False`. These universally quantified types are in universe zero, as in the original characteristic-two challenge.
- `AlternatingAnalyticChallenge.false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach`: fix any prescribed nontrivially normed `K : Type u` of prime characteristic `p` and any `k ≥ p`. Assuming degree-`k` precomposition is `ContDiff K ω` for every pair of K-Banach spaces `E, F : Type u`, with `E′ = E` and index `Fin k`, gives `False`. The field need not be complete.

These are consequences of the full constructive results. The comparator checks these two contradiction corollaries; it does not claim that they are equivalent to the constructive main theorem or factorial classification. The unchanged library retains the actual Banach witnesses, the obstruction to an equivalent ultrametric target norm, nowhere analyticity and nowhere `ContDiffAt K ω` for all finite index types of the prescribed cardinality, and the full factorial classification.

[`solution.lean`](solution.lean) repeats the two statements verbatim and proves them from the library. [`comparator.json`](comparator.json) selects both theorems and permits only `propext`, `Quot.sound` and `Classical.choice`. The challenge has two deliberate theorem placeholders, as required for a comparator exercise. They are outside the proof library and never imported by the solution or axiom audit. The library and solution contain no admitted proofs.

The default build includes both comparator modules in separate environments. `scripts/verify.py` audits the library and solution. The independent GitHub Actions comparator job uses a fresh checkout, the comparator revision matching Lean 4.34.0-rc2 and the real Linux sandbox. [The comparator receipt](verification/comparator-local.json) identifies the exact file hashes and checks for its recorded run; earlier receipts certify only their recorded versions. Local macOS runs use upstream's development launcher, which does not provide the Linux sandbox. Current build and comparator results are reported in the verification records.

Project metadata follows the version 0.4 [`formalization.yaml`](https://github.com/mathlib-initiative/formalization.yaml) format: see [`formalization.yaml`](formalization.yaml). The record distinguishes the proved scope, source provenance, integrated prior work, deliberate challenge placeholders, and separate model reviews.

## Coverage

[THEOREM_MAP.md](THEOREM_MAP.md) links the paper's proved results and complements to their Lean declarations. The construction includes the actual finite-field Ramsey obstruction, ordinary-sum projective exterior completion, sharp coefficient/support map, Laurent subfield, completed scalar extension, descent, and dense scalar restriction.

The proved complements include finite-field polarization distinctions and both sharp counterexamples, spherical and discretely valued positive results, the explicit sorted-basis lift and convergent determinant formula, norm-preserving heterogeneous dense extension, the descending-ball criterion, and the normalized multiplier example.

The paper expressly announces or leaves open several further results. Those are listed separately in the coverage audit and are not claimed here. The cited external classification of all discretely valued ultrametric Banach spaces is also outside this paper's proved scope.

## Provenance and verification

The PDF and LaTeX snapshot captured at the start of this task are preserved in `sources/`, with SHA256 hashes. During the run, the original files received an editorial revision clarifying the provenance of Theorem A; a saved diff confirms that the mathematical statements are unchanged. The source audit records both versions. Integrated existing proofs are distinguished from new work in `verification/provenance/`. This extends the characteristic-two development's approach without modifying its original repository.

`verification/` contains source hashes, exact build and exhaustive axiom logs, the semantic comparison with the main theorem, the paper coverage audit, and independent-review results. Review timeouts are retained as abstentions, never approvals. Kernel verification and model review are reported separately.

The delivered archive excludes dependency caches, local machine links, and development probes. Its validation used the locked dependency sources and an existing verified Mathlib cache. The repository contains the verified source package and the additional comparator and metadata files. The original characteristic-two repository remains separate.
