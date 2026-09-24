# Alternating precomposition in positive characteristic

Lean formalization of Jack McCarthy's **Precomposition on continuous alternating maps is not analytic in positive characteristic**.

Read the [paper](paper/charp.pdf), edit its [LaTeX source](paper/charp.tex), or consult the [theorem map](THEOREM_MAP.md) for the corresponding Lean declarations.

## Main results

For every nontrivially normed field K of prime characteristic p, including incomplete fields, and every k ≥ p, there are K-Banach spaces E and F such that degree-k alternating precomposition on E is analytic at no point. The same spaces work for every finite index type of cardinality k, and F has no equivalent ultrametric norm.

The complete statement, including the absence of a bounded multilinear lift and failure of `ContDiffAt K ω` at every point, is `AlternatingAnalytic.exists_banach_counterexample_full` in [MainTheorem.lean](AlternatingAnalytic/MainTheorem.lean).

The exact factorial criterion is `AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic` in [FactorialClassification.lean](AlternatingAnalytic/Analysis/FactorialClassification.lean): precomposition is analytic for every Banach triple over K if and only if k! is nonzero in K.

The construction includes the finite-field Ramsey obstruction, the projective exterior completion and coefficient-support estimate, and scalar extension and descent. [THEOREM_MAP.md](THEOREM_MAP.md) also records the proved complements and the explicitly excluded announced or open results.

Section 2, **Spherically complete targets: proof of Theorem A**, gives a standalone positive result: over an ultrametric field, a spherically complete ultrametric target makes precomposition analytic in every degree. Its extension, spherical-completeness, and retraction arguments follow the existing proofs in [SphericalCompleteness.lean](AlternatingAnalytic/Analysis/SphericalCompleteness.lean) and [SphericalAnalytic.lean](AlternatingAnalytic/Analysis/SphericalAnalytic.lean).

## Using the library

The project uses Lean **4.34.0-rc2** and pins Mathlib to [2b73d9821d297b80d92eecc54cc09bfc263e0098](https://github.com/Deicyde/mathlib4/tree/2b73d9821d297b80d92eecc54cc09bfc263e0098). All dependency revisions are recorded in `lake-manifest.json`.

With Lean installed through elan:

```sh
lake exe cache get
lake build AlternatingAnalytic
```

The cache download is optional. Import `AlternatingAnalytic` for the full library, or `AlternatingAnalytic.MainTheorem` for the main result.

## Challenge and solution

[`challenge.lean`](challenge.lean) imports only Mathlib and presents two contradiction theorems in the style of the [characteristic-two challenge](https://github.com/Deicyde/alternating-analytic-counterexample/blob/main/Challenge.lean):

- The global theorem refutes analyticity of precomposition for every nontrivially normed field, every triple of normed spaces, and every finite index type. These types lie in universe zero, as in the earlier challenge.
- The fixed-field theorem takes a prescribed `K : Type u` of prime characteristic p and k ≥ p. Its hypothesis `h : BanachPrecompositionAnalytic K k` asserts analytic precomposition for every pair of K-Banach spaces `E, F : Type u`, with `E′ = E` and index `Fin k`. The field need not be complete.

The named predicate is defined identically in both files. [`solution.lean`](solution.lean) proves the same statements using the library. The two deliberate challenge placeholders are separate from the proved solution. These contradiction corollaries are consequences of the stronger constructive library theorems, not replacements for them.

Challenge checks use only [Kim Morrison's comparator](https://github.com/leanprover/comparator), pinned to revision `19e111e2141cf333c7daff0f64c5f24acc91dd2e` for this Lean toolchain. [`comparator.json`](comparator.json) selects both theorems and permits only `propext`, `Quot.sound`, and `Classical.choice`.

Follow the comparator's installation instructions, then run it from this project directory:

```sh
lake env /path/to/comparator/.lake/build/bin/comparator comparator.json
```

The comparator checks the statements, their dependencies, and permitted axioms, and replays the solution with Lean's kernel. The [GitHub Actions workflow](.github/workflows/comparator.yml) uses a fresh candidate checkout and the Linux Landrun sandbox. On macOS, upstream's development launcher allows local comparator checks without that Linux sandbox.

## Manuscript and metadata

The current manuscript is in `paper/`; the original supplied PDF and LaTeX snapshots remain in `sources/`. The author disclosure credits the original Claude-assisted informal work and the later Codex/Autoform formalization. The [earlier characteristic-two development](https://github.com/Deicyde/alternating-analytic-counterexample) remains separate.

[`formalization.yaml`](formalization.yaml) records the scope, provenance, automation, and reported total cost of **USD 200**, using the ChatGPT Pro subscription price specified by the maintainer.
