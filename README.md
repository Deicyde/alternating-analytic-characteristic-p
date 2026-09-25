# Analyticity of alternating-map functors and vector bundles

Research manuscript by Jack McCarthy, with a Lean 4 / Mathlib proof library for the original operator results, finite-coordinate analytic reflection, the core laws of admissible analytic families, the invertible-shear counterexample, and canonical exterior support. The expanded manuscript also contains bundle, parameter-space and analytic-domain results whose formalization remains in progress.

Read the [paper](paper/charp.pdf), edit its [LaTeX source](paper/charp.tex), or consult the [theorem map](THEOREM_MAP.md) and [formalization roadmap](FORMALIZATION_ROADMAP.md) for the precise verification scope and next proof steps.

## Main results

For a nontrivially normed field K, let `Vec_K` be the category of normed K-spaces with bounded linear maps, and `Ban_K` its full subcategory of complete spaces. In positive characteristic, `Vec_K^∘` denotes nonarchimedean, spherically complete spaces. The alternating-map bifunctor `Alt^k` is contravariant in the first variable and covariant in the second. Analyticity of a functor means joint analyticity of its maps on morphism spaces with their operator norms.

The paper's categorical **Main Theorem** has four parts:

1. `Alt^k : Vec_K^op × Vec_K → Vec_K` is always C∞ and is analytic exactly when `k! ≠ 0` in K. The same statements hold for `Ban_K`. In characteristic p this is exactly `k < p`; in characteristic zero every finite degree works.
2. In positive characteristic, `Alt^k : Vec_K^op × Vec_K^∘ → Vec_K^∘` is analytic in every finite degree. Alternating-map spaces inherit spherical completeness from their targets. Section 2 proves this result, previously called Theorem A.
3. In every characteristic and degree, `Alt^k` preserves every analytic morphism family parametrized by an open subset of `K^d`. It therefore induces a bifunctor on analytic normed vector bundles over manifolds with open `K^d` charts, preserving operator-valued analytic bundle morphisms. Fibers may be arbitrary normed spaces. Over an incomplete field, finite algebraic dimension alone is not a substitute for these continuous coordinates.
4. For the t-adic field `K = F_p(t)`, every prime p and every `k ≥ p`, there is **no largest full analytic domain** in `Vec_K^op × Vec_K`. Two objects with analytic self-actions have a nonanalytic cross-action. The conclusion persists for finite algebraic dimensional nonarchimedean objects and for domains closed under isomorphisms in the chosen ambient category. This construction uses incomplete spaces; the complete-field and Banach versions remain open.

The operator inputs to parts (1) and (2), and the joint action with its identity/composition laws, are formalized. The bundled categorical functors and their regularity classification remain to be assembled. The finite-coordinate reflection ingredient of part (3) is formalized; its alternating-family and bundle conclusions, and part (4), remain pending.

The expanded paper also constructs the canonical admissible-family structure, proves positive parameter results for nonarchimedean `c₀` and ordinary `ℓ¹` spaces, transfers the obstruction to invertible shear families, and characterizes universal analytic reflection through closed Banach subspaces using projections onto diagonal tensor powers with exponential norm bounds. Ordinary infinite `ℓ¹` spaces over complete nonarchimedean fields show that this general reflection property is strictly stronger than the alternating-family property. A universal-target core is compatible with every analytic domain. The core admissible-family laws and shear obstruction now have checked Lean declarations; the other results in this paragraph remain pending.

The 25 September revision draws out further consequences:

- Finite-coordinate reflection preserves the ambient coefficient bounds and radius when the ambient norm is nonarchimedean.
- An explicit Banach-valued map is C∞ and a uniform limit of entire polynomials on every smaller ball, yet is nonanalytic into the closed diagonal tensor subspace at zero: every degree-n multilinear coefficient has norm at least `n!`. This example works also in characteristic zero over complete nonarchimedean fields.
- A nowhere analytic alternating pullback action becomes analytic after a bounded open quotient reparameterization by ordinary `ℓ¹`. The quotient has no local section differentiable at even one point.
- Within a fixed set of objects, full analytic domains are cliques in a compatibility graph. Every domain extends to one maximal under inclusion, and every maximal domain contains the available universal-target core objects; this does not supply a largest domain.
- Contractions determine the unique smallest subspace supporting an exterior vector, so support dimension equals contraction-matrix rank. The canonical-support equality and finite-ambient matrix formula are formalized; the general finite-support matrix transport remains pending. The alternative infinite-field obstruction and proposed large-index nonarchimedean counterexample remain unproved.

The first four consequences in this list remain to be formalized.

## Existing Lean results and current scope

The numbered **Counterexample theorem** (`thm:main`) retains the stronger constructive statement: for every prescribed nontrivially normed field K of prime characteristic p, including incomplete fields, and every `k ≥ p`, there are K-Banach spaces E and F such that degree-k alternating precomposition on E is analytic at no point. The same spaces work for every finite index type of cardinality k, and F has no equivalent ultrametric norm.

The complete statement, including the absence of a bounded multilinear lift and failure of `ContDiffAt K ω` at every point, is `AlternatingAnalytic.exists_banach_counterexample_full` in [MainTheorem.lean](AlternatingAnalytic/MainTheorem.lean).

The exact operator factorial criterion in Corollary `cor:class` is `AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic` in [FactorialClassification.lean](AlternatingAnalytic/Analysis/FactorialClassification.lean). The construction includes the finite-field Ramsey obstruction, projective exterior completion and coefficient-support estimate, and scalar extension and descent.

The operator proof for spherical targets follows [SphericalCompleteness.lean](AlternatingAnalytic/Analysis/SphericalCompleteness.lean) and [SphericalAnalytic.lean](AlternatingAnalytic/Analysis/SphericalAnalytic.lean), including extension, spherical completeness of alternating-map spaces, and a contracting retraction. The Lean operator theorem has no characteristic assumption: it applies over any ultrametric nontrivially normed field. The base and source spaces need not be complete.

The original proof-library scope is complete without admitted proofs. New checked modules prove closed-subspace reflection of analyticity for finite-coordinate parameters over arbitrary nontrivially normed fields, and the core admissible-family laws: constants, reparameterization, local gluing, composition, and the ambient graph characterization. The general reflection, family and shear-transfer results add no completeness or characteristic assumptions. The shear module also supplies the positive-characteristic Banach example at the identity. The [theorem map](THEOREM_MAP.md) distinguishes these results from the remaining full manuscript scope; the [roadmap](FORMALIZATION_ROADMAP.md) records the next dependencies. The three-statement comparator challenge is unchanged.

The weighted `c₀` target example remains a supplementary informal corollary: its given norm is not spherically complete, although alternating precomposition is analytic in every degree. Open problems now concern intrinsic criteria for universal targets and admissible parameter spaces, extensions of the split-pair category, and analytic domains over complete fields or among Banach pairs. The general largest-domain question has been answered negatively by part (4); it is no longer listed as wholly unresolved.

[CanonicalExteriorSupport.lean](AlternatingAnalytic/Algebra/CanonicalExteriorSupport.lean) identifies the contraction span as the smallest supporting subspace over every field, in arbitrary ambient dimension. It also proves the degree-zero/one cases and the contraction-matrix rank formula for finite-dimensional ambient spaces.

## Using the library

The project uses Lean **4.34.0-rc2** and pins Mathlib to [2b73d9821d297b80d92eecc54cc09bfc263e0098](https://github.com/Deicyde/mathlib4/tree/2b73d9821d297b80d92eecc54cc09bfc263e0098). All dependency revisions are recorded in `lake-manifest.json`.

With Lean installed through elan:

```sh
lake exe cache get
lake build AlternatingAnalytic
```

The cache download is optional. Import `AlternatingAnalytic` for the full library, or `AlternatingAnalytic.MainTheorem` for the full operator counterexample.

## Challenge and solution

[`challenge.lean`](challenge.lean) imports only Mathlib and presents three theorems. The first two follow the style of the [characteristic-two challenge](https://github.com/Deicyde/alternating-analytic-counterexample/blob/main/Challenge.lean):

- The global theorem refutes analyticity of precomposition for every nontrivially normed field, every triple of normed spaces, and every finite index type. These types lie in universe zero, as in the earlier challenge.
- The fixed-field theorem takes a prescribed `K : Type u` of prime characteristic p and k ≥ p. Its hypothesis `h : BanachPrecompositionAnalytic K k` asserts analytic precomposition for every pair of K-Banach spaces `E, F : Type u`, with `E′ = E` and index `Fin k`. The field need not be complete.
- The operator result underlying Main Theorem (2) asserts `ContDiff K n` for every `n : WithTop ℕ∞`, including analytic regularity, when K is ultrametric and F is ultrametric and spherically complete. E and E′ are arbitrary normed K-spaces, and the finite index type is arbitrary. All five types have independent universes; no characteristic restriction or completeness of K, E, or E′ is assumed.

The two transparent predicates `BanachPrecompositionAnalytic` and `SphericallyComplete` are defined identically in both files. The latter says that every nonempty family of pairwise-meeting closed balls has a common point, and appears as the explicit hypothesis `hF : SphericallyComplete F`. [`solution.lean`](solution.lean) proves all three statements using the library. The three deliberate challenge placeholders are separate from the proved solution. The two contradiction corollaries are consequences of the stronger constructive library theorems; the operator form of Main Theorem (2) is the separate positive result.

Challenge checks use only [Kim Morrison's comparator](https://github.com/leanprover/comparator), pinned to revision `19e111e2141cf333c7daff0f64c5f24acc91dd2e` for this Lean toolchain. [`comparator.json`](comparator.json) selects all three theorems and permits only `propext`, `Quot.sound`, and `Classical.choice`.

Follow the comparator's installation instructions, then run it from this project directory:

```sh
lake env /path/to/comparator/.lake/build/bin/comparator comparator.json
```

The comparator checks the statements, their dependencies, and permitted axioms, and replays the solution with Lean's kernel. The unchanged three-statement challenge passed a refreshed check on 25 September 2026, including acceptance of the solution by Lean's default kernel. This check does not cover the new manuscript extensions. The [GitHub Actions workflow](.github/workflows/comparator.yml) uses a fresh candidate checkout and the Linux Landrun sandbox. On macOS, upstream's development launcher allows local comparator checks without that Linux sandbox.

## Manuscript and metadata

The current manuscript is in `paper/`; the original supplied PDF and LaTeX snapshots remain in `sources/`. An independent agent audit on **25 September 2026** reviewed mathematical scope, arguments, organization and terminology. The revision keeps the spherical-target proof in Section 2, puts the categorical-domain argument before the tensor criterion, moves exterior preliminaries next to their use, consolidates the finite-dimensional completeness argument, and explains the completion step in the rigid-source construction. This audit is informal review, not kernel verification or human expert review. The author disclosure credits the original Claude-assisted informal work and the later Codex/Autoform formalization. The [earlier characteristic-two development](https://github.com/Deicyde/alternating-analytic-counterexample) remains separate.

[`formalization.yaml`](formalization.yaml) records the scope, provenance, automation, and reported total cost of **USD 200**, using the ChatGPT Pro subscription price specified by the maintainer.
