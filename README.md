# Alternating precomposition in positive characteristic

Lean formalization of Jack McCarthy's **Precomposition on continuous alternating maps is not analytic in positive characteristic**.

Read the [paper](paper/charp.pdf), edit its [LaTeX source](paper/charp.tex), or consult the [theorem map](THEOREM_MAP.md) for the corresponding Lean declarations.

## Main results

The paper leads with one categorical **Main Theorem** in two parts. For a nontrivially normed field K, let `Vec_K` be the category of normed K-spaces with bounded linear maps, allowing ordinary norms that need not be ultrametric. Let `Ban_K` be its full subcategory of complete spaces. When K has positive characteristic, let `Vec_K^∘` be its full subcategory of ultrametric, spherically complete spaces. For every integer k ≥ 0, the bifunctor `Alt^k` is contravariant in its first variable and covariant in its second; its action is `(u, v) ↦ [m ↦ v ∘ m ∘ (u, …, u)]`. Regularity means joint regularity on each pair of morphism spaces with their operator norms.

1. `Alt^k : Vec_K^op × Vec_K → Vec_K` is always C∞ and is analytic if and only if `k! ≠ 0` in K. The same statements hold for `Alt^k : Ban_K^op × Ban_K → Ban_K`.
2. When K has positive characteristic, `Alt^k : Vec_K^op × Vec_K^∘ → Vec_K^∘` is analytic in every finite degree. The target category records that alternating-map spaces inherit spherical completeness from the target.

Neither part assumes completeness of K. In characteristic zero, part (1) already gives analyticity in every finite degree for all normed spaces. Part (2) was previously called Theorem A.

The underlying operator results are formalized in Lean. Both parts of the categorical Main Theorem follow mathematically from these results, bounded bilinear postcomposition, and the closure properties of alternating-map spaces; the categorical functors and joint morphism actions are not separate Lean declarations.

The introduction explains the vector-bundle motivation: a multifunctor that is jointly Cⁿ on morphism spaces carries transition maps to a new Cⁿ bundle cocycle. It treats contravariant arguments using inverse transitions and applies the construction to alternating-map bundles and differential forms. This is explanatory mathematical motivation, with no additional Lean bundle or functor declarations.

The numbered **Counterexample theorem** (`thm:main`) retains the stronger constructive statement: for every nontrivially normed field K of prime characteristic p, including incomplete fields, and every k ≥ p, there are K-Banach spaces E and F such that degree-k alternating precomposition on E is analytic at no point. The same spaces work for every finite index type of cardinality k, and F has no equivalent ultrametric norm.

The complete statement, including the absence of a bounded multilinear lift and failure of `ContDiffAt K ω` at every point, is `AlternatingAnalytic.exists_banach_counterexample_full` in [MainTheorem.lean](AlternatingAnalytic/MainTheorem.lean).

The exact operator factorial criterion in Corollary `cor:class` is `AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic` in [FactorialClassification.lean](AlternatingAnalytic/Analysis/FactorialClassification.lean): precomposition is analytic for every Banach triple over K if and only if k! is nonzero in K.

The construction includes the finite-field Ramsey obstruction, the projective exterior completion and coefficient-support estimate, and scalar extension and descent. [THEOREM_MAP.md](THEOREM_MAP.md) also records the proved complements and the explicitly excluded announced or open results.

Section 2, **Spherically complete targets**, proves part (2) of the Main Theorem. It begins with the broader operator result: over any ultrametric field, a spherically complete ultrametric target makes precomposition analytic in every degree. The Lean result retains this scope without a characteristic assumption; the positive-characteristic hypothesis in Main Theorem (2) supplies ultrametricity of K. Its extension, spherical-completeness, and retraction arguments follow the existing proofs in [SphericalCompleteness.lean](AlternatingAnalytic/Analysis/SphericalCompleteness.lean) and [SphericalAnalytic.lean](AlternatingAnalytic/Analysis/SphericalAnalytic.lean). Bounded bilinear postcomposition and spherical completeness of alternating-map spaces complete the categorical statement.

The complements include a weighted `c₀` example whose given norm is not spherically complete, although alternating precomposition is analytic in every degree. The open problems ask for an intrinsic necessary and sufficient condition on the target. This new example is an informal corollary, not a separate Lean declaration.

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

The comparator checks the statements, their dependencies, and permitted axioms, and replays the solution with Lean's kernel. The [GitHub Actions workflow](.github/workflows/comparator.yml) uses a fresh candidate checkout and the Linux Landrun sandbox. On macOS, upstream's development launcher allows local comparator checks without that Linux sandbox.

## Manuscript and metadata

The current manuscript is in `paper/`; the original supplied PDF and LaTeX snapshots remain in `sources/`. The author disclosure credits the original Claude-assisted informal work and the later Codex/Autoform formalization. The [earlier characteristic-two development](https://github.com/Deicyde/alternating-analytic-counterexample) remains separate.

[`formalization.yaml`](formalization.yaml) records the scope, provenance, automation, and reported total cost of **USD 200**, using the ChatGPT Pro subscription price specified by the maintainer.
