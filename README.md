# Analyticity of alternating-map functors and vector bundles

> **Formalization checkpoint: 46 accepted extension nodes.** All four categorical main results have Lean declarations in the stated scopes. Whole-project builds cover all library modules.

Research manuscript by Jack McCarthy, with a Lean 4 / Mathlib proof library.
The central distinction is between analyticity on entire operator spaces and preservation of analytic families: alternating maps preserve finite-coordinate analytic families in every characteristic and degree, even when the operator action is nonanalytic.

Read the [paper](paper/charp.pdf), edit its [LaTeX source](paper/charp.tex), or consult the [theorem map](THEOREM_MAP.md) and [formalization roadmap](FORMALIZATION_ROADMAP.md) for exact statements and verification scope.

## Categorical main results

For a nontrivially normed field K, let `Vec_K` be the category of normed K-spaces with bounded linear maps, and `Ban_K` its full subcategory of complete spaces.
In positive characteristic, `Vec_K^∘` denotes nonarchimedean, spherically complete spaces.
The alternating-map bifunctor `Alt^k` is contravariant in its first variable and covariant in its second; functor analyticity means joint analyticity on morphism spaces with their operator norms.

1. **Sharp degree criterion — formalized.** `Alt^k : Vec_K^op × Vec_K → Vec_K` is always C∞ and is analytic exactly when `k! ≠ 0` in K. The same holds on `Ban_K`. In characteristic p the analytic range is `k < p`; in characteristic zero it includes every finite degree.
2. **Spherical targets — formalized.** In positive characteristic, `Alt^k : Vec_K^op × Vec_K^∘ → Vec_K^∘` is analytic in every finite degree. Alternating-map spaces inherit spherical completeness from their targets. Section 2 proves this result, formerly called Theorem A.
3. **Analytic families and bundles — formalized.** In every characteristic and degree, `Alt^k` preserves analytic morphism families on open subsets of `K^d`. Over each fixed analytic base with open coordinate charts and supplied continuous coordinates `P ≃L[K] (Fin d → K)`, it induces the actual alternating bifunctor on analytic normed vector bundles and operator-valued analytic bundle morphisms. The model fibers may be arbitrary normed spaces; neither K nor the fibers must be complete.
4. **No largest full analytic domain — formalized.** For the t-adic field `K = F_p(t)`, every prime p and every `k ≥ p`, no largest full analytic domain exists in `Vec_K^op × Vec_K`. The paper constructs two objects with analytic self-actions and a nonanalytic cross-action. The conclusion persists for finite algebraic dimensional nonarchimedean objects and domains closed under isomorphisms inside the chosen ambient category. The scalar field is incomplete; the corresponding complete-field and Banach questions remain open. The Lean theorem retains every radius `0 < r < 1` and uses the actual category of universe-zero normed spaces.

For part (3), the library supplies an actual `ContMDiffVectorBundle ω` witness on Mathlib’s existing alternating-bundle topology, exact transition and morphism formulas, functor laws, and transport through analytically compatible bundle presentations.
Every coordinate dimension and degree, including zero, is allowed. Actual fibers retain their topological/normable structures.
Over an incomplete field, algebraic finite-dimensionality alone does not replace the continuous-coordinate hypothesis on the base.

## Operator results and positive cases

The constructive **Counterexample theorem** is stronger than the selected challenge corollaries.
For every prescribed nontrivially normed field K of prime characteristic p, including incomplete K, and every `k ≥ p`, it gives K-Banach spaces E and F with nowhere-analytic degree-k alternating precomposition on E.
The same witnesses work for every finite index type of cardinality k; the theorem also excludes a bounded multilinear lift and `ContDiffAt K ω` at every point. F has no equivalent nonarchimedean norm.

For an operator `f : E →L[K] E′`, write `Q(f)(m) = m ∘ (f,…,f)`, so Q takes alternating maps on E′ to alternating maps on E, with value target F.
The following positive results are formalized:

| Hypothesis | Conclusion and scope |
|---|---|
| `k! ≠ 0` in K | Q has a finite power series at every operator; the spaces need not be complete. |
| K nonarchimedean; F nonarchimedean and spherically complete | Q is `ContDiff K n` for every regularity order n, including analytic regularity. E and E′ are arbitrary normed spaces; K need not be complete. |
| E has a finite basis with continuous coordinate functionals | An explicit continuous k-multilinear lift has diagonal Q; Q is continuously polynomial and analytic everywhere. K, E′ and F need not be complete. |
| E′ has a finite basis with continuous coordinate functionals | A separate determinant construction gives the same lift and regularity conclusions, with arbitrary normed E and F. K need not be complete. |
| K complete; either E or E′ finite-dimensional | Continuous coordinates follow, giving polynomiality and analyticity everywhere in every degree. F and the other input may be arbitrary normed spaces. |

The two finite-coordinate constructions include degree zero and degrees above the coordinate dimension, with explicit real norm bounds and no division by `k!` in K.
These are hypotheses on the **operator inputs E or E′**. The separate reduction for a finite-dimensional **value target F** remains to be formalized.

## Principal Lean entry points

Names below are in namespace `AlternatingAnalytic` unless indicated otherwise. The [theorem map](THEOREM_MAP.md) records supporting declarations and their precise hypotheses.

| Result | Module and public entry point |
|---|---|
| Prescribed-field Banach counterexample | [MainTheorem.lean](AlternatingAnalytic/MainTheorem.lean): `exists_banach_counterexample_full` |
| Actual categorical functors and Main Theorem (1)–(2) | [AlternatingRegularity.lean](AlternatingAnalytic/Category/AlternatingRegularity.lean): `alternatingFunctor_main`, `alternatingSphericalFunctor_main`, `alternatingSphericalFunctor_main_of_charP` |
| Finite-coordinate analytic families | [FiniteCoordinateFamilies.lean](AlternatingAnalytic/Analysis/FiniteCoordinateFamilies.lean): `finite_coordinate_analytic_families` |
| Actual analytic alternating bundle | [AnalyticAlternatingBundle.lean](AlternatingAnalytic/Geometry/AnalyticAlternatingBundle.lean): `analyticAlternatingBundle_of_finiteCoordinates` |
| Operator-valued bundle morphisms and actual bifunctor | [AnalyticAlternatingBundleMorphism.lean](AlternatingAnalytic/Geometry/AnalyticAlternatingBundleMorphism.lean): `analyticAlternatingBundleMorphism_of_finiteCoordinates`; [AnalyticAlternatingBundleFunctor.lean](AlternatingAnalytic/Geometry/AnalyticAlternatingBundleFunctor.lean): `alternatingBundleFunctor` |
| Shared finite-word coefficient grouping | [FiniteWordGrouping.lean](AlternatingAnalytic/Algebra/FiniteWordGrouping.lean): `FiniteWord.finite_word_grouping_spec`, `FiniteWord.finite_diagonal_grouping` |
| Ordinary ℓ¹ homogeneous diagonal lift | [L1PolynomialLift.lean](AlternatingAnalytic/Analysis/L1PolynomialLift.lean): `L1PolynomialLift.exists_l1_diagonal_lift` |
| Fixed-degree reflection along ordinary ℓ¹ families | [L1FixedDegreeReflection.lean](AlternatingAnalytic/Analysis/L1FixedDegreeReflection.lean): `analyticOn_comp_of_l1_fixed_degree`, `exists_l1_completion_diagonal_lift` |
| Ordinary ℓ¹ analytic alternating families and bounded retracts | [L1Families.lean](AlternatingAnalytic/Analysis/L1Families.lean): `l1_family_admissibility`, `isAdmissibleOn_of_l1_of_isOpen`, `isAdmissibleOn_of_l1_retract_of_isOpen` |
| Quotient-parameter failure and absence of ordinary ℓ¹ retracts | [QuotientParameterCounterexample.lean](AlternatingAnalytic/Analysis/QuotientParameterCounterexample.lean): `exists_quotient_parameter_counterexample`, `no_l1_retract_of_nowhere_analytic_Q`, `not_differentiableWithinAt_section_of_isOpen` |
| Ordinary ℓ¹ unit-ball quotient of Banach spaces | [L1BanachQuotient.lean](AlternatingAnalytic/Analysis/L1BanachQuotient.lean): `unitBall_l1_quotient`, `unitBallL1Quotient_exists_single_lt`, `unitBallL1Quotient_ball_subset` |
| Supremum-norm c₀ analytic alternating families | [CZeroFamilies.lean](AlternatingAnalytic/Analysis/CZeroFamilies.lean): `c0_analytic_family_admissibility`, `isAdmissibleOn_of_c0_of_isOpen`, `isAdmissibleOn_of_c0_equiv_of_isOpen` |
| Supremum-norm c₀ reflection on the same analytic ball | [CZeroReflection.lean](AlternatingAnalytic/Analysis/CZeroReflection.lean): `c0_exists_hasFPowerSeriesOnBall_linearIsometry`, `c0_analyticOn_linearIsometry`, `c0_analyticOn_linearIsometry_of_equiv` |
| Supremum-norm c₀ homogeneous diagonal lifting | [CZeroCoefficients.lean](AlternatingAnalytic/Analysis/CZeroCoefficients.lean): `CZero.homogeneous_diagonal_lifting`, `CZero.norm_groupedCoefficient_le` |
| Supremum-norm c₀ coordinates and bounded coefficient arrays | [CZeroCoordinateBasics.lean](AlternatingAnalytic/Analysis/CZeroCoordinateBasics.lean): `CZero.coordinate_calculus`; [CZeroCoordinates.lean](AlternatingAnalytic/Analysis/CZeroCoordinates.lean): `CZero.boundedArrayMultilinearMap_spec`, `CZero.boundedArrayMultilinearMap_zero` |
| Ordinary ℓ¹ bounded coefficient arrays | [L1Coordinates.lean](AlternatingAnalytic/Analysis/L1Coordinates.lean): `L1Coordinates.exists_l1_multilinear_of_bounded_coefficients` |
| Local analytic factorization through ordinary ℓ¹ | [L1AnalyticFactorization.lean](AlternatingAnalytic/Analysis/L1AnalyticFactorization.lean): `L1Coordinates.l1_word_factorization`, `L1Coordinates.exists_analyticAt_l1_factorization` |
| Finite-coordinate operator inputs | [FiniteCoordinateDomain.lean](AlternatingAnalytic/Analysis/FiniteCoordinateDomain.lean): `finiteCoordinateDomain`; [FiniteCoordinateCodomain.lean](AlternatingAnalytic/Analysis/FiniteCoordinateCodomain.lean): `finiteCoordinateCodomain` |
| Finite-dimensional inputs over complete K | [FiniteDimensionalPositive.lean](AlternatingAnalytic/Analysis/FiniteDimensionalPositive.lean): `finiteDimensional_positive` |
| Universal-target core and split analytic domains | [AnalyticDomains.lean](AlternatingAnalytic/Category/AnalyticDomains.lean): `universalTarget_core`, `product_isAnalyticDomain_iff`, `splitPairs_incoming_analytic` |
| Incompatible analytic self-actions in every degree `k ≥ p` | [PaddedIncompatiblePairs.lean](AlternatingAnalytic/Analysis/PaddedIncompatiblePairs.lean): `DeterminantPair.Padding.realized_pairs_for_every_degree` |
| No largest full analytic domain, with all four ambient/replete variants | [NoLargestAnalyticDomain.lean](AlternatingAnalytic/Category/NoLargestAnalyticDomain.lean): `DeterminantPair.Padding.no_largest_full_analytic_domain` |
| Split-domain limit and completed-action comparison | [NoLargestAnalyticDomain.lean](AlternatingAnalytic/Category/NoLargestAnalyticDomain.lean): `DeterminantPair.Padding.no_largest_domain_limits`; [PaddedCompletionAnalytic.lean](AlternatingAnalytic/Analysis/PaddedCompletionAnalytic.lean): `DeterminantPair.Padding.concrete_completed_analytic_action_and_lift` |

Further checked results include the core admissible-family laws, invertible-shear obstruction, nonarchimedean radius preservation, canonical exterior support, exact-norm dense scalar extension, and the concrete scalar, determinant and padded constructions supporting part (4).
Main Theorem (4) is collected by `DeterminantPair.Padding.no_largest_full_analytic_domain` in [NoLargestAnalyticDomain.lean](AlternatingAnalytic/Category/NoLargestAnalyticDomain.lean). Its four nonexistence clauses cover arbitrary full domains and isomorphism-closed domains, both in the full normed pair category and inside the finite-dimensional nonarchimedean ambient category. The relative closure stays inside that chosen ambient.

The limits theorem also shows that the constructed rigid object cannot be adjoined to the full split-pair domain. After passing to the explicitly identified completions over `L = F_p((t))`, the corresponding joint action is analytic; an explicit p-linear product of constant coefficients lifts the old determinant coordinate after inclusion into L. This lift is p-linear even when the alternating degree is `p+n`. These particular completion results do not settle the complete-field or Banach largest-domain questions.

The ordinary sum-norm ℓ¹ results are formalized: Lemma 28 (`fam:lem:l1-polynomial`), Theorem 29 (`fam:thm:l1-families`) and Corollary 30 (`fam:cor:l1-families`). In every characteristic and degree, analytic joint morphism families on `ℓ¹(I,K)` or any supplied bounded linear retract are admissible for the alternating-map construction. Only the final value target F′ must be complete; K, E, E′, F and the retract parameter P may be incomplete. Indices are arbitrary, including empty and uncountable sets, and degree zero is included. The open-domain wrappers retain an open parameter set; neighborhood-analytic forms apply on arbitrary sets. The inclusion and retraction are bounded linear maps whose composition is the identity, with no norm-one or isometry condition.

The proof library supplies the coefficient-array sum, finite-word grouping and local word factorization. The homogeneous lift has the same diagonal as its ambient representative B and norm at most `(d! : ℝ) · ‖B‖`, for the same lift. Fixed-degree reflection retains W closed in Banach Z and merely normed H, with no analyticity or continuity premise on the represented map P. Its quantitative lift has bound `(d! : ℝ) · ‖B‖ · ‖T‖^d`, depending only on the fixed outer degree. The auxiliary analytic map in the local factorization lands in **uncompleted K-valued ℓ¹**; the bounded synthesis map lands in the completion of H.

These results establish analytic morphism-family admissibility. Actual alternating bundles over ordinary ℓ¹ or retract bases remain a separate formalization task, as do tensor results.

The supremum-norm c₀ foundation is also formalized on genuine `C₀(I,K)` for arbitrary discrete I, with no completeness or nonarchimedean assumption on K. It supplies coordinates, bounded evaluations, contractive finite truncations, truncation convergence and finite-support density. For complete nonarchimedean W, every bounded coefficient array defines one continuous multilinear map with its unconditional sum formula, operator norm bound, coordinate values and finite-support/truncation formulas. All degrees, including zero, and empty or uncountable indices are included. The homogeneous lifting step is also formalized: for nonarchimedean normed Z and a submodule W complete in its inherited norm, every continuous n-multilinear p whose diagonal lies in W admits one continuous W-valued q with exactly that diagonal and `‖q‖ ≤ ‖p‖`. K and Z may be incomplete; no separate nonarchimedean assumption on K or closedness premise on W is added. Every degree, including zero, and every discrete index set are covered. The c₀ reflection theorem is also formalized. For a linear isometry from complete W into nonarchimedean normed Z, an ambient power series on a supplied ball lifts to one W-valued series with coefficient norms no larger, exact included coefficient diagonals, intrinsic radius at least the original radius, and the same represented ball—including infinite radius. K and Z may be incomplete; no separate nonarchimedean assumption on K is added. This preserves the represented ball without asserting equality of intrinsic radii. Pointwise, neighborhood and open-domain analytic wrappers are available, together with analyticity transport along continuous linear parameter equivalences and explicit extension wrappers for functions on open subtypes. The c₀ alternating-family corollary is formalized as well: analytic joint morphism families on C₀(I,K), or on any parameter space supplied with a continuous linear equivalence to it, are admissible in every degree. Only the final value target F′ must be complete and nonarchimedean; K, E, E′, F and P may be incomplete, with no separate nonarchimedean assumption on K or the other fibers. The theorem includes pointwise, neighborhood and open-domain forms and the needed operator-target completeness and nonarchimedean properties. Parameter transport uses an isomorphism; actual infinite-dimensional bundle and tensor constructions remain separate tasks.

The generic ordinary ℓ¹ quotient construction is formalized. Over complete K, every Banach H is the image of its closed-unit-ball-indexed ordinary ℓ¹ space under an open continuous linear surjection q with `‖q‖ ≤ 1`. For any `c : K` with `1 < ‖c‖`, every h has a one-coordinate lift bounded by `‖c‖ · ‖h‖`, strictly so when h is nonzero; `ball(q x, ε / ‖c‖)` lies in the image of `ball(x, ε)` for every positive ε. The theorem also records actual summability and exact coordinate values. Its helper construction needs complete H but allows incomplete K; the collected Banach-source statement retains complete K. The quotient-parameter counterexample and non-retract consequence are also formalized. For complete K of positive characteristic p and k ≥ p, the same Banach witnesses E,F and quotient onto H = E →L[K] E have an everywhere-analytic pullback Q ∘ q while Q is nowhere analytic. Every local section on an open set fails to be Fréchet differentiable at every point of that set; this does not exclude continuous sections. This same H is not a bounded linear retract of ordinary ℓ¹(I,K) for any index type I, whose universe is independent of the witness universe. The actual norms are retained; no nonarchimedean assumption is added.

## Verification and remaining scope

The original operator proof library is complete for its stated scope, without admitted proofs. Forty-six extension nodes have passed the shared build/kernel/axiom gates and clean independent AI jury review.
Whole-project builds include every library module through recursive library globs. The accepted root reaches all 181 project modules, including the ordinary ℓ¹ and c₀ family constructions and the quotient counterexample. Each worker-added root import was included in its original accepted gate.
The expanded manuscript is still partly formalized. The full **71-node extension plan** remains the implementation objective, including proved remarks and consequences.

Remaining work includes set-sized maximal analytic domains and any separately stated normable-category packaging; tensor reflection, optimal projections and separation examples; finite-dimensional value-target reduction; the weighted nonspherical target; other positive bundle regimes and the general Cⁿ multifunctor construction; and the remaining family and support-transport results.
The [roadmap](FORMALIZATION_ROADMAP.md) and [pending theorem inventory](THEOREM_MAP.md#new-manuscript-results-awaiting-formalization) distinguish these from mathematical open problems and explicitly unproved proposals.
No human expert review or complete formalization of the expanded manuscript is claimed.

## Using the library

The project uses Lean **4.34.0-rc2** and Mathlib revision [2b73d9821d297b80d92eecc54cc09bfc263e0098](https://github.com/Deicyde/mathlib4/tree/2b73d9821d297b80d92eecc54cc09bfc263e0098).
All dependency revisions are recorded in [lake-manifest.json](lake-manifest.json).
With Lean installed through elan:

```sh
lake exe cache get
lake build AlternatingAnalytic
```

The cache download is optional. Import the module for the desired result from the table above, or `AlternatingAnalytic.MainTheorem` for the complete operator counterexample.
The root import `AlternatingAnalytic` exposes the accepted library, including the no-largest-domain construction and the full ordinary ℓ¹ family/retract chain. Import `AlternatingAnalytic.Analysis.L1Coordinates` for the coefficient foundation, `AlternatingAnalytic.Analysis.L1AnalyticFactorization` for the local factorization, `AlternatingAnalytic.Analysis.L1PolynomialLift` for the homogeneous lift, or `AlternatingAnalytic.Analysis.L1FixedDegreeReflection` for fixed-degree reflection.

## Challenge and solution

[`challenge.lean`](challenge.lean) presents five theorems; [`solution.lean`](solution.lean) supplies their library proofs. Alongside Mathlib, the challenge imports `RationalLaurentScalars` and `AnalyticDomains` for the concrete normed field and actual categorical analytic-domain predicate. This boundary includes their established supporting positive results; it does not import the final no-largest theorem or the determinant/padded obstruction modules.
The first two follow the style of the [characteristic-two challenge](https://github.com/Deicyde/alternating-analytic-counterexample/blob/main/Challenge.lean):

1. Refute universal analytic precomposition over every nontrivially normed field, every triple of normed spaces, and every finite index type, with types in universe zero.
2. For prescribed `K : Type u` of prime characteristic p and `k ≥ p`, refute `BanachPrecompositionAnalytic K k`: analytic precomposition for every pair of K-Banach spaces `E, F : Type u`, with `E′ = E` and index `Fin k`. K need not be complete.
3. Prove `ContDiff K n` for every `n : WithTop ℕ∞` when K and F are nonarchimedean and F is spherically complete. E and E′ are arbitrary normed spaces, the finite index type is arbitrary, and all five types have independent universes. There is no characteristic restriction or completeness assumption on K, E or E′.
4. Prove the actual `ContMDiffVectorBundle ω` witness over a self-model analytic base with supplied `P ≃L[K] (Fin d → K)`, arbitrary normed model fibers and existing topological actual fibers. All d and k, including zero, are allowed, without completeness, characteristic or factorial assumptions.
5. Prove that no largest full analytic domain exists over `RationalField (ZMod p) r`, for every prime p, every `k ≥ p` and every `0 < r < 1`. The field and normed object carriers lie in universe zero. This selects the principal unrestricted nonexistence conclusion; the collected witnesses, isomorphism-closed and finite-ambient variants, and completion clauses remain separate library results.

The original transparent predicates `BanachPrecompositionAnalytic` and `SphericallyComplete` are unchanged and identical in both files; the latter is the closed-ball intersection property. The new transparent `HasLargestFullAnalyticDomain K k` states that some full analytic object property is greatest under inclusion, using the actual `IsAlternatingAnalyticDomain` predicate. It assumes no incompatible witness or obstruction.
The five deliberate challenge placeholders are separate from the proved solution. The first two statements are corollaries of stronger constructive library results.

Challenge validation uses only [Kim Morrison’s comparator](https://github.com/leanprover/comparator), pinned to `19e111e2141cf333c7daff0f64c5f24acc91dd2e`.
[`comparator.json`](comparator.json) selects all five statements and permits only `propext`, `Quot.sound`, and `Classical.choice`.
After following the comparator’s installation instructions, run:

```sh
lake env /path/to/comparator/.lake/build/bin/comparator comparator.json
```

All five selected statements passed local comparator checking and Lean default-kernel replay on 26 September 2026. This publication reuses that successful receipt: the challenge, solution, configuration, dependency pins and all 126 project modules in the solution import closure are byte-for-byte unchanged. No new comparator run was needed for this batch. The first four signatures and the original two transparent predicates remain unchanged.
The checked selected scope includes the bundle witness and the principal unrestricted no-largest conclusion. It does not certify the separate bundle category, morphism construction, final bifunctor, the other collected Main Theorem (4) clauses or all manuscript extensions.
The macOS check used upstream’s development launcher. The [GitHub workflow](.github/workflows/comparator.yml) uses the Linux Landrun sandbox; the recorded hosted run did not start because of an account billing/spending restriction, so no hosted CI success is claimed.

## Manuscript and provenance

The current manuscript is in [paper/](paper/); original PDF and LaTeX snapshots remain in [sources/](sources/).
The disclosure credits the original Claude-assisted informal result and write-up separately from the later Codex/Autoform formalization and editorial work. Codex is the persisted proof backend.
Informal manuscript audits are distinct from kernel verification and independent proof review. The [earlier characteristic-two development](https://github.com/Deicyde/alternating-analytic-counterexample) remains separate.

[`formalization.yaml`](formalization.yaml), using schema **0.4** (`version: 'v0.4'`), records scope, provenance, automation and the reported total cost of **USD 200**, using the ChatGPT Pro subscription price specified by the maintainer.
