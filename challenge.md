# Claim ledger for 'Alternating bundles and analytic descent'

Ledger created 2026-10-08 at library commit f85751e; all claims formalized on branch `ledger-proofs` the same day. Paper: Jack McCarthy, *Alternating bundles and analytic descent*, October 2026, 64 pp.

**What this is.** Every numbered claim of the paper has its own Lean file under `Challenges/`. Each file states the claim with `sorry`, under the namespace `AlternatingAnalyticChallenge.<ID>`. The module docstring gives the paper reference and page, the informal statement, and "Formalization notes" that list every way the Lean statement differs from the paper. When the library proves the claim, `Solutions/<ID>.lean` proves the same statement from library declarations, with identical definitions and statements character for character, and `Challenges/<ID>.json` is a comparator config for that pair. Multi-part results have one theorem per part.

**Status legend.**
- **proved**: `Solutions/<ID>.lean` compiles with no `sorry` and proves the identical statement. Only `propext`, `Quot.sound` and `Classical.choice` are allowed.
- **partially_proved**: the library proves a special case, a weaker form, or some parts but not all. There is no solution file.
- **not_proved**: the library has no Lean proof of the claim.
- **statement_pending**: no faithful formal statement yet.

No claim currently has the last three statuses; they are kept for future additions to the paper.

**How to check.**
- Build everything: `lake build` (the `Challenges` and `Solutions` targets are in `defaultTargets`). Compile one claim: `lake env lean Challenges/<ID>.lean` (only `sorry` warnings expected), then `lake env lean Solutions/<ID>.lean` (must have no `sorry`). On a machine with little memory, `scripts/run_lean.py` compiles files through a four-slot lock: `python3 -I scripts/run_lean.py Challenges/<ID>.lean Solutions/<ID>.lean`.
- Run the comparator on a pair: `lake env /path/to/comparator/.lake/build/bin/comparator Challenges/<ID>.json`. The `Challenges` and `Solutions` targets are declared in `lakefile.toml`, so the comparator can build the two modules of a pair.
- Check one claim end to end: `python3 -I scripts/check_claim.py <ID>`. It confirms that the challenge file is unchanged since the ledger was created (git tag `ledger-base`), builds the pair, checks that every theorem uses only the three standard axioms, and checks that the challenge and solution statements print identically under `pp.all`.

## Summary

Total: **76 claims**, in 76 challenge files. **All 76 are proved**: each has a solution file that proves the identical statement with only the three standard axioms, and a `.json` comparator config. 45 were proved by the library as it stood at f85751e; the other 31 were formalized on 2026-10-08, adding about 13,400 lines in 97 new library files.

| Section | Claims | proved at ledger creation | proved on 2026-10-08 |
|---|---:|---:|---:|
| 2-3 (constructions, descent) | 5 | 0 | 5 |
| 4 (positive results, bundle theorem) | 7 | 6 | 1 |
| 5 (representation, duality tests) | 2 | 0 | 2 |
| 6 (obstructions, classification) | 7 | 3 | 4 |
| 7 (differential calculus) | 2 | 0 | 2 |
| 9 (fibers) | 1 | 0 | 1 |
| A-B (algebra, finite fields) | 16 | 16 | 0 |
| C (Laurent obstruction) | 7 | 4 | 3 |
| D-E (base change, target norm) | 12 | 10 | 2 |
| F (scalar counterexample) | 5 | 0 | 5 |
| G (tensor reflection) | 4 | 2 | 2 |
| H (analytic domains) | 5 | 4 | 1 |
| I (countable type, c0, weighted norm) | 3 | 0 | 3 |
| **Total** | **76** | **45** | **31** |

In the tables below, file names are relative to the repository root, and "—" means no file. Unless a row says otherwise, the degree is `Fin k`.

## Sections 2-3

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Thm2_1 | Theorem 2.1 (pp. 4-5) | Fiberwise application lifts C^n mixed-variance functors to functors on C^n bundle categories | proved | [Challenges/Thm2_1.lean](Challenges/Thm2_1.lean) | [Solutions/Thm2_1.lean](Solutions/Thm2_1.lean) | `bundleLifting`, `bundleLifting_familywise` (Bundle/FunctorLifting/) | Statement written during formalization (2026-10-08), not part of the original ledger: review it. Variables grouped by variance (contravariant first); the functor uses the canonical trivializations, so it exists on the nose; independence of the cover is not stated; two instances on `VectorBundleCore.Fiber` are declared. |
| Prop2_2 | Proposition 2.2 (p. 6) | The ambient action g∘m∘(f,…,f) is a bounded (k+1)-linear diagonal, analytic, with values in Alt^k | proved | [Challenges/Prop2_2.lean](Challenges/Prop2_2.lean) | [Solutions/Prop2_2.lean](Solutions/Prop2_2.lean) | `exists_ambientMultilinearAction_rep`, `contDiff_ambientMultilinearAction` (Descent/AmbientAction.lean) | k = 0 allowed. The norm bound ‖H‖ ≤ 1 is not stated. Part 4 phrases the closed subspace via the range of `toContinuousMultilinearMap`. |
| Thm3_1 | Theorem 3.1 (p. 7) | Coefficient descent: diagonals lie in j(W); f analytic iff the coefficients lift with a geometric bound | proved | [Challenges/Thm3_1.lean](Challenges/Thm3_1.lean) | [Solutions/Thm3_1.lean](Solutions/Thm3_1.lean) | `CoefficientCriterion.analyticAt_iff` (Descent/CoefficientCriterion.lean) | Open set U dropped. Coefficients as a `FormalMultilinearSeries`, bounds as `BddAbove`, convergence as `HasSum`. |
| Lem3_2 | Lemma 3.2 (p. 8) | f is C^n on open U iff j∘f is C^n | proved | [Challenges/Lem3_2.lean](Challenges/Lem3_2.lean) | [Solutions/Lem3_2.lean](Solutions/Lem3_2.lean) | `contDiffOn_iff_comp_linearIsometry` (Descent/SmoothDescentOn.lean) | Open-set `ContDiffOn` version, n : ℕ∞, no completeness. |
| Prop3_3 | Proposition 3.3 (p. 8) | One lift, every base point: analytic somewhere ⟺ bounded lift ⟺ polynomial everywhere; dichotomy for A^k | proved | [Challenges/Prop3_3.lean](Challenges/Prop3_3.lean) | [Solutions/Prop3_3.lean](Solutions/Prop3_3.lean) | `OneLift.tfae`, `OneLift.precomposition_polynomial_or_nowhereAnalytic` (Descent/OneLift.lean) | (3) as `HasFiniteFPowerSeriesOnBall` of infinite radius. k = 0 allowed (trivial). |


## Section 4

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Prop4_1 | Proposition 4.1 (pp. 8-9) | A bounded retraction Alt→Mult gives a lift of norm ≤ ‖ρ‖; lifts exist if k! ≠ 0 or finite coordinates | proved | [Challenges/Prop4_1.lean](Challenges/Prop4_1.lean) | [Solutions/Prop4_1.lean](Solutions/Prop4_1.lean) | `contractingRetractionLift` (SortedBasisLift.lean), `altProj` (FactorialInvertible.lean), `finiteCoordinateDomainLift`, `finiteCoordinateCodomainLift` | Norm bound stated pointwise. Parts (1)-(2) are existence only. |
| Thm4_2 | Theorem 4.2 (pp. 9-10) | Spherically complete targets: Alt^k is ultrametric, spherically complete and retracts; A^k is a continuous polynomial | proved | [Challenges/Thm4_2.lean](Challenges/Thm4_2.lean) | [Solutions/Thm4_2.lean](Solutions/Thm4_2.lean) | `sphericallyCompleteSpace_continuousAlternatingMap`, `exists_contracting_retraction_toContinuousMultilinearMap`, `hasBoundedLift_of_sphericallyComplete` (SphericalAnalytic.lean) | 4 parts. IsContinuousPolynomial is defined in the file. [^thm42] |
| Cor4_3 | Corollary 4.3 (p. 10) | Discrete value group: equivalent nonarchimedean Banach targets make A^k analytic | proved | [Challenges/Cor4_3.lean](Challenges/Cor4_3.lean) | [Solutions/Cor4_3.lean](Solutions/Cor4_3.lean) | `analyticAt_of_equivalentUltrametricNorm_discreteValueGroup` (DiscreteTargetAnalytic.lean) | K need not be complete. |
| Thm4_4 | Theorem 4.4 (pp. 10-11) | Finite-coordinate parameters: f analytic iff j∘f is; coefficient bounds d^n (1 if Z ultrametric) | proved | [Challenges/Thm4_4.lean](Challenges/Thm4_4.lean) | [Solutions/Thm4_4.lean](Solutions/Thm4_4.lean) | `analyticAt_of_closed_linearIsometry_of_equiv` (FiniteCoordinateReflection.lean), `FiniteCoordinateReflection.exists_lift`, `exists_hasFPowerSeriesOnBall_of_closed_linearIsometry_of_isUltrametricDist` | Parts 2-3 are for P = Fin d → K. "Analytic" is the Section 3 power-series notion. |
| Thm4_5a | Theorem 4.5(1) (p. 11) | c0 parameters: j∘f analytic ⇒ f analytic, coefficients lift without norm increase; also on retracts | proved | [Challenges/Thm4_5a.lean](Challenges/Thm4_5a.lean) | [Solutions/Thm4_5a.lean](Solutions/Thm4_5a.lean) | `c0_analyticOn_linearIsometry`, `c0_exists_hasFPowerSeriesOnBall_linearIsometry`, `c0_analyticOnNhd_linearIsometry` (Analysis/CZeroReflection.lean) | The retract clause is proved by glue in the solution file, not by a library declaration. |
| Thm4_5b | Theorem 4.5(2) (p. 11) | l1 parameters, fixed-degree representation: a∘γ analytic; also on retracts | proved | [Challenges/Thm4_5b.lean](Challenges/Thm4_5b.lean) | [Solutions/Thm4_5b.lean](Solutions/Thm4_5b.lean) | `analyticOn_comp_of_l1_fixed_degree_isometry`, `analyticOnNhd_comp_of_l1_fixed_degree_isometry` (Analysis/L1FixedDegreeReflection.lean) | The retract clause is proved by glue in the solution file. |
| Cor4_6 | Corollary 4.6 (p. 12) | Bundle theorem: Alt^k is an analytic bifunctor on bundles in six settings; C^n always | proved | [Challenges/Cor4_6.lean](Challenges/Cor4_6.lean) | [Solutions/Cor4_6.lean](Solutions/Cor4_6.lean) | existing bundle theorems + `BundleRows` glue (Geometry/BundleRows/) | Two theorems (object, morphism) per setting. Model 𝓘(K,P), no boundary. Functor laws not stated. Spherical alternative via `HasEquivalentSphericallyCompleteUltrametricNorm`. |

[^thm42]: `part1_ultrametric` can be closed by an instance that the challenge's definition import makes visible; this is disclosed. The library proves the stronger form with a single homogeneous lift.

## Section 5

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Prop5_1 | Proposition 5.1 (p. 13) | Alt^k(E;F) ≅ L(Λ^k_π E, F) isometrically and naturally | proved | [Challenges/Prop5_1.lean](Challenges/Prop5_1.lean) | [Solutions/Prop5_1.lean](Solutions/Prop5_1.lean) | `ExteriorRepresentation.exists_representation`, `exists_naturality` (Exterior/Representation/) | Λ^k_π E = separation quotient with the library seminorm. The isometry is stated as the existence of a `≃ₗᵢ` with Φ m ∘ ω_E = m. |
| Thm5_2 | Theorem 5.2 (pp. 13-14) | Universal and scalar (bidual) tests for regularity of W : U → L(X,Y) | proved | [Challenges/Thm5_2.lean](Challenges/Thm5_2.lean) | [Solutions/Thm5_2.lean](Solutions/Thm5_2.lean) | `DualTests.part1_analytic` … `part3_contDiff` (Exterior/DualTests.lean) | Open U in a normed P. Analytic = `AnalyticOnNhd`, C^n = `ContDiffOn` with n : ℕ∞. Each "iff for every F" split into implications. |

## Section 6

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Thm6_1a | Theorem 6.1(1) (p. 15) | Char p, k ≥ p: Banach E, F with A^k_{E,E;F} analytic nowhere and F not equivalently nonarchimedean | proved | [Challenges/Thm6_1a.lean](Challenges/Thm6_1a.lean) | [Solutions/Thm6_1a.lean](Solutions/Thm6_1a.lean) | `exists_banach_counterexample_full` (MainTheorem.lean) | The library theorem is stronger. K is not assumed complete. |
| Thm6_1b | Theorem 6.1(2) (p. 15) | K complete, not spherically complete, char p: nonarchimedean Banach E, D with scalar A^k analytic nowhere | proved | [Challenges/Thm6_1b.lean](Challenges/Thm6_1b.lean) | [Solutions/Thm6_1b.lean](Solutions/Thm6_1b.lean) | `ScalarObstruction` from `ChainSpaces.sequenceConclusion` (Scalar/ScalarObstruction.lean) | `[CharP K p]`, 0 < p. Sequence-space form in `lp (fun _ : Λ => Fin n → K) ∞`, Λ countable. |
| Cor6_2 | Corollary 6.2 (p. 15) | Alt^k is C^∞ on hom spaces, and analytic iff k! ≠ 0; also on Banach spaces | proved | [Challenges/Cor6_2.lean](Challenges/Cor6_2.lean) | [Solutions/Cor6_2.lean](Solutions/Cor6_2.lean) | `contDiff_alternatingMapAction`, `cpolynomialAt_alternatingMapAction_of_factorial_ne_zero` (AlternatingActionRegularity.lean), `factorial_ne_zero_iff_allBanachPrecompositionAnalytic` (FactorialClassification.lean) | Stated in hom coordinates. The power-series form is stated; it agrees here with the paper's C^ω reading. |
| Thm6_3 | Theorem 6.3 (p. 16) | Alt^k(−;K) analytic on all hom spaces iff k! ≠ 0 or K spherically complete | proved | [Challenges/Thm6_3.lean](Challenges/Thm6_3.lean) | [Solutions/Thm6_3.lean](Solutions/Thm6_3.lean) | `ScalarClassification.analytic_on_homs_iff'` and its Banach variants (Scalar/ScalarClassification/) | "Analytic on every Hom space" = `AnalyticOnNhd` on univ. Three source categories. |
| Prop6_4 | Proposition 6.4 (p. 16) | Shear g(u)(d,e) = (d+ue, e): g and g⁻¹ affine analytic, u ↦ g(u)^* not analytic at u0 | proved | [Challenges/Prop6_4.lean](Challenges/Prop6_4.lean) | [Solutions/Prop6_4.lean](Solutions/Prop6_4.lean) | `analyticAt_shear`, `analyticAt_shear_inverse`, `not_analyticAt_shear_pullback` (Analysis/ShearCounterexample.lean) | H = D × E with the max norm. |
| Prop6_4_bundle | Proposition 6.4, bundle paragraph (p. 16) | Analytic trivial bundle whose induced Alt^k(H;F) atlas is not analytic | proved | [Challenges/Prop6_4_bundle.lean](Challenges/Prop6_4_bundle.lean) | [Solutions/Prop6_4_bundle.lean](Solutions/Prop6_4_bundle.lean) | `shearBundle_realization` (Geometry/ShearBundleGeneral.lean) | Two-chart `VectorBundleCore` over L(E,D), general E, D and u₀. |
| Prop6_5 | Proposition 6.5 (p. 17) | Two analytic charts with nowhere-analytic transition on Alt^k; pullback h^*ω0 analytic into Mult but not Alt | proved | [Challenges/Prop6_5.lean](Challenges/Prop6_5.lean) | [Solutions/Prop6_5.lean](Solutions/Prop6_5.lean) | `TangentPullback.tangent_obstruction_of_scalar_obstruction`, `pullback_obstruction_of_scalar_obstruction` (Scalar/TangentPullback/) | The manifold is the model space, with charts id and an analytic equivalence ψ. "Polynomial analytic" = `CPolynomialOn`. |

## Section 7

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Thm7_2 | Theorem 7.2 (pp. 18-19) | Ambient analytic forms: sheaf of graded algebras with pullback, ∧, d; d² = 0, Leibniz | proved | [Challenges/Thm7_2.lean](Challenges/Thm7_2.lean) | [Solutions/Thm7_2.lean](Solutions/Thm7_2.lean) | `Forms` calculus (Forms/Calculus/) | Chart level only: open subsets of a normed space (Mathlib has no forms on manifolds). Degree identities stated pointwise via `finCongr`. |
| Prop7_3 | Proposition 7.3 (p. 19) | Intrinsic ⇒ ambient analytic; with a retraction or finite coordinates the cotangent atlas is analytic and sections agree | proved | [Challenges/Prop7_3.lean](Challenges/Prop7_3.lean) | [Solutions/Prop7_3.lean](Solutions/Prop7_3.lean) | `analyticOnNhd_iff_toContinuousMultilinearMap_of_retraction`, `contMDiffVectorBundle_alternating_of_retraction` (Forms/Comparison/) | Atlas and section claims at chart level; the atlas claim also as `ContMDiffVectorBundle`. |


## Section 9

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Sec9_zeroDual | Section 9, "Which fibers remove the obstruction?" (p. 23) | Over complete non-spherically-complete char p K, k ≥ p, every universal target has zero dual | proved | [Challenges/Sec9_zeroDual.lean](Challenges/Sec9_zeroDual.lean) | [Solutions/Sec9_zeroDual.lean](Solutions/Sec9_zeroDual.lean) | `ZeroDual` + `UniversalAlternatingTarget.of_retract` (Scalar/ZeroDual.lean) | Universal target = library `UniversalAlternatingTarget`. Zero dual = every CLM F → K is 0. |

## Appendices A-B

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| LemA_1 | Lemma A.1 (p. 24) | One-variable uniqueness of a bounded power series summing to 0 | proved | [Challenges/LemA_1.lean](Challenges/LemA_1.lean) | [Solutions/LemA_1.lean](Solutions/LemA_1.lean) | Mathlib only: `HasFPowerSeriesAt.apply_eq_zero` | No completeness. Convergence is read as partial sums. |
| LemA_2 | Lemma A.2 (p. 24) | A normed field of characteristic p > 0 is nonarchimedean | proved | [Challenges/LemA_2.lean](Challenges/LemA_2.lean) | [Solutions/LemA_2.lean](Solutions/LemA_2.lean) | `charP_isUltrametricDist` (Analysis/PositiveCharacteristic.lean) | Primality is derived from 0 < p. |
| LemA_3 | Lemma A.3 (pp. 24-25) | Finite-dimensional spaces over complete K: linear functionals are bounded and U is complete | proved | [Challenges/LemA_3.lean](Challenges/LemA_3.lean) | [Solutions/LemA_3.lean](Solutions/LemA_3.lean) | Mathlib only: `LinearMap.toContinuousLinearMap`, `FiniteDimensional.complete` | Two parts. |
| LemB_2 | Lemma B.2 (p. 26) | The determinant array Ω on Λ^k V is injective | proved | [Challenges/LemB_2.lean](Challenges/LemB_2.lean) | [Solutions/LemB_2.lean](Solutions/LemB_2.lean) | `determinantArraySubmodule_injective` (Algebra/DeterminantArray.lean) | part0 shows such an Ω exists. hk is unused. |
| LemB_3 | Lemma B.3 (p. 26) | Flattening rank ≤ sdim(ω) | proved | [Challenges/LemB_3.lean](Challenges/LemB_3.lean) | [Solutions/LemB_3.lean](Solutions/LemB_3.lean) | `exteriorFlattening_rank_le` (Algebra/ExteriorFlattening.lean), `exteriorSupportDim_attained` | sdim is defined in the file and bridged to the library's. |
| LemB_4 | Lemma B.4 (p. 27) | Contractions c_φ: cofactor formula, c_φ(Λ^k W) ⊆ W, dim span ≤ sdim | proved | [Challenges/LemB_4.lean](Challenges/LemB_4.lean) | [Solutions/LemB_4.lean](Solutions/LemB_4.lean) | `exteriorLastContraction`, `exteriorContractionSpan_finrank_le` (Algebra/ExteriorContraction.lean) | k = n+1. Part 3 also asserts the span is finite-dimensional. |
| PropB_5 | Proposition B.5 (p. 27) | Canonical exterior support S(ω): smallest supporting subspace, sdim = dim S(ω) | proved | [Challenges/PropB_5.lean](Challenges/PropB_5.lean) | [Solutions/PropB_5.lean](Solutions/PropB_5.lean) | `mem_exteriorPowerSubmodule_iff_contractionSpan_le`, `exteriorSupportDim_eq_finrank_contractionSpan` (Algebra/CanonicalExteriorSupport.lean) | Degree 0 and degree 1 remarks are omitted. |
| LemB_6 | Lemma B.6 (p. 28) | Identity principle for vector polynomials over an infinite field | proved | [Challenges/LemB_6.lean](Challenges/LemB_6.lean) | [Solutions/LemB_6.lean](Solutions/LemB_6.lean) | `VectorPolynomial.coeff_eq_zero_of_sum_eq_zero` (Algebra/PolynomialIdentity.lean) | Direct `exact`. |
| LemB_7 | Lemma B.7 (p. 28) | A homogeneous form of degree e ≤ q vanishing on F_q^m is zero | proved | [Challenges/LemB_7.lean](Challenges/LemB_7.lean) | [Solutions/LemB_7.lean](Solutions/LemB_7.lean) | `finiteField_homogeneous_extension_eq_zero` (Algebra/FiniteHomogeneousIdentity.lean) | Direct `exact`. |
| PropB_8 | Proposition B.8 (p. 29) | Pointwise vs polarized lifts: implications and counterexamples | proved | [Challenges/PropB_8.lean](Challenges/PropB_8.lean) | [Solutions/PropB_8.lean](Solutions/PropB_8.lean) | `sum_perm_eq_of_multiplier_diagonal` (Algebra/Polarization.lean), `PolarizationCounterexamples.exists_pw_not_pol`, `exists_pol1_not_pw` | "Not in general" is read as an existential. |
| ThmB_9 | Theorem B.9 (p. 30) | No bounded-support multiplier lift over a finite field when k! = 0 | proved | [Challenges/ThmB_9.lean](Challenges/ThmB_9.lean) | [Solutions/ThmB_9.lean](Solutions/ThmB_9.lean) | `finiteField_multiplier_obstruction(_full, _finsupp)` (Algebra/FiniteFieldObstruction.lean) | Part (2) is split into E0 = V and E0 = V_fin. |
| LemB_10 | Lemma B.10 (pp. 30-31) | Infinite pattern-homogeneous subset (Ramsey) | proved | [Challenges/LemB_10.lean](Challenges/LemB_10.lean) | [Solutions/LemB_10.lean](Solutions/LemB_10.lean) | `OrderPattern.exists_infinite_order_homogeneous` (Algebra/OrderPattern.lean) | "Same pattern" uses the paper's comparison characterization. |
| LemB_11 | Lemma B.11 (p. 32) | Output-free clusters cancel: Ω_{Ψ(u;v)}(c) = χ | proved | [Challenges/LemB_11.lean](Challenges/LemB_11.lean) | [Solutions/LemB_11.lean](Solutions/LemB_11.lean) | `cluster_family_cancellation_of_intervals` (Algebra/ClusterCancellation.lean) | [^b1113] |
| LemB_12 | Lemma B.12 (pp. 32-33) | Staircase: χ(τ) = χ(τ') under an adjacent exchange | proved | [Challenges/LemB_12.lean](Challenges/LemB_12.lean) | [Solutions/LemB_12.lean](Solutions/LemB_12.lean) | `clusterValue_adjacent_eq` (Algebra/ClusterStaircase.lean) | [^b1113] |
| LemB_13 | Lemma B.13 (p. 33) | Diagonal: Σ_τ χ(τ) = 1 | proved | [Challenges/LemB_13.lean](Challenges/LemB_13.lean) | [Solutions/LemB_13.lean](Solutions/LemB_13.lean) | `sum_clusterValue_order_eq_one` (Algebra/ClusterDiagonal.lean) | [^b1113] |
| RemB_15 | Remark B.15 (p. 34) | k! invertible: normalized lift is alternating, (Pol1), sdim ≤ k², cluster value 1/k! | proved | [Challenges/RemB_15.lean](Challenges/RemB_15.lean) | [Solutions/RemB_15.lean](Solutions/RemB_15.lean) | `normalizedMultiplierLift` and lemmas (Algebra/NormalizedMultiplierLift.lean) | Defined on V instead of V_fin, which is stronger. The commentary sentences and the (5,3) example are not formalized. |

[^b1113]: The paper's ambient hypotheses (a)-(c) together with k! = 0 are contradictory, so each lemma keeps only the hypotheses its proof uses. This keeps the statements from being vacuous. The cluster definitions are shared across B.11-B.13.

## Appendix C

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| ThmC_1 | Theorem C.1 (p. 35) | Over κ((X)), A^k into B has no bounded lift, hence is analytic nowhere | proved | [Challenges/ThmC_1.lean](Challenges/ThmC_1.lean) | [Solutions/ThmC_1.lean](Solutions/ThmC_1.lean) | `laurent_not_hasBoundedLift`, `laurent_not_analyticAt` (Analysis/LaurentResidueLift.lean) | HasBoundedKLinearLift is defined in the file. |
| LemC_2 | Lemma C.2 (pp. 35-36) | ‖·‖_π is a norm; Ω injective with ‖Ω‖ ≤ 1; completion B, J, W_B | proved | [Challenges/LemC_2.lean](Challenges/LemC_2.lean) | [Solutions/LemC_2.lean](Solutions/LemC_2.lean) | `projectiveExterior_properties`, `projectiveExteriorCompletion_properties` (Analysis/ProjectiveExterior.lean) | projNorm is defined in the file and proved equal to the library seminorm. |
| PropC_3 | Proposition C.3 (pp. 36-37) | Unique η(b) with Ω(η b) = coeff₀(J b), κ-linear, sdim ≤ k M_r ‖b‖ | proved | [Challenges/PropC_3.lean](Challenges/PropC_3.lean) | [Solutions/PropC_3.lean](Solutions/PropC_3.lean) | `completedLaurentCoefficient_*` (Analysis/LaurentCompletedCoefficient.lean) | Ω^κ is quantified (its existence is LemB_2). M_r is defined in the file. |
| LemC_4 | Lemma C.4 (pp. 37-38) | The coefficient lift Ψ is 2k-linear, alternating, sdim-bounded, (Pol) and (Pol1) | proved | [Challenges/LemC_4.lean](Challenges/LemC_4.lean) | [Solutions/LemC_4.lean](Solutions/LemC_4.lean) | `laurentResidueLift_*` (Analysis/LaurentResidueLift.lean, LaurentResiduePolarization.lean) | (Ψ1)-(Ψ4) and (Pol1) are bundled in one theorem. |
| PropC_6 | Proposition C.6 (p. 39) | Multipliers on c0: σ has no bounded lift; a ↦ A(u0 + D_a) is analytic nowhere | proved | [Challenges/PropC_6.lean](Challenges/PropC_6.lean) | [Solutions/PropC_6.lean](Solutions/PropC_6.lean) | `CZeroMultipliers` (Laurent/CZeroMultipliers/) | Hypotheses of Theorem C.1 (κ finite, char p, k ≥ p). c₀ = `C₀(ℕ,K₁)`. |
| CorC_7 | Corollary C.7 (pp. 39-40) | Diagonal transitions over a c0 base: analytic isometric bundle with non-analytic Alt^k atlas | proved | [Challenges/CorC_7.lean](Challenges/CorC_7.lean) | [Solutions/CorC_7.lean](Solutions/CorC_7.lean) | `DiagonalTransitions` (Laurent/DiagonalTransitions.lean) | Explicit-map form, not a `ContMDiffVectorBundle` statement. |
| CorC_8 | Corollary C.8 (p. 40) | Over F_q((u)), k ≥ p: the alternating construction preserves bundles over P iff dim P < ∞ | proved | [Challenges/CorC_8.lean](Challenges/CorC_8.lean) | [Solutions/CorC_8.lean](Solutions/CorC_8.lean) | `FiniteDimSharp.IfHalf`, `FiniteDimSharp.OnlyIf` (Laurent/FiniteDimSharp/) | K = `LaurentField κ r`, κ finite. Bundle preservation defined in the file. All types in one universe. The "only if" half avoids Serre's full basis theorem: a complemented copy of c₀(ℕ,K) suffices. |

## Appendices D-E

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| LemD_1 | Lemma D.1 (pp. 40-41) | Complete ultrametric space with distances in r^ℤ ∪ {0} is spherically complete | proved | [Challenges/LemD_1.lean](Challenges/LemD_1.lean) | [Solutions/LemD_1.lean](Solutions/LemD_1.lean) | `sphericallyCompleteSpace_of_discreteDist_radius` (Analysis/DiscreteSphericalCompleteness.lean) | None of substance. |
| LemD_2 | Lemma D.2 (p. 41) | Laurent subfield: nonarchimedean, norm of Laurent polynomials, isometric ev_t, image spherically complete | proved | [Challenges/LemD_2.lean](Challenges/LemD_2.lean) | [Solutions/LemD_2.lean](Solutions/LemD_2.lean) | `norm_sum_zmod_zpow_eq`, `exists_laurentField_evaluation`, `sphericallyCompleteSpace_closure_subfieldClosure` (Analysis/LaurentSubfieldExtra/) | F_p((X)) = `LaurentField (ZMod p) r`. "Closure of F_p(t)" = closure of `Subfield.closure {t}`. Evaluation formula as `HasSum` over ℤ. |
| ThmD_3 | Theorem D.3 (p. 42) | Ingleton's extension theorem | proved | [Challenges/ThmD_3.lean](Challenges/ThmD_3.lean) | [Solutions/ThmD_3.lean](Solutions/ThmD_3.lean) | `exists_extension_of_sphericallyComplete` (Analysis/SphericalCompleteness.lean) | K1 is nontrivially normed (from (H1)), so the trivially normed case is not covered. |
| CorD_4 | Corollary D.4 (p. 42) | Ingleton projection ϖ : K' → K1 with ϖ\|K1 = id, \|ϖ λ\| ≤ \|λ\| | proved | [Challenges/CorD_4.lean](Challenges/CorD_4.lean) | [Solutions/CorD_4.lean](Solutions/CorD_4.lean) | `exists_scalar_projection` (Analysis/ScalarProjection.lean) | K1 ⊆ K' is a NormedAlgebra. |
| LemD_5 | Lemma D.5 (p. 42) | Unique bounded extension of linear and multilinear maps from dense subspaces | proved | [Challenges/LemD_5.lean](Challenges/LemD_5.lean) | [Solutions/LemD_5.lean](Solutions/LemD_5.lean) | `denseLinearExtension` (DenseMultilinearExtension.lean), `exists_denseMultilinearFamilyExtension_of_bound` | Any nontrivially normed field, which is more general. |
| LemD_6 | Lemma D.6 (p. 43) | Projective base change: bounds, K'-norm, isometric ι_V, contraction Π_V | proved | [Challenges/LemD_6.lean](Challenges/LemD_6.lean) | [Solutions/LemD_6.lean](Solutions/LemD_6.lean) | `baseChangeSeminorm_*` (Analysis/ProjectiveBaseChange.lean, CompletedBaseChange.lean), `denseLinearExtension` | Every completion is quantified. V and K' share one universe. |
| LemD_7 | Lemma D.7 (p. 44) | Base change of operators f ↦ f_{K'}, ‖f_{K'}‖ ≤ ‖f‖, K1-linear | proved | [Challenges/LemD_7.lean](Challenges/LemD_7.lean) | [Solutions/LemD_7.lean](Solutions/LemD_7.lean) | `baseChangeOperatorAlgebraic`, `norm_completedBaseChangeOperator_le` (BaseChangeOperators.lean) | One universe. The extra IsUltrametricDist K1 follows from (H2). |
| LemD_8 | Lemma D.8 (pp. 44-45) | Base change of alternating forms m ↦ m_{K'} | proved | [Challenges/LemD_8.lean](Challenges/LemD_8.lean) | [Solutions/LemD_8.lean](Solutions/LemD_8.lean) | `baseChangeAlternatingForms` (BaseChangeAlternatingForms.lean) | The library does not need F1 complete, so it is stronger. |
| PropD_9 | Proposition D.9 (p. 45) | Descent of a lift from K' to K1; nowhere-analyticity ascends | proved | [Challenges/PropD_9.lean](Challenges/PropD_9.lean) | [Solutions/PropD_9.lean](Solutions/PropD_9.lean) | `exists_baseChangeLiftDescent`, `not_analyticAt_completedBaseChange_of_not_analyticAt` (BaseChangeLiftDescent.lean) | A local norm instance is used for the lift space. |
| LemD_11 | Lemma D.11 (p. 46) | Over incomplete K, the map spaces and lifts agree with those over K̂ | proved | [Challenges/LemD_11.lean](Challenges/LemD_11.lean) | [Solutions/LemD_11.lean](Solutions/LemD_11.lean) | `denseScalarLinearEquiv`, `denseScalarAlternatingEquiv` (DenseScalarRestriction.lean), `denseScalarLiftTransport` | K̂ is an abstract complete dense extension. Equalities are isometric equivalences. |
| PropE_1 | Proposition E.1 (pp. 46-47) | B (and F = B⊗̂K') has no equivalent nonarchimedean norm | proved | [Challenges/PropE_1.lean](Challenges/PropE_1.lean) | [Solutions/PropE_1.lean](Solutions/PropE_1.lean) | `norm_laurentBlockWedge` (LaurentBlockNorms.lean), `laurentExterior_not_hasEquivalentUltrametricNorm`, `HasLinearUnitSumGrowth.not_hasEquivalentUltrametricNorm` | Six theorems. |
| RemE_2 | Remark E.2 (p. 48) | K1 = K̂ case: base change is trivial; direct F_q((u)) route to Theorem 6.1(1) | proved | [Challenges/RemE_2.lean](Challenges/RemE_2.lean) | [Solutions/RemE_2.lean](Solutions/RemE_2.lean) | `completedBaseChangeEmbedding_surjective_self` (Analysis/BaseChangeCompleteSelf.lean) | Part 1 generalized to every complete V. F_q((u)) = `LaurentField κ r`. |


## Appendix F

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| ThmF_1 | Theorem F.1 (p. 48) | K complete, not spherically complete, k! = 0: nonarchimedean Banach E, E' with scalar A^k analytic nowhere | proved | [Challenges/ThmF_1.lean](Challenges/ThmF_1.lean) | [Solutions/ThmF_1.lean](Solutions/ThmF_1.lean) | `ChainSpaces.abstractConclusion`, `ChainSpaces.sequenceConclusion` (Scalar/ChainSpaces/) | Abstract and sequence-space forms; ℓ^∞(Λ;K^n) = `lp`. Needs `maxSynthPendingDepth 2`. |
| LemF_2 | Lemma F.2 (pp. 48-49) | Bounded d-linear forms on ℓ^∞(I,K) are sums of null arrays; tail property; diagonal → 0 | proved | [Challenges/LemF_2.lean](Challenges/LemF_2.lean) | [Solutions/LemF_2.lean](Solutions/LemF_2.lean) | `Tails.multilinear_expansion`, `multilinear_tail`, `multilinear_diagonal_tendsto_zero` (Scalar/Tails/) | ℓ^∞(I,K) = `lp (fun _ : I => K) ∞`, e_i = `lp.single`. Ported from the characteristic-2 repository's tail lemma. |
| LemF_3 | Lemma F.3 (pp. 49-50) | Chain gap in the word tree L^{<ω} | proved | [Challenges/LemF_3.lean](Challenges/LemF_3.lean) | [Solutions/LemF_3.lean](Solutions/LemF_3.lean) | `ChainGap.labelChain_inter_subsingleton`, `iInter_nonempty_of_cofinite_on_chains` (Scalar/ChainGap.lean) | Λ = `List L`, extension = prefix; j-chains via `IsLabelChain`. |
| LemF_4 | Lemma F.4 (p. 50) | Finite fibre obstruction: no k-linear τ meets both conditions | proved | [Challenges/LemF_4.lean](Challenges/LemF_4.lean) | [Solutions/LemF_4.lean](Solutions/LemF_4.lean) | `FibreObstruction.not_exists_fibre_map` (Scalar/FibreObstruction/) | Algebraic alternating maps over κ, 0-based indices, δ′ = `Basis.det`. |
| LemF_5 | Lemma F.5 (p. 51) | Finite test certificate with threshold 1 | proved | [Challenges/LemF_5.lean](Challenges/LemF_5.lean) | [Solutions/LemF_5.lean](Solutions/LemF_5.lean) | `TestCertificate.exists_finite_test_certificate` (Scalar/TestCertificate/) | Adds the standing hypothesis k! = 0 that the printed lemma omits (referee finding M3). |

## Appendix G

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| PropG_1 | Proposition G.1 (p. 54) | Homogeneous reflection in degree n ⟺ Δ_n(P) is complemented in T_n(P) | proved | [Challenges/PropG_1.lean](Challenges/PropG_1.lean) | [Solutions/PropG_1.lean](Solutions/PropG_1.lean) | `homogeneous_reflection_iff_projection` (Analysis/HomogeneousTensorReflection.lean:181), `exists_diagonal_lift_of_projection` | In part 1, targets are in Type u; part 2 allows any universe. |
| ThmG_3 | Theorem G.3 (pp. 54-55) | Universal analytic reflection ⟺ projections R_n with limsup ‖R_n‖^{1/n} < ∞ | proved | [Challenges/ThmG_3.lean](Challenges/ThmG_3.lean) | [Solutions/ThmG_3.lean](Solutions/ThmG_3.lean) | `universal_analytic_reflection_iff_tensor_projections` (Analysis/UniversalAnalyticReflection.lean:309), `analyticAt_subtype_of_tensor_projections` | The limsup is in ENNReal. Part 2 allows targets in any universe. |
| PropG_4 | Proposition G.4 (p. 55) | For l1(I,K), the infimum of projection norms is n!, so no universal analytic reflection | proved | [Challenges/PropG_4.lean](Challenges/PropG_4.lean) | [Solutions/PropG_4.lean](Solutions/PropG_4.lean) | `L1Projection.sInf_norm_projection_eq_factorial`, `not_universalAnalyticReflection` (Tensor/L1Projection/) | ℓ¹ = `lp _ 1`. Infimum as a real `sInf`. Test targets in one universe. |
| CorG_5 | Corollary G.5 (pp. 55-56) | A map analytic into Z, C^∞ into W, not analytic into W, and a limit of entire polynomials | proved | [Challenges/CorG_5.lean](Challenges/CorG_5.lean) | [Solutions/CorG_5.lean](Solutions/CorG_5.lean) | `PolynomialApproximation.exists_smooth_nonanalytic_polynomial_limit` (Tensor/PolynomialApproximation/) | Z in the universe of P. Uniform convergence on every closed ball of radius < 1. |

## Appendix H

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| LemH_3 | Lemma H.3 (p. 57) | Split destinations give analytic actions; split pairs form an analytic domain | proved | [Challenges/LemH_3.lean](Challenges/LemH_3.lean) | [Solutions/LemH_3.lean](Solutions/LemH_3.lean) | `alternatingFunctor_analyticOnNhd_hom_of_split_destination`, `splitPairs_isAnalyticDomain` (Category/AnalyticDomains.lean) | The challenge imports the proving module for definitions (disclosed). |
| ThmH_4 | Theorem H.4 (p. 57) | Over F_p(t), k ≥ p: no largest full analytic domain (four variants plus witnesses) | proved | [Challenges/ThmH_4.lean](Challenges/ThmH_4.lean) | [Solutions/ThmH_4.lean](Solutions/ThmH_4.lean) | `DeterminantPair.Padding.no_largest_full_analytic_domain` (Category/NoLargestAnalyticDomain.lean) | part1 is the existing comparator statement `no_largest_full_analytic_domain_charP`. |
| LemH_5 | Lemma H.5 (p. 58) | Rigidity of E: endomorphisms are scalars, dual is zero | proved | [Challenges/LemH_5.lean](Challenges/LemH_5.lean) | [Solutions/LemH_5.lean](Solutions/LemH_5.lean) | `RigidDenseSource.existsUnique_scalar`, `dual_eq_zero` (Analysis/RigidDenseSourceGeneric.lean) | Assumes only that the a_i are independent, so it is at least as strong. |
| LemH_6 | Lemma H.6 (p. 58) | Every bounded p-linear map D^p → G is alternating; (D,G) is split | proved | [Challenges/LemH_6.lean](Challenges/LemH_6.lean) | [Solutions/LemH_6.lean](Solutions/LemH_6.lean) | `DeterminantPairGeneral` (Category/DeterminantPairGeneral/) | Every jointly algebraically independent family, as in the paper. |
| LemH_7 | Lemma H.7 (p. 59) | Degree-one part of C_0 is zero | proved | [Challenges/LemH_7.lean](Challenges/LemH_7.lean) | [Solutions/LemH_7.lean](Solutions/LemH_7.lean) | `DeterminantQuadratic.homogeneous_linear_eq_zero` (Algebra/DeterminantQuadraticGap.lean) | Purely algebraic; uses RatFunc (ZMod p). |

## Appendix I

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| PropI_1 | Proposition I.1 (pp. 61-62) | K complete nonarchimedean, E or D of countable type: scalar A^k analytic in every degree | proved | [Challenges/PropI_1.lean](Challenges/PropI_1.lean) | [Solutions/PropI_1.lean](Solutions/PropI_1.lean) | `CountableType.analyticAt_compContinuousLinearMapCLM_of_countableType_source`, `_target` (Coordinates/CountableType/) | "Countable type" defined in the file. Two parts: E or D of countable type. |
| PropI_2 | Proposition I.2 (pp. 62-63) | A continuous algebraic polynomial on c0 has a bounded lift with ‖q‖ ≤ C_{K,n}‖p‖_diag | proved | [Challenges/PropI_2.lean](Challenges/PropI_2.lean) | [Solutions/PropI_2.lean](Solutions/PropI_2.lean) | `AlgebraicPolynomialCZero.BoundedLift` (Coordinates/AlgebraicPolynomialCZero/) | ‖p‖_diag defined in the file. C quantified before I, Z, p. |
| RemI_3 | Remark I.3 (p. 63) | A weighted, non-spherically-complete norm on c0 with analytic precomposition | proved | [Challenges/RemI_3.lean](Challenges/RemI_3.lean) | [Solutions/RemI_3.lean](Solutions/RemI_3.lean) | `WeightedNorm` (Coordinates/WeightedNorm/) | K = `LaurentField (ZMod p) (1/2)`. The weighted space is given through a model, with its existence as part 1. |


## Existing comparator challenge

`challenge.lean`, `solution.lean` and `comparator.json` (namespace `AlternatingAnalyticChallenge`) are **unchanged**. Their six statements map to ledger IDs as follows.

| Statement in challenge.lean | Ledger ID |
|---|---|
| `false_of_contDiff_omega_compContinuousLinearMapCLM` | Thm6_1a / Cor6_2 (failure of universal C^ω precomposition) |
| `false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach` | Thm6_1a / Cor6_2 (char p, k ≥ p, Banach, E' = E) |
| `contDiff_compContinuousLinearMapCLM_of_sphericallyComplete` | Thm4_2 |
| `contMDiffVectorBundle_alternating_of_finiteCoordinates` | Cor4_6, finite-coordinate row (row 2) |
| `false_of_contMDiffVectorBundle_omega_alternating` | Prop6_4_bundle (bundle realization) |
| `no_largest_full_analytic_domain_charP` | ThmH_4 (same statement as ThmH_4.part1) |

## Scope notes

Every row's last column lists how the Lean statement differs from the paper; the challenge docstrings give the details. The differences a reader should know about:

- **Theorem 2.1** had no formal statement when the ledger was created. Its statement (`bundleLifting`, `bundleLifting_familywise`) was written during formalization and has not yet been reviewed by the author. It groups the variables by variance, uses the canonical trivializations so the functor exists on the nose, and does not state independence of the trivializing cover.
- **Theorem 7.2 and Proposition 7.3** are stated at chart level, on open subsets of a normed space, because Mathlib has no differential forms on manifolds. Proposition 7.3's atlas claim is also stated as a `ContMDiffVectorBundle` instance.
- **Corollary C.7** is stated for the explicit transition and section maps, not as a bundle statement. **Corollary 4.6** states objects and morphisms for each setting but not the functor laws.
- **Lemma F.5** includes the hypothesis k! = 0 that the printed lemma leaves implicit (referee finding M3).
- **Lemma H.7** imports its proving module in the challenge so that both files resolve the same instances (see its docstring).

## Verification record (2026-10-08)

Checked on macOS on branch `ledger-proofs` (Lean v4.34.0-rc2, Mathlib fork pin 2b73d98):

- `lake build` of every target (`AlternatingAnalytic`, `challenge`, `solution`, `Challenges`, `Solutions`): completed successfully, 3618 jobs, with no `sorry` outside challenge files.
- `python3 -I scripts/check_claim.py <ID>` for all 76 claims: all pass. Each run confirms the challenge file is unchanged since `ledger-base` (except Theorem 2.1, whose statement was added), builds the pair, checks that each of the 211 solution theorems depends only on `propext`, `Classical.choice` and `Quot.sound`, and checks that `#check` of every theorem and `#print` of every definition, under `pp.all`, give identical output for the challenge and the solution. Receipts are written to `work/checks/<ID>.json`, which git ignores.
- All library modules import together in one file, so no two developments declare the same name.
- No new library file contains `sorry`, `admit`, an `axiom` declaration, `native_decide`, `unsafe` code or a heartbeat increase.
- The comparator was not run on the ledger pairs. The existing six-statement challenge was accepted by comparator revision 19e111e on 2026-10-08 (see README).
