# Claim ledger for 'Alternating bundles and analytic descent'

Ledger date 2026-10-08, library commit f85751e. Paper: Jack McCarthy, *Alternating bundles and analytic descent*, October 2026, 64 pp.

**What this is.** Every numbered claim of the paper has its own Lean file under `Challenges/`. Each file states the claim with `sorry`, under the namespace `AlternatingAnalyticChallenge.<ID>`. The module docstring gives the paper reference and page, the informal statement, and "Formalization notes" that list every way the Lean statement differs from the paper. When the library proves the claim, `Solutions/<ID>.lean` proves the same statement from library declarations, with identical definitions and statements character for character, and `Challenges/<ID>.json` is a comparator config for that pair. Multi-part results have one theorem per part. `Partial/Cor4_6.lean` is a partial proof file: it repeats the fourteen statements of `Challenges/Cor4_6.lean` and proves twelve of them from the library, leaving the two spherical-target theorems as `sorry`. It is not a solution and no comparator config uses it.

**Status legend.**
- **proved**: `Solutions/<ID>.lean` compiles with no `sorry` and proves the identical statement. Only `propext`, `Quot.sound` and `Classical.choice` are allowed.
- **partially_proved**: the library proves a special case, a weaker form, or some parts but not all. There is no solution file. The row names what the library has and what is missing.
- **not_proved**: the library has no Lean proof of the claim. Some ingredients may exist.
- **statement_pending**: no faithful formal statement yet. The file explains why.

**How to check.**
- Build everything: `lake build Challenges Solutions Partial` (these three targets are in `defaultTargets`, so plain `lake build` covers them). Compile one claim: `lake env lean Challenges/<ID>.lean` (only `sorry` warnings expected), then `lake env lean Solutions/<ID>.lean` (must have no `sorry`). On a machine with little memory, `scripts/run_lean.py` compiles files through a four-slot lock: `python3 -I scripts/run_lean.py Challenges/<ID>.lean Solutions/<ID>.lean`.
- Run the comparator on a pair: `lake env /path/to/comparator/.lake/build/bin/comparator Challenges/<ID>.json`. The `Challenges` and `Solutions` targets are declared in `lakefile.toml`, so the comparator can build the two modules of a pair.
- Add a solution and flip the status: copy the challenge file to `Solutions/<ID>.lean`, add the needed imports (never import `Challenges`), and replace each `sorry` with a proof. Leave every definition and statement unchanged. Compile it with no `sorry`, write `Challenges/<ID>.json` in the format of the existing ones, then change the row below to **proved**.

## Summary

Total: **76 claims**, in 76 challenge files. **45 proved**, 13 partially_proved, 17 not_proved, 1 statement_pending. All 76 challenge files elaborate. All 45 solution files compile with no `sorry`, and each has a `.json` config.

| Section | Claims | proved | partially_proved | not_proved | statement_pending |
|---|---:|---:|---:|---:|---:|
| 2-3 (constructions, descent) | 5 | 0 | 4 | 0 | 1 |
| 4 (positive results, bundle theorem) | 7 | 6 | 1 | 0 | 0 |
| 5 (representation, duality tests) | 2 | 0 | 0 | 2 | 0 |
| 6 (obstructions, classification) | 7 | 3 | 2 | 2 | 0 |
| 7 (differential calculus) | 2 | 0 | 1 | 1 | 0 |
| 9 (fibers) | 1 | 0 | 0 | 1 | 0 |
| A-B (algebra, finite fields) | 16 | 16 | 0 | 0 | 0 |
| C (Laurent obstruction) | 7 | 4 | 1 | 2 | 0 |
| D-E (base change, target norm) | 12 | 10 | 2 | 0 | 0 |
| F (scalar counterexample) | 5 | 0 | 0 | 5 | 0 |
| G (tensor reflection) | 4 | 2 | 0 | 2 | 0 |
| H (analytic domains) | 5 | 4 | 1 | 0 | 0 |
| I (countable type, c0, weighted norm) | 3 | 0 | 1 | 2 | 0 |
| **Total** | **76** | **45** | **13** | **17** | **1** |

In the tables below, file names are relative to the repository root, and "—" means no file. Unless a row says otherwise, the degree is `Fin k`.

## Sections 2-3

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Thm2_1 | Theorem 2.1 (pp. 4-5) | Fiberwise application lifts C^n mixed-variance functors to functors on C^n bundle categories | statement_pending | Challenges/Thm2_1.lean | — | (auxiliary only) `contMDiffVectorBundle_alternating_of_family` (Geometry/AnalyticAlternatingBundle.lean:124) | [^thm21] |
| Prop2_2 | Proposition 2.2 (p. 6) | The ambient action g∘m∘(f,…,f) is a bounded (k+1)-linear diagonal, analytic, with values in Alt^k | partially_proved | Challenges/Prop2_2.lean | — | parts 3-4: `ambientAlternatingMapAction`, `analyticAt_ambient_alternatingMapAction`, `isClosed_range_alternatingMapActionInclusion` (Analysis/FiniteCoordinateFamilies.lean) | [^prop22] |
| Thm3_1 | Theorem 3.1 (p. 7) | Coefficient descent: diagonals lie in j(W); f analytic iff the coefficients lift with a geometric bound | partially_proved | Challenges/Thm3_1.lean | — | part 1: `HasFPowerSeriesAt.diagonal_mem_closedSubspace` (Analysis/ClosedSubspaceCoefficients.lean) + glue | [^thm31] |
| Lem3_2 | Lemma 3.2 (p. 8) | f is C^n on open U iff j∘f is C^n | partially_proved | Challenges/Lem3_2.lean | — | global version only: `LinearIsometry.comp_contDiff_iff` (Mathlib fork, not upstream: Mathlib/Analysis/Calculus/ContDiff/LinearIsometry.lean:106) | [^lem32] |
| Prop3_3 | Proposition 3.3 (p. 8) | One lift, every base point: analytic somewhere ⟺ bounded lift ⟺ polynomial everywhere; dichotomy for A^k | partially_proved | Challenges/Prop3_3.lean | — | precomposition case only: `Round24Transfer.tfae_Q`, `hasBoundedLift_of_analyticAt` (Analysis/LiftCriterion.lean) | [^prop33] |

[^thm21]: Only an auxiliary special case is stated (`alternating_object_familywise`: the Alt^k bifunctor, objects only, familywise form). The library proves it word for word. The paper's functor B^n_M, with morphisms, natural transformations and the whole-hom-space version, needs definitions that exist in neither Mathlib nor the library. Library's `alternatingBundleFunctor` (Geometry/AnalyticAlternatingBundleFunctor.lean) needs n = ω, a finite-coordinate base, model 𝓘(K,P) and one universe. With boundary or corners, the familywise hypothesis is a different condition, not a more general one.
[^prop22]: Parts 1-2 (full multilinear inputs and their C^ω property) are missing. The library's representative exists only on alternating inputs. Parts 3-4 close with short glue (checked in scratch, not committed). The norm bound ‖H‖ ≤ 1 is not stated.
[^thm31]: Part 2, the iff criterion, is not in the library. The open set U is dropped, and the coefficients are a FormalMultilinearSeries with a HasSum expansion.
[^lem32]: The open-set ContDiffOn version would need the local induction redone, since there are no bump functions over a general field.
[^prop33]: The TFAE for a general a : H → W with an ambient homogeneous representation is missing. The dichotomy for A^k follows from the library with about 15 lines of glue. k = 0 is allowed; it is trivial and disclosed.

## Section 4

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Prop4_1 | Proposition 4.1 (pp. 8-9) | A bounded retraction Alt→Mult gives a lift of norm ≤ ‖ρ‖; lifts exist if k! ≠ 0 or finite coordinates | proved | Challenges/Prop4_1.lean | Solutions/Prop4_1.lean | `contractingRetractionLift` (SortedBasisLift.lean), `altProj` (FactorialInvertible.lean), `finiteCoordinateDomainLift`, `finiteCoordinateCodomainLift` | Norm bound stated pointwise. Parts (1)-(2) are existence only. |
| Thm4_2 | Theorem 4.2 (pp. 9-10) | Spherically complete targets: Alt^k is ultrametric, spherically complete and retracts; A^k is a continuous polynomial | proved | Challenges/Thm4_2.lean | Solutions/Thm4_2.lean | `sphericallyCompleteSpace_continuousAlternatingMap`, `exists_contracting_retraction_toContinuousMultilinearMap`, `hasBoundedLift_of_sphericallyComplete` (SphericalAnalytic.lean) | 4 parts. IsContinuousPolynomial is defined in the file. [^thm42] |
| Cor4_3 | Corollary 4.3 (p. 10) | Discrete value group: equivalent nonarchimedean Banach targets make A^k analytic | proved | Challenges/Cor4_3.lean | Solutions/Cor4_3.lean | `analyticAt_of_equivalentUltrametricNorm_discreteValueGroup` (DiscreteTargetAnalytic.lean) | K need not be complete. |
| Thm4_4 | Theorem 4.4 (pp. 10-11) | Finite-coordinate parameters: f analytic iff j∘f is; coefficient bounds d^n (1 if Z ultrametric) | proved | Challenges/Thm4_4.lean | Solutions/Thm4_4.lean | `analyticAt_of_closed_linearIsometry_of_equiv` (FiniteCoordinateReflection.lean), `FiniteCoordinateReflection.exists_lift`, `exists_hasFPowerSeriesOnBall_of_closed_linearIsometry_of_isUltrametricDist` | Parts 2-3 are for P = Fin d → K. "Analytic" is the Section 3 power-series notion. |
| Thm4_5a | Theorem 4.5(1) (p. 11) | c0 parameters: j∘f analytic ⇒ f analytic, coefficients lift without norm increase; also on retracts | proved | Challenges/Thm4_5a.lean | Solutions/Thm4_5a.lean | `c0_analyticOn_linearIsometry`, `c0_exists_hasFPowerSeriesOnBall_linearIsometry`, `c0_analyticOnNhd_linearIsometry` (Analysis/CZeroReflection.lean) | The retract clause is proved by glue in the solution file, not by a library declaration. |
| Thm4_5b | Theorem 4.5(2) (p. 11) | l1 parameters, fixed-degree representation: a∘γ analytic; also on retracts | proved | Challenges/Thm4_5b.lean | Solutions/Thm4_5b.lean | `analyticOn_comp_of_l1_fixed_degree_isometry`, `analyticOnNhd_comp_of_l1_fixed_degree_isometry` (Analysis/L1FixedDegreeReflection.lean) | The retract clause is proved by glue in the solution file. |
| Cor4_6 | Corollary 4.6 (p. 12) | Bundle theorem: Alt^k is an analytic bifunctor on bundles in six settings; C^n always | partially_proved | Challenges/Cor4_6.lean | — (partial: Partial/Cor4_6.lean) | row 2: `contMDiffVectorBundle_alternating_of_finiteCoordinates` (Geometry/AnalyticAlternatingBundle.lean), `alternatingBundleHom_of_finiteCoordinates` (Geometry/AnalyticAlternatingBundleMorphism.lean); other rows: glue in Partial/Cor4_6.lean | [^cor46] |

[^thm42]: `part1_ultrametric` can be closed by an instance that the challenge's definition import makes visible; this is disclosed. The library proves the stronger form with a single homogeneous lift.
[^cor46]: Status of the 14 theorems. The 2 row-2 theorems (finite-coordinate base) are proved by library `exact`. Ten more are proved in Partial/Cor4_6.lean by library declarations plus glue: rows 1 (factorial), 1 (finite source coordinates), 3 (c0 retract), 4 (l1 retract) and the smooth row, each with bundle and morphism. The 2 spherical theorems (`row1_spherical_bundle` and `row1_spherical_morphism`) are not proved. The library's spherical theorem needs the given fiber norm itself to be ultrametric and spherically complete; the transfer to an equivalent such norm is missing. The model is 𝓘(K,P) without boundary, and the functor laws are not stated.

## Section 5

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Prop5_1 | Proposition 5.1 (p. 13) | Alt^k(E;F) ≅ L(Λ^k_π E, F) isometrically and naturally | not_proved | Challenges/Prop5_1.lean | — | — | Λ^k_π E is the SeparationQuotient of ⋀^k E with `projectiveExteriorSeminorm`. The library has the seminorm but no universal property. |
| Thm5_2 | Theorem 5.2 (pp. 13-14) | Universal and scalar (bidual) tests for regularity of W : U → L(X,Y) | not_proved | Challenges/Thm5_2.lean | — | — | Analytic and C^n versions, 3 parts each. The "iff for every F" clauses are split into implications. |

## Section 6

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Thm6_1a | Theorem 6.1(1) (p. 15) | Char p, k ≥ p: Banach E, F with A^k_{E,E;F} analytic nowhere and F not equivalently nonarchimedean | proved | Challenges/Thm6_1a.lean | Solutions/Thm6_1a.lean | `exists_banach_counterexample_full` (MainTheorem.lean) | The library theorem is stronger. K is not assumed complete. |
| Thm6_1b | Theorem 6.1(2) (p. 15) | K complete, not spherically complete, char p: nonarchimedean Banach E, D with scalar A^k analytic nowhere | not_proved | Challenges/Thm6_1b.lean | — | — | Sequence-space form in ℓ^∞(Λ,K^n) with Λ countable. Depends on Appendix F. |
| Cor6_2 | Corollary 6.2 (p. 15) | Alt^k is C^∞ on hom spaces, and analytic iff k! ≠ 0; also on Banach spaces | proved | Challenges/Cor6_2.lean | Solutions/Cor6_2.lean | `contDiff_alternatingMapAction`, `cpolynomialAt_alternatingMapAction_of_factorial_ne_zero` (AlternatingActionRegularity.lean), `factorial_ne_zero_iff_allBanachPrecompositionAnalytic` (FactorialClassification.lean) | Stated in hom coordinates. The power-series form is stated; it agrees here with the paper's C^ω reading. |
| Thm6_3 | Theorem 6.3 (p. 16) | Alt^k(−;K) analytic on all hom spaces iff k! ≠ 0 or K spherically complete | partially_proved | Challenges/Thm6_3.lean | — | "if" half: `cpolynomialAt_compContinuousLinearMapCLM` (FactorialInvertible.lean), `analyticAt_compContinuousLinearMapCLM_of_sphericallyComplete` (SphericalAnalytic.lean) | The "if" half (`analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete`) was proved in a scratch file. The "only if" halves need Thm6_1b. |
| Prop6_4 | Proposition 6.4 (p. 16) | Shear g(u)(d,e) = (d+ue, e): g and g⁻¹ affine analytic, u ↦ g(u)^* not analytic at u0 | proved | Challenges/Prop6_4.lean | Solutions/Prop6_4.lean | `analyticAt_shear`, `analyticAt_shear_inverse`, `not_analyticAt_shear_pullback` (Analysis/ShearCounterexample.lean) | H = D × E with the max norm. |
| Prop6_4_bundle | Proposition 6.4, bundle paragraph (p. 16) | Analytic trivial bundle whose induced Alt^k(H;F) atlas is not analytic | partially_proved | Challenges/Prop6_4_bundle.lean | — | E = D, u0 = 0 only: `shearBundleCore`, `not_contMDiffVectorBundle_alternating_shearBundle` (Geometry/AlternatingBundleShearCounterexample.lean) | General E ≠ D and arbitrary u0 are missing. Encoded as a Bool-indexed VectorBundleCore. |
| Prop6_5 | Proposition 6.5 (p. 17) | Two analytic charts with nowhere-analytic transition on Alt^k; pullback h^*ω0 analytic into Mult but not Alt | not_proved | Challenges/Prop6_5.lean | — | — | The manifold is the model space itself. Depends on Thm6_1b. |

## Section 7

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Thm7_2 | Theorem 7.2 (pp. 18-19) | Ambient analytic forms: sheaf of graded algebras with pullback, ∧, d; d² = 0, Leibniz | not_proved | Challenges/Thm7_2.lean | — | — | 18 theorems, chart level only (Mathlib has no forms on manifolds). wedge and extDeriv are defined in the file. |
| Prop7_3 | Proposition 7.3 (p. 19) | Intrinsic ⇒ ambient analytic; with a retraction or finite coordinates the cotangent atlas is analytic and sections agree | partially_proved | Challenges/Prop7_3.lean | — | `part3_manifold`: `contMDiffVectorBundle_alternating_of_finiteCoordinates` (Geometry/AnalyticAlternatingBundle.lean); ingredient `contDiff_compContinuousLinearMapCLM_of_retraction` (SphericalAnalytic.lean:435) | [^prop73] |

[^prop73]: `part3_manifold` is an exact library term. `part2_manifold` would follow by glue through `analyticAt_alternatingMapAction_of_precomposition` and `contMDiffVectorBundle_alternating_of_family`. The section-equivalence clauses and part 1 have no library declaration; part 1 is a trivial composition with a CLM. The chart-level atlas clause quantifies over all C^ω ψ.

## Section 9

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| Sec9_zeroDual | Section 9, "Which fibers remove the obstruction?" (p. 23) | Over complete non-spherically-complete char p K, k ≥ p, every universal target has zero dual | not_proved | Challenges/Sec9_zeroDual.lean | — | — | The compression step exists (`UniversalAlternatingTarget.of_retract`, UniversalAlternatingTargets.lean:212). The missing input is Thm6_1b. |

## Appendices A-B

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| LemA_1 | Lemma A.1 (p. 24) | One-variable uniqueness of a bounded power series summing to 0 | proved | Challenges/LemA_1.lean | Solutions/LemA_1.lean | Mathlib only: `HasFPowerSeriesAt.apply_eq_zero` | No completeness. Convergence is read as partial sums. |
| LemA_2 | Lemma A.2 (p. 24) | A normed field of characteristic p > 0 is nonarchimedean | proved | Challenges/LemA_2.lean | Solutions/LemA_2.lean | `charP_isUltrametricDist` (Analysis/PositiveCharacteristic.lean) | Primality is derived from 0 < p. |
| LemA_3 | Lemma A.3 (pp. 24-25) | Finite-dimensional spaces over complete K: linear functionals are bounded and U is complete | proved | Challenges/LemA_3.lean | Solutions/LemA_3.lean | Mathlib only: `LinearMap.toContinuousLinearMap`, `FiniteDimensional.complete` | Two parts. |
| LemB_2 | Lemma B.2 (p. 26) | The determinant array Ω on Λ^k V is injective | proved | Challenges/LemB_2.lean | Solutions/LemB_2.lean | `determinantArraySubmodule_injective` (Algebra/DeterminantArray.lean) | part0 shows such an Ω exists. hk is unused. |
| LemB_3 | Lemma B.3 (p. 26) | Flattening rank ≤ sdim(ω) | proved | Challenges/LemB_3.lean | Solutions/LemB_3.lean | `exteriorFlattening_rank_le` (Algebra/ExteriorFlattening.lean), `exteriorSupportDim_attained` | sdim is defined in the file and bridged to the library's. |
| LemB_4 | Lemma B.4 (p. 27) | Contractions c_φ: cofactor formula, c_φ(Λ^k W) ⊆ W, dim span ≤ sdim | proved | Challenges/LemB_4.lean | Solutions/LemB_4.lean | `exteriorLastContraction`, `exteriorContractionSpan_finrank_le` (Algebra/ExteriorContraction.lean) | k = n+1. Part 3 also asserts the span is finite-dimensional. |
| PropB_5 | Proposition B.5 (p. 27) | Canonical exterior support S(ω): smallest supporting subspace, sdim = dim S(ω) | proved | Challenges/PropB_5.lean | Solutions/PropB_5.lean | `mem_exteriorPowerSubmodule_iff_contractionSpan_le`, `exteriorSupportDim_eq_finrank_contractionSpan` (Algebra/CanonicalExteriorSupport.lean) | Degree 0 and degree 1 remarks are omitted. |
| LemB_6 | Lemma B.6 (p. 28) | Identity principle for vector polynomials over an infinite field | proved | Challenges/LemB_6.lean | Solutions/LemB_6.lean | `VectorPolynomial.coeff_eq_zero_of_sum_eq_zero` (Algebra/PolynomialIdentity.lean) | Direct `exact`. |
| LemB_7 | Lemma B.7 (p. 28) | A homogeneous form of degree e ≤ q vanishing on F_q^m is zero | proved | Challenges/LemB_7.lean | Solutions/LemB_7.lean | `finiteField_homogeneous_extension_eq_zero` (Algebra/FiniteHomogeneousIdentity.lean) | Direct `exact`. |
| PropB_8 | Proposition B.8 (p. 29) | Pointwise vs polarized lifts: implications and counterexamples | proved | Challenges/PropB_8.lean | Solutions/PropB_8.lean | `sum_perm_eq_of_multiplier_diagonal` (Algebra/Polarization.lean), `PolarizationCounterexamples.exists_pw_not_pol`, `exists_pol1_not_pw` | "Not in general" is read as an existential. |
| ThmB_9 | Theorem B.9 (p. 30) | No bounded-support multiplier lift over a finite field when k! = 0 | proved | Challenges/ThmB_9.lean | Solutions/ThmB_9.lean | `finiteField_multiplier_obstruction(_full, _finsupp)` (Algebra/FiniteFieldObstruction.lean) | Part (2) is split into E0 = V and E0 = V_fin. |
| LemB_10 | Lemma B.10 (pp. 30-31) | Infinite pattern-homogeneous subset (Ramsey) | proved | Challenges/LemB_10.lean | Solutions/LemB_10.lean | `OrderPattern.exists_infinite_order_homogeneous` (Algebra/OrderPattern.lean) | "Same pattern" uses the paper's comparison characterization. |
| LemB_11 | Lemma B.11 (p. 32) | Output-free clusters cancel: Ω_{Ψ(u;v)}(c) = χ | proved | Challenges/LemB_11.lean | Solutions/LemB_11.lean | `cluster_family_cancellation_of_intervals` (Algebra/ClusterCancellation.lean) | [^b1113] |
| LemB_12 | Lemma B.12 (pp. 32-33) | Staircase: χ(τ) = χ(τ') under an adjacent exchange | proved | Challenges/LemB_12.lean | Solutions/LemB_12.lean | `clusterValue_adjacent_eq` (Algebra/ClusterStaircase.lean) | [^b1113] |
| LemB_13 | Lemma B.13 (p. 33) | Diagonal: Σ_τ χ(τ) = 1 | proved | Challenges/LemB_13.lean | Solutions/LemB_13.lean | `sum_clusterValue_order_eq_one` (Algebra/ClusterDiagonal.lean) | [^b1113] |
| RemB_15 | Remark B.15 (p. 34) | k! invertible: normalized lift is alternating, (Pol1), sdim ≤ k², cluster value 1/k! | proved | Challenges/RemB_15.lean | Solutions/RemB_15.lean | `normalizedMultiplierLift` and lemmas (Algebra/NormalizedMultiplierLift.lean) | Defined on V instead of V_fin, which is stronger. The commentary sentences and the (5,3) example are not formalized. |

[^b1113]: The paper's ambient hypotheses (a)-(c) together with k! = 0 are contradictory, so each lemma keeps only the hypotheses its proof uses. This keeps the statements from being vacuous. The cluster definitions are shared across B.11-B.13.

## Appendix C

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| ThmC_1 | Theorem C.1 (p. 35) | Over κ((X)), A^k into B has no bounded lift, hence is analytic nowhere | proved | Challenges/ThmC_1.lean | Solutions/ThmC_1.lean | `laurent_not_hasBoundedLift`, `laurent_not_analyticAt` (Analysis/LaurentResidueLift.lean) | HasBoundedKLinearLift is defined in the file. |
| LemC_2 | Lemma C.2 (pp. 35-36) | ‖·‖_π is a norm; Ω injective with ‖Ω‖ ≤ 1; completion B, J, W_B | proved | Challenges/LemC_2.lean | Solutions/LemC_2.lean | `projectiveExterior_properties`, `projectiveExteriorCompletion_properties` (Analysis/ProjectiveExterior.lean) | projNorm is defined in the file and proved equal to the library seminorm. |
| PropC_3 | Proposition C.3 (pp. 36-37) | Unique η(b) with Ω(η b) = coeff₀(J b), κ-linear, sdim ≤ k M_r ‖b‖ | proved | Challenges/PropC_3.lean | Solutions/PropC_3.lean | `completedLaurentCoefficient_*` (Analysis/LaurentCompletedCoefficient.lean) | Ω^κ is quantified (its existence is LemB_2). M_r is defined in the file. |
| LemC_4 | Lemma C.4 (pp. 37-38) | The coefficient lift Ψ is 2k-linear, alternating, sdim-bounded, (Pol) and (Pol1) | proved | Challenges/LemC_4.lean | Solutions/LemC_4.lean | `laurentResidueLift_*` (Analysis/LaurentResidueLift.lean, LaurentResiduePolarization.lean) | (Ψ1)-(Ψ4) and (Pol1) are bundled in one theorem. |
| PropC_6 | Proposition C.6 (p. 39) | Multipliers on c0: σ has no bounded lift; a ↦ A(u0 + D_a) is analytic nowhere | not_proved | Challenges/PropC_6.lean | — | — | No library result about lifts over a c0 base. |
| CorC_7 | Corollary C.7 (pp. 39-40) | Diagonal transitions over a c0 base: analytic isometric bundle with non-analytic Alt^k atlas | not_proved | Challenges/CorC_7.lean | — | — | Explicit-map form, not a bundle statement. Part 2 is PropC_6 part 2 at u0 = id. |
| CorC_8 | Corollary C.8 (p. 40) | Over F_q((u)), k ≥ p: the alternating construction preserves bundles over P iff dim P < ∞ | partially_proved | Challenges/CorC_8.lean | — | "if" half: `contMDiffVectorBundle_alternating_of_finiteCoordinates`, `alternatingBundleHom_of_finiteCoordinates` + `ContinuousLinearEquiv.ofFinrankEq` | The "if" half is about 8 lines of glue, recorded in the docstring. The "only if" half needs Serre's orthonormal-basis theorem and PropC_6. |

## Appendices D-E

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| LemD_1 | Lemma D.1 (pp. 40-41) | Complete ultrametric space with distances in r^ℤ ∪ {0} is spherically complete | proved | Challenges/LemD_1.lean | Solutions/LemD_1.lean | `sphericallyCompleteSpace_of_discreteDist_radius` (Analysis/DiscreteSphericalCompleteness.lean) | None of substance. |
| LemD_2 | Lemma D.2 (p. 41) | Laurent subfield: nonarchimedean, norm of Laurent polynomials, isometric ev_t, image spherically complete | partially_proved | Challenges/LemD_2.lean | — | `charP_isUltrametricDist`, `exists_isometric_laurentField_embedding` (Analysis/LaurentSubfield.lean), `laurentField_range_properties` | [^lemd2] |
| ThmD_3 | Theorem D.3 (p. 42) | Ingleton's extension theorem | proved | Challenges/ThmD_3.lean | Solutions/ThmD_3.lean | `exists_extension_of_sphericallyComplete` (Analysis/SphericalCompleteness.lean) | K1 is nontrivially normed (from (H1)), so the trivially normed case is not covered. |
| CorD_4 | Corollary D.4 (p. 42) | Ingleton projection ϖ : K' → K1 with ϖ\|K1 = id, \|ϖ λ\| ≤ \|λ\| | proved | Challenges/CorD_4.lean | Solutions/CorD_4.lean | `exists_scalar_projection` (Analysis/ScalarProjection.lean) | K1 ⊆ K' is a NormedAlgebra. |
| LemD_5 | Lemma D.5 (p. 42) | Unique bounded extension of linear and multilinear maps from dense subspaces | proved | Challenges/LemD_5.lean | Solutions/LemD_5.lean | `denseLinearExtension` (DenseMultilinearExtension.lean), `exists_denseMultilinearFamilyExtension_of_bound` | Any nontrivially normed field, which is more general. |
| LemD_6 | Lemma D.6 (p. 43) | Projective base change: bounds, K'-norm, isometric ι_V, contraction Π_V | proved | Challenges/LemD_6.lean | Solutions/LemD_6.lean | `baseChangeSeminorm_*` (Analysis/ProjectiveBaseChange.lean, CompletedBaseChange.lean), `denseLinearExtension` | Every completion is quantified. V and K' share one universe. |
| LemD_7 | Lemma D.7 (p. 44) | Base change of operators f ↦ f_{K'}, ‖f_{K'}‖ ≤ ‖f‖, K1-linear | proved | Challenges/LemD_7.lean | Solutions/LemD_7.lean | `baseChangeOperatorAlgebraic`, `norm_completedBaseChangeOperator_le` (BaseChangeOperators.lean) | One universe. The extra IsUltrametricDist K1 follows from (H2). |
| LemD_8 | Lemma D.8 (pp. 44-45) | Base change of alternating forms m ↦ m_{K'} | proved | Challenges/LemD_8.lean | Solutions/LemD_8.lean | `baseChangeAlternatingForms` (BaseChangeAlternatingForms.lean) | The library does not need F1 complete, so it is stronger. |
| PropD_9 | Proposition D.9 (p. 45) | Descent of a lift from K' to K1; nowhere-analyticity ascends | proved | Challenges/PropD_9.lean | Solutions/PropD_9.lean | `exists_baseChangeLiftDescent`, `not_analyticAt_completedBaseChange_of_not_analyticAt` (BaseChangeLiftDescent.lean) | A local norm instance is used for the lift space. |
| LemD_11 | Lemma D.11 (p. 46) | Over incomplete K, the map spaces and lifts agree with those over K̂ | proved | Challenges/LemD_11.lean | Solutions/LemD_11.lean | `denseScalarLinearEquiv`, `denseScalarAlternatingEquiv` (DenseScalarRestriction.lean), `denseScalarLiftTransport` | K̂ is an abstract complete dense extension. Equalities are isometric equivalences. |
| PropE_1 | Proposition E.1 (pp. 46-47) | B (and F = B⊗̂K') has no equivalent nonarchimedean norm | proved | Challenges/PropE_1.lean | Solutions/PropE_1.lean | `norm_laurentBlockWedge` (LaurentBlockNorms.lean), `laurentExterior_not_hasEquivalentUltrametricNorm`, `HasLinearUnitSumGrowth.not_hasEquivalentUltrametricNorm` | Six theorems. |
| RemE_2 | Remark E.2 (p. 48) | K1 = K̂ case: base change is trivial; direct F_q((u)) route to Theorem 6.1(1) | partially_proved | Challenges/RemE_2.lean | — | part 3: `laurent_not_analyticAt`, `laurentExterior_not_hasEquivalentUltrametricNorm` | Parts 1-2 are missing: surjectivity of ι_V when K1 = K', and the ultrametric base change of ℓ^∞. |

[^lemd2]: Part (1) follows from the library with short glue (checked in scratch). Part (2) is missing: the library has only nonnegative exponents (`norm_polynomial_eval₂_eq_laurent`). Parts (3)-(4) are missing the HasSum evaluation formula and the identification of the image with closure(Subfield.closure {t}).

## Appendix F

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| ThmF_1 | Theorem F.1 (p. 48) | K complete, not spherically complete, k! = 0: nonarchimedean Banach E, E' with scalar A^k analytic nowhere | not_proved | Challenges/ThmF_1.lean | — | — | Abstract and sequence-space forms. No CharP or ultrametric hypothesis. |
| LemF_2 | Lemma F.2 (pp. 48-49) | Bounded d-linear forms on ℓ^∞(I,K) are sums of null arrays; tail property; diagonal → 0 | not_proved | Challenges/LemF_2.lean | — | — | e_i = `lp.single`. Three theorems. |
| LemF_3 | Lemma F.3 (pp. 49-50) | Chain gap in the word tree L^{<ω} | not_proved | Challenges/LemF_3.lean | — | — | Purely combinatorial, Mathlib only. |
| LemF_4 | Lemma F.4 (p. 50) | Finite fibre obstruction: no k-linear τ meets both conditions | not_proved | Challenges/LemF_4.lean | — | — | Finite linear algebra over κ, Mathlib only. |
| LemF_5 | Lemma F.5 (p. 51) | Finite test certificate with threshold 1 | not_proved | Challenges/LemF_5.lean | — | — | Adds the standing k! = 0, which the statement needs. |

## Appendix G

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| PropG_1 | Proposition G.1 (p. 54) | Homogeneous reflection in degree n ⟺ Δ_n(P) is complemented in T_n(P) | proved | Challenges/PropG_1.lean | Solutions/PropG_1.lean | `homogeneous_reflection_iff_projection` (Analysis/HomogeneousTensorReflection.lean:181), `exists_diagonal_lift_of_projection` | In part 1, targets are in Type u; part 2 allows any universe. |
| ThmG_3 | Theorem G.3 (pp. 54-55) | Universal analytic reflection ⟺ projections R_n with limsup ‖R_n‖^{1/n} < ∞ | proved | Challenges/ThmG_3.lean | Solutions/ThmG_3.lean | `universal_analytic_reflection_iff_tensor_projections` (Analysis/UniversalAnalyticReflection.lean:309), `analyticAt_subtype_of_tensor_projections` | The limsup is in ENNReal. Part 2 allows targets in any universe. |
| PropG_4 | Proposition G.4 (p. 55) | For l1(I,K), the infimum of projection norms is n!, so no universal analytic reflection | not_proved | Challenges/PropG_4.lean | — | — | Ingredient: `exists_l1_diagonal_lift` (Analysis/L1PolynomialLift.lean:140) for the upper bound. |
| CorG_5 | Corollary G.5 (pp. 55-56) | A map analytic into Z, C^∞ into W, not analytic into W, and a limit of entire polynomials | not_proved | Challenges/CorG_5.lean | — | — | Only the "analytic into Z" clause exists (`tensorTestMap_analyticOnNhd`, Analysis/TensorTestFamily.lean:202). |

## Appendix H

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| LemH_3 | Lemma H.3 (p. 57) | Split destinations give analytic actions; split pairs form an analytic domain | proved | Challenges/LemH_3.lean | Solutions/LemH_3.lean | `alternatingFunctor_analyticOnNhd_hom_of_split_destination`, `splitPairs_isAnalyticDomain` (Category/AnalyticDomains.lean) | The challenge imports the proving module for definitions (disclosed). |
| ThmH_4 | Theorem H.4 (p. 57) | Over F_p(t), k ≥ p: no largest full analytic domain (four variants plus witnesses) | proved | Challenges/ThmH_4.lean | Solutions/ThmH_4.lean | `DeterminantPair.Padding.no_largest_full_analytic_domain` (Category/NoLargestAnalyticDomain.lean) | part1 is the existing comparator statement `no_largest_full_analytic_domain_charP`. |
| LemH_5 | Lemma H.5 (p. 58) | Rigidity of E: endomorphisms are scalars, dual is zero | proved | Challenges/LemH_5.lean | Solutions/LemH_5.lean | `RigidDenseSource.existsUnique_scalar`, `dual_eq_zero` (Analysis/RigidDenseSourceGeneric.lean) | Assumes only that the a_i are independent, so it is at least as strong. |
| LemH_6 | Lemma H.6 (p. 58) | Every bounded p-linear map D^p → G is alternating; (D,G) is split | partially_proved | Challenges/LemH_6.lean | — | fixed scalars only: `DeterminantPair.all_multilinear_maps_alternating` (Analysis/DeterminantPairAllAlternating.lean), `isSplit_unpaddedD` | Missing: an arbitrary jointly independent family. The library proves it only at `DeterminantPair.z p r`. |
| LemH_7 | Lemma H.7 (p. 59) | Degree-one part of C_0 is zero | proved | Challenges/LemH_7.lean | Solutions/LemH_7.lean | `DeterminantQuadratic.homogeneous_linear_eq_zero` (Algebra/DeterminantQuadraticGap.lean) | Purely algebraic; uses RatFunc (ZMod p). |

## Appendix I

| ID | Paper reference (page) | Claim (one line) | Status | Challenge file | Solution file | Proved by | Deviations / notes |
|---|---|---|---|---|---|---|---|
| PropI_1 | Proposition I.1 (pp. 61-62) | K complete nonarchimedean, E or D of countable type: scalar A^k analytic in every degree | partially_proved | Challenges/PropI_1.lean | — | overlapping case: `analyticAt_of_orthogonalSchauderBasis` (Analysis/SortedBasisAnalytic.lean) | [^propi1] |
| PropI_2 | Proposition I.2 (pp. 62-63) | A continuous algebraic polynomial on c0 has a bounded lift with ‖q‖ ≤ C_{K,n}‖p‖_diag | not_proved | Challenges/PropI_2.lean | — | — | Ingredients only: `CZero.boundedArrayMultilinearMap` (Analysis/CZeroCoordinates.lean). |
| RemI_3 | Remark I.3 (p. 63) | A weighted, non-spherically-complete norm on c0 with analytic precomposition | not_proved | Challenges/RemI_3.lean | — | — | 8 parts. The weighted norm is given through a model predicate plus an existence part. |

[^propi1]: The library covers sources with a 1-orthogonal unconditional Schauder basis. That case overlaps the claim but is not a sub-case of it. Missing: the ultrametric hull, van der Put's t-orthogonal basis theorem, and the whole target-side case (part 2).

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

## Not yet proved: what is missing

This section covers the 13 partially_proved claims, the 17 not_proved claims and the one statement_pending claim, grouped by what a proof would need. Within a group, the order is the order in which the proofs depend on each other.

1. **The scalar counterexample chain.** This is the largest gap, and it blocks most of Section 6's negative side.
   LemF_3 (chain gap), LemF_4 (fibre obstruction), LemF_5 (test certificate) and LemF_2 (multilinear tails) → ThmF_1 → Thm6_1b → Thm6_3 "only if" halves, Prop6_5, Sec9_zeroDual.
   LemF_3 and LemF_4 are pure Mathlib combinatorics and linear algebra, so they are the natural place to start.
2. **The c0-base obstruction.** PropC_6 → CorC_7 (part 2 is PropC_6 part 2 at u0 = id) → CorC_8 "only if" half, which also needs Serre's orthonormal-basis theorem for nonarchimedean Banach spaces with an equivalent ultrametric norm.
3. **Manifold-level calculus.** Thm7_2 needs only chart-level analysis (wedge and d are already defined in the file). For Prop7_3: `part3_manifold` is an exact library term, and `part2_manifold` is glue. The section-equivalence clauses need Thm7_2's notion of ambient analytic forms.
4. **General bundle lifting.** Thm2_1 first needs a formal statement: definitions of C^n mixed-variance functors and bundle categories VB^n_K(M). Cor4_6's two spherical theorems need the transfer from a fiber norm that is only equivalent to a spherically complete ultrametric norm. Prop6_4_bundle needs the coordinate-change computation redone for L(E,D) with general u0.
5. **Exterior-power representation and duality tests.** Prop5_1 needs the universal property of Λ^k_π (the library has only the seminorm). Thm5_2 needs bidual and duality-test results; none exist.
6. **Descent in Sections 2-3.**
   - Prop2_2 parts 1-2: the (k+1)-linear representative on full multilinear inputs. Mathlib's `compContinuousLinearMapContinuousMultilinear` makes this routine.
   - Thm3_1 part 2: the coefficient criterion for a general closed isometry.
   - Lem3_2: the open-set ContDiffOn induction.
   - Prop3_3: the TFAE for a general a : H → W, using `coeff_eq_of_ambient` and `map_diag_add_smul`.
7. **The Laurent subfield and base-change remarks.** LemD_2 parts (2)-(4): negative exponents, the HasSum evaluation formula, and the image equal to closure(Subfield.closure {t}). RemE_2 parts 1-2: ι_V is an isometric iso when K1 = K', and the base change of ℓ^∞ is ultrametric.
8. **Tensor reflection for l1.** PropG_4 (T_n(l1) = l1(I^n), the sorted-orbit projection, the n! lower bound) → CorG_5 (also needs C^∞ reflection for the test map and the polynomial approximation).
9. **Determinant pair for general scalars.** LemH_6 needs to be redone for an arbitrary jointly independent family, not only `DeterminantPair.z p r`.
10. **Appendix I.**
    - PropI_1: the ultrametric hull, van der Put's basis theorem, and the target-side case.
    - PropI_2: finiteness of ‖p‖_diag and the Vandermonde interpolation bound.
    - RemI_3: the weighted-norm facts, then `analyticAt_of_equivalentUltrametricNorm_discreteValueGroup` for the analytic parts.

## Verification record (2026-10-08)

Checked on macOS against library commit f85751e (Lean v4.34.0-rc2, Mathlib fork pin 2b73d98), in a clean export of the repository:

- `lake build Challenges Solutions Partial`: completed successfully (3437 jobs). All 76 challenge files elaborate (only `sorry` warnings); all 45 solution files and `Partial/Cor4_6.lean` compile.
- `#print axioms` for all 101 theorems of the 45 solution files: each depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Statement identity: for each of the 45 pairs, `#check @<theorem>` (with `set_option pp.all true`) for every theorem and `#print` for every definition were run once importing `Challenges.<ID>` and once importing `Solutions.<ID>`; the outputs are identical for all 45 pairs. (For `LemH_7` this required giving the challenge the same imports as the solution; see its docstring.)
- The comparator was not run on the new pairs. The existing six-statement challenge was accepted by comparator revision 19e111e on 2026-10-08 (see README).
