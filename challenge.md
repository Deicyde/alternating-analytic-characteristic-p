# Claim ledger

This file lists the formalized claims of *Alternating bundles and analytic descent* ([paper/charp.pdf](paper/charp.pdf), 67 pages), each with its Lean statement and proof: every theorem, proposition, lemma and corollary other than Proposition 6.6, together with three remarks and two unnumbered statements. All 76 claims are proved. Proposition 6.6 has a written proof only.

Each claim has an ID, such as `Thm4_4` for Theorem 4.4. `Challenges/<ID>.lean` states the claim with `sorry`; its docstring quotes the paper and lists how the Lean statement differs from it. `Solutions/<ID>.lean` repeats the same statement and proves it from the library. `Challenges/<ID>.json` is a [comparator](https://github.com/leanprover/comparator) config for the pair. A result with several parts has one theorem per part.

To check a claim, run `python3 scripts/check_claim.py <ID>`. It confirms that the challenge's code is unchanged since the ledger was created (git tag `ledger-base`; for `Thm2_1`, since commit `7c9f61c`, which first stated it), builds both files, checks that the proof uses only `propext`, `Classical.choice` and `Quot.sound`, and checks that the two files state the same theorem.

Unless a row says otherwise, the degree of the alternating maps is `Fin k`. Paths in the "Proved by" column are relative to `AlternatingAnalytic/`.

## Sections 2-3

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| Thm2_1 | Theorem 2.1 (pp. 4-5) | Fiberwise application lifts C^n mixed-variance functors to functors on C^n bundle categories | [statement](Challenges/Thm2_1.lean), [proof](Solutions/Thm2_1.lean) | `FunctorLifting.liftCore_isContMDiff`, `FunctorLifting.contMDiff_liftHom`, `FunctorLifting.contMDiff_liftApp` (Bundle/FunctorLifting/); the functor is assembled in the solution file | Statement written during formalization. Variables grouped by variance; canonical trivializations; independence of the cover not stated. |
| Prop2_2 | Proposition 2.2 (p. 6) | The ambient action g∘m∘(f,…,f) is a bounded (k+1)-linear diagonal, analytic, with values in Alt^k | [statement](Challenges/Prop2_2.lean), [proof](Solutions/Prop2_2.lean) | `exists_ambientMultilinearAction_rep`, `contDiff_ambientMultilinearAction` (Descent/AmbientAction.lean) | k = 0 allowed. The norm bound ‖H‖ ≤ 1 is not stated. Part 4 phrases the closed subspace via the range of `toContinuousMultilinearMap`. |
| Thm3_1 | Theorem 3.1 (p. 7) | Coefficient descent: diagonals lie in j(W); f analytic iff the coefficients lift with a geometric bound | [statement](Challenges/Thm3_1.lean), [proof](Solutions/Thm3_1.lean) | `CoefficientCriterion.analyticAt_iff` (Descent/CoefficientCriterion.lean) | Open set U dropped. Coefficients as a `FormalMultilinearSeries`, bounds as `BddAbove`, convergence as `HasSum`. |
| Lem3_2 | Lemma 3.2 (p. 8) | f is C^n on open U iff j∘f is C^n | [statement](Challenges/Lem3_2.lean), [proof](Solutions/Lem3_2.lean) | `contDiffOn_iff_comp_linearIsometry` (Descent/SmoothDescentOn.lean) | Open-set `ContDiffOn` version, n : ℕ∞, no completeness. |
| Prop3_3 | Proposition 3.3 (p. 8) | One lift, every base point: analytic somewhere ⟺ bounded lift ⟺ polynomial everywhere; dichotomy for A^k | [statement](Challenges/Prop3_3.lean), [proof](Solutions/Prop3_3.lean) | `OneLift.tfae`, `OneLift.precomposition_polynomial_or_nowhereAnalytic` (Descent/OneLift.lean) | (3) as `HasFiniteFPowerSeriesOnBall` of infinite radius. k = 0 allowed (trivial). |


## Section 4

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| Prop4_1 | Proposition 4.1 (pp. 8-9) | A bounded retraction Alt→Mult gives a lift of norm ≤ ‖ρ‖; lifts exist if k! ≠ 0 or finite coordinates | [statement](Challenges/Prop4_1.lean), [proof](Solutions/Prop4_1.lean) | `contractingRetractionLift` (Analysis/SortedBasisLift.lean), `altProj` (Analysis/FactorialInvertible.lean), `finiteCoordinateDomainLift`, `finiteCoordinateCodomainLift` | Norm bound stated pointwise. Parts (1)-(2) are existence only. |
| Thm4_2 | Theorem 4.2 (pp. 9-10) | Spherically complete targets: Alt^k is ultrametric, spherically complete and retracts; A^k is a continuous polynomial | [statement](Challenges/Thm4_2.lean), [proof](Solutions/Thm4_2.lean) | `sphericallyCompleteSpace_continuousAlternatingMap`, `exists_contracting_retraction_toContinuousMultilinearMap`, `hasBoundedLift_of_sphericallyComplete` (Analysis/SphericalAnalytic.lean) | 4 parts. IsContinuousPolynomial is defined in the file. |
| Cor4_3 | Corollary 4.3 (p. 10) | Discrete value group: equivalent nonarchimedean Banach targets make A^k analytic | [statement](Challenges/Cor4_3.lean), [proof](Solutions/Cor4_3.lean) | `analyticAt_of_equivalentUltrametricNorm_discreteValueGroup` (Analysis/DiscreteTargetAnalytic.lean) | K need not be complete. |
| Thm4_4 | Theorem 4.4 (pp. 10-11) | Finite-coordinate parameters: f analytic iff j∘f is; coefficient bounds d^n (1 if Z ultrametric) | [statement](Challenges/Thm4_4.lean), [proof](Solutions/Thm4_4.lean) | `analyticAt_of_closed_linearIsometry_of_equiv` (Analysis/FiniteCoordinateReflection.lean), `FiniteCoordinateReflection.exists_lift`, `exists_hasFPowerSeriesOnBall_of_closed_linearIsometry_of_isUltrametricDist` | Parts 2-3 are for P = Fin d → K. "Analytic" is the Section 3 power-series notion. |
| Thm4_5a | Theorem 4.5(1) (pp. 11-12) | c0 parameters: j∘f analytic ⇒ f analytic, coefficients lift without norm increase; also on retracts | [statement](Challenges/Thm4_5a.lean), [proof](Solutions/Thm4_5a.lean) | `c0_analyticOn_linearIsometry`, `c0_exists_hasFPowerSeriesOnBall_linearIsometry`, `c0_analyticOnNhd_linearIsometry` (Analysis/CZeroReflection.lean) | The retract clause is stated for analyticity only; the paper's coefficient bound on a retract is not stated. It is proved by glue in the solution file, not by a library declaration. |
| Thm4_5b | Theorem 4.5(2) (pp. 11-12) | l1 parameters, fixed-degree representation: a∘γ analytic; also on retracts | [statement](Challenges/Thm4_5b.lean), [proof](Solutions/Thm4_5b.lean) | `analyticOn_comp_of_l1_fixed_degree_isometry`, `analyticOnNhd_comp_of_l1_fixed_degree_isometry` (Analysis/L1FixedDegreeReflection.lean) | The retract clause is proved by glue in the solution file. |
| Cor4_6 | Corollary 4.6 (p. 12) | Bundle theorem: Alt^k is an analytic bifunctor on bundles in six settings; C^n always | [statement](Challenges/Cor4_6.lean), [proof](Solutions/Cor4_6.lean) | existing bundle theorems + `BundleRows` glue (Geometry/BundleRows/) | Two theorems (objects, morphisms) per setting; functor laws not stated. Model 𝓘(K,P), no boundary. |


## Section 5

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| Prop5_1 | Proposition 5.1 (p. 13) | Alt^k(E;F) ≅ L(Λ^k_π E, F) isometrically and naturally | [statement](Challenges/Prop5_1.lean), [proof](Solutions/Prop5_1.lean) | `ExteriorRepresentation.exists_representation`, `exists_naturality` (Exterior/Representation/) | Λ^k_π E = separation quotient with the library seminorm. The isometry is stated as the existence of a `≃ₗᵢ` with Φ m ∘ ω_E = m. |
| Thm5_2 | Theorem 5.2 (p. 14) | Universal and scalar (bidual) tests for regularity of W : U → L(X,Y) | [statement](Challenges/Thm5_2.lean), [proof](Solutions/Thm5_2.lean) | `DualTests.part1_analytic` … `part3_contDiff` (Exterior/DualTests.lean) | Open U in a normed P. Analytic = `AnalyticOnNhd`, C^n = `ContDiffOn` with n : ℕ∞. Each "iff for every F" split into implications. |

## Section 6

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| Thm6_1a | Theorem 6.1(1) (p. 15) | Char p, k ≥ p: Banach E, F with A^k_{E,E;F} analytic nowhere and F not equivalently nonarchimedean | [statement](Challenges/Thm6_1a.lean), [proof](Solutions/Thm6_1a.lean) | `exists_banach_counterexample_full` (MainTheorem.lean) | The library theorem is stronger. K is not assumed complete. |
| Thm6_1b | Theorem 6.1(2) (p. 15) | K complete, not spherically complete, char p: nonarchimedean Banach E, D with scalar A^k analytic nowhere | [statement](Challenges/Thm6_1b.lean), [proof](Solutions/Thm6_1b.lean) | `ScalarObstruction` from `ChainSpaces.sequenceConclusion` (Scalar/ScalarObstruction.lean) | `[CharP K p]`, 0 < p. Sequence-space form in `lp (fun _ : Λ => Fin n → K) ∞`, Λ countable. |
| Cor6_2 | Corollary 6.2 (p. 16) | Alt^k is C^∞ on hom spaces, and analytic iff k! ≠ 0; also on Banach spaces | [statement](Challenges/Cor6_2.lean), [proof](Solutions/Cor6_2.lean) | `contDiff_alternatingMapAction`, `cpolynomialAt_alternatingMapAction_of_factorial_ne_zero` (Analysis/AlternatingActionRegularity.lean), `factorial_ne_zero_iff_allBanachPrecompositionAnalytic` (Analysis/FactorialClassification.lean) | Stated in hom coordinates. The power-series form is stated; it agrees here with the paper's C^ω reading. |
| Thm6_3 | Theorem 6.3 (p. 16) | Alt^k(−;K) analytic on all hom spaces iff k! ≠ 0 or K spherically complete | [statement](Challenges/Thm6_3.lean), [proof](Solutions/Thm6_3.lean) | `ScalarClassification.analytic_on_homs_iff'` and its Banach variants (Scalar/ScalarClassification/) | "Analytic on every hom space" = `AnalyticOnNhd` on univ. Three source categories. |
| Prop6_4 | Proposition 6.4 (pp. 16-17) | Shear g(u)(d,e) = (d+ue, e): g and g⁻¹ affine analytic, u ↦ g(u)^* not analytic at u0 | [statement](Challenges/Prop6_4.lean), [proof](Solutions/Prop6_4.lean) | `analyticAt_shear`, `analyticAt_shear_inverse`, `not_analyticAt_shear_pullback` (Analysis/ShearCounterexample.lean) | H = D × E with the max norm. |
| Prop6_4_bundle | Proposition 6.4, bundle paragraph (p. 17) | Analytic trivial bundle whose induced Alt^k(H;F) atlas is not analytic | [statement](Challenges/Prop6_4_bundle.lean), [proof](Solutions/Prop6_4_bundle.lean) | `shearBundle_realization` (Geometry/ShearBundleGeneral.lean) | Two-chart `VectorBundleCore` over L(E,D), general E, D and u₀. |
| Prop6_5 | Proposition 6.5 (pp. 17-18) | Two analytic charts with nowhere-analytic transition on Alt^k; pullback h^*ω0 analytic into Mult but not Alt | [statement](Challenges/Prop6_5.lean), [proof](Solutions/Prop6_5.lean) | `TangentPullback.tangent_obstruction_of_scalar_obstruction`, `pullback_obstruction_of_scalar_obstruction` (Scalar/TangentPullback/) | The manifold is the model space, with charts id and an analytic equivalence ψ. "Polynomial analytic" = `CPolynomialOn`. |

## Section 7

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| Thm7_2 | Theorem 7.2 (pp. 19-20) | Ambient analytic forms: sheaf of graded algebras with pullback, ∧, d; d² = 0, Leibniz | [statement](Challenges/Thm7_2.lean), [proof](Solutions/Thm7_2.lean) | `Forms` calculus (Forms/Calculus/) | Chart level only: open subsets of a normed space (Mathlib has no forms on manifolds). Degree identities stated pointwise via `finCongr`. |
| Prop7_3 | Proposition 7.3 (pp. 20-21) | Intrinsic ⇒ ambient analytic; with a retraction or finite coordinates the cotangent atlas is analytic and sections agree | [statement](Challenges/Prop7_3.lean), [proof](Solutions/Prop7_3.lean) | `analyticOnNhd_iff_toContinuousMultilinearMap_of_retraction`, `contMDiffVectorBundle_alternating_of_retraction` (Forms/Comparison/) | Atlas and section claims at chart level; the atlas claim also as `ContMDiffVectorBundle`. |


## Section 9

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| Sec9_zeroDual | Section 9, "Which fibers remove the obstruction?" (p. 25) | Over complete non-spherically-complete char p K, k ≥ p, every universal target has zero dual | [statement](Challenges/Sec9_zeroDual.lean), [proof](Solutions/Sec9_zeroDual.lean) | `UniversalAlternatingTarget.dual_eq_zero_of_scalar_obstruction` (Scalar/ZeroDual.lean) | Universal target = library `UniversalAlternatingTarget`. Zero dual = every CLM F → K is 0. |

## Appendices A-B

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| LemA_1 | Lemma A.1 (p. 27) | One-variable uniqueness of a bounded power series summing to 0 | [statement](Challenges/LemA_1.lean), [proof](Solutions/LemA_1.lean) | Mathlib only: `HasFPowerSeriesAt.apply_eq_zero` | No completeness. Convergence is read as partial sums. |
| LemA_2 | Lemma A.2 (p. 27) | A normed field of characteristic p > 0 is nonarchimedean | [statement](Challenges/LemA_2.lean), [proof](Solutions/LemA_2.lean) | `charP_isUltrametricDist` (Analysis/PositiveCharacteristic.lean) | Primality is derived from 0 < p. |
| LemA_3 | Lemma A.3 (p. 27) | Finite-dimensional spaces over complete K: linear functionals are bounded and U is complete | [statement](Challenges/LemA_3.lean), [proof](Solutions/LemA_3.lean) | Mathlib only: `LinearMap.toContinuousLinearMap`, `FiniteDimensional.complete` | Two parts. |
| LemB_2 | Lemma B.2 (p. 29) | The determinant array Ω on Λ^k V is injective | [statement](Challenges/LemB_2.lean), [proof](Solutions/LemB_2.lean) | `determinantArraySubmodule_injective` (Algebra/DeterminantArray.lean) | part0 shows such an Ω exists. hk is unused. |
| LemB_3 | Lemma B.3 (p. 29) | Flattening rank ≤ sdim(ω) | [statement](Challenges/LemB_3.lean), [proof](Solutions/LemB_3.lean) | `exteriorFlattening_rank_le` (Algebra/ExteriorFlattening.lean), `exteriorSupportDim_attained` | sdim is defined in the file and bridged to the library's. |
| LemB_4 | Lemma B.4 (p. 29) | Contractions c_φ: cofactor formula, c_φ(Λ^k W) ⊆ W, dim span ≤ sdim | [statement](Challenges/LemB_4.lean), [proof](Solutions/LemB_4.lean) | `exteriorLastContraction`, `exteriorContractionSpan_finrank_le` (Algebra/ExteriorContraction.lean) | k = n+1. Part 3 also asserts the span is finite-dimensional. |
| PropB_5 | Proposition B.5 (p. 30) | Canonical exterior support S(ω): smallest supporting subspace, sdim = dim S(ω) | [statement](Challenges/PropB_5.lean), [proof](Solutions/PropB_5.lean) | `mem_exteriorPowerSubmodule_iff_contractionSpan_le`, `exteriorSupportDim_eq_finrank_contractionSpan` (Algebra/CanonicalExteriorSupport.lean) | Degree 0 and degree 1 remarks are omitted. |
| LemB_6 | Lemma B.6 (p. 31) | Identity principle for vector polynomials over an infinite field | [statement](Challenges/LemB_6.lean), [proof](Solutions/LemB_6.lean) | `VectorPolynomial.coeff_eq_zero_of_sum_eq_zero` (Algebra/PolynomialIdentity.lean) | Direct `exact`. |
| LemB_7 | Lemma B.7 (p. 31) | A homogeneous form of degree e ≤ q vanishing on F_q^m is zero | [statement](Challenges/LemB_7.lean), [proof](Solutions/LemB_7.lean) | `finiteField_homogeneous_extension_eq_zero` (Algebra/FiniteHomogeneousIdentity.lean) | Direct `exact`. |
| PropB_8 | Proposition B.8 (pp. 31-32) | Pointwise vs polarized lifts: implications and counterexamples | [statement](Challenges/PropB_8.lean), [proof](Solutions/PropB_8.lean) | `sum_perm_eq_of_multiplier_diagonal` (Algebra/Polarization.lean), `PolarizationCounterexamples.exists_pw_not_pol`, `exists_pol1_not_pw` | "Not in general" is read as an existential. |
| ThmB_9 | Theorem B.9 (p. 33) | No bounded-support multiplier lift over a finite field when k! = 0 | [statement](Challenges/ThmB_9.lean), [proof](Solutions/ThmB_9.lean) | `finiteField_multiplier_obstruction(_full, _finsupp)` (Algebra/FiniteFieldObstruction.lean) | Part (2) is split into E0 = V and E0 = V_fin. |
| LemB_10 | Lemma B.10 (p. 33) | Infinite pattern-homogeneous subset (Ramsey) | [statement](Challenges/LemB_10.lean), [proof](Solutions/LemB_10.lean) | `OrderPattern.exists_infinite_order_homogeneous` (Algebra/OrderPattern.lean) | "Same pattern" uses the paper's comparison characterization. |
| LemB_11 | Lemma B.11 (p. 35) | Output-free clusters cancel: Ω_{Ψ(u;v)}(c) = χ | [statement](Challenges/LemB_11.lean), [proof](Solutions/LemB_11.lean) | `cluster_family_cancellation_of_intervals` (Algebra/ClusterCancellation.lean) | [^b1113] |
| LemB_12 | Lemma B.12 (pp. 35-36) | Staircase: χ(τ) = χ(τ') under an adjacent exchange | [statement](Challenges/LemB_12.lean), [proof](Solutions/LemB_12.lean) | `clusterValue_adjacent_eq` (Algebra/ClusterStaircase.lean) | [^b1113] |
| LemB_13 | Lemma B.13 (p. 36) | Diagonal: Σ_τ χ(τ) = 1 | [statement](Challenges/LemB_13.lean), [proof](Solutions/LemB_13.lean) | `sum_clusterValue_order_eq_one` (Algebra/ClusterDiagonal.lean) | [^b1113] |
| RemB_15 | Remark B.15 (p. 37) | k! invertible: normalized lift is alternating, (Pol1), sdim ≤ k², cluster value 1/k! | [statement](Challenges/RemB_15.lean), [proof](Solutions/RemB_15.lean) | `normalizedMultiplierLift` and lemmas (Algebra/NormalizedMultiplierLift.lean) | Defined on V instead of V_fin, which is stronger. The commentary sentences and the (5,3) example are not formalized. |

[^b1113]: Lemmas B.11–B.13 sit inside the proof by contradiction of Theorem B.9, whose hypotheses together with k! = 0 are inconsistent. Each Lean statement keeps only the hypotheses its own proof uses, so that it is not vacuous.

## Appendix C

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| ThmC_1 | Theorem C.1 (p. 37) | Over κ((X)), A^k into B has no bounded lift, hence is analytic nowhere | [statement](Challenges/ThmC_1.lean), [proof](Solutions/ThmC_1.lean) | `laurent_not_hasBoundedLift`, `laurent_not_analyticAt` (Analysis/LaurentResidueLift.lean) | HasBoundedKLinearLift is defined in the file. |
| LemC_2 | Lemma C.2 (p. 38) | ‖·‖_π is a norm; Ω injective with ‖Ω‖ ≤ 1; completion B, J, W_B | [statement](Challenges/LemC_2.lean), [proof](Solutions/LemC_2.lean) | `projectiveExteriorSeminorm_eq_iInf_wedgeCost`, `coordinateExteriorArray`, `completedExteriorArray`, `completedExteriorWedge` (Analysis/ProjectiveExterior.lean) | projNorm is defined in the file and proved equal to the library seminorm. |
| PropC_3 | Proposition C.3 (pp. 39-40) | Unique η(b) with Ω(η b) = coeff₀(J b), κ-linear, sdim ≤ k M_r ‖b‖ | [statement](Challenges/PropC_3.lean), [proof](Solutions/PropC_3.lean) | `completedLaurentCoefficient_*` (Analysis/LaurentCompletedCoefficient.lean) | Ω^κ is quantified (its existence is LemB_2). M_r is defined in the file. |
| LemC_4 | Lemma C.4 (pp. 40-41) | The coefficient lift Ψ is 2k-linear, alternating, sdim-bounded, (Pol) and (Pol1) | [statement](Challenges/LemC_4.lean), [proof](Solutions/LemC_4.lean) | `laurentResidueLift_*` (Analysis/LaurentResidueLift.lean, Analysis/LaurentResiduePolarization.lean) | (Ψ1)-(Ψ4) and (Pol1) are bundled in one theorem. |
| PropC_6 | Proposition C.6 (p. 42) | Multipliers on c0: σ has no bounded lift; a ↦ A(u0 + D_a) is analytic nowhere | [statement](Challenges/PropC_6.lean), [proof](Solutions/PropC_6.lean) | `CZeroMultipliers` (Laurent/CZeroMultipliers/) | Hypotheses of Theorem C.1 (κ finite, char p, k ≥ p). c₀ = `C₀(ℕ,K₁)`. |
| CorC_7 | Corollary C.7 (p. 42) | Diagonal transitions over a c0 base: analytic isometric bundle with non-analytic Alt^k atlas | [statement](Challenges/CorC_7.lean), [proof](Solutions/CorC_7.lean) | `DiagonalTransitions` (Laurent/DiagonalTransitions.lean) | Explicit-map form, not a `ContMDiffVectorBundle` statement. |
| CorC_8 | Corollary C.8 (pp. 42-43) | Over F_q((u)), k ≥ p: the alternating construction preserves bundles over P iff dim P < ∞ | [statement](Challenges/CorC_8.lean), [proof](Solutions/CorC_8.lean) | `FiniteDimSharp.IfHalf`, `FiniteDimSharp.OnlyIf` (Laurent/FiniteDimSharp/) | K = `LaurentField κ r` with κ finite. Bundle preservation is defined in the file. All types in one universe. |

## Appendices D-E

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| LemD_1 | Lemma D.1 (p. 43) | Complete ultrametric space with distances in r^ℤ ∪ {0} is spherically complete | [statement](Challenges/LemD_1.lean), [proof](Solutions/LemD_1.lean) | `sphericallyCompleteSpace_of_discreteDist_radius` (Analysis/DiscreteSphericalCompleteness.lean) | None of substance. |
| LemD_2 | Lemma D.2 (p. 44) | Laurent subfield: nonarchimedean, norm of Laurent polynomials, isometric ev_t, image spherically complete | [statement](Challenges/LemD_2.lean), [proof](Solutions/LemD_2.lean) | `norm_sum_zmod_zpow_eq`, `exists_laurentField_evaluation`, `sphericallyCompleteSpace_closure_subfieldClosure` (Analysis/LaurentSubfieldExtra/) | F_p((X)) = `LaurentField (ZMod p) r`. "Closure of F_p(t)" = closure of `Subfield.closure {t}`. Evaluation formula as `HasSum` over ℤ. |
| ThmD_3 | Theorem D.3 (p. 44) | Ingleton's extension theorem | [statement](Challenges/ThmD_3.lean), [proof](Solutions/ThmD_3.lean) | `exists_extension_of_sphericallyComplete` (Analysis/SphericalCompleteness.lean) | K1 is nontrivially normed (from (H1)), so the trivially normed case is not covered. |
| CorD_4 | Corollary D.4 (pp. 44-45) | Ingleton projection ϖ : K' → K1 with ϖ\|K1 = id, \|ϖ λ\| ≤ \|λ\| | [statement](Challenges/CorD_4.lean), [proof](Solutions/CorD_4.lean) | `exists_scalar_projection` (Analysis/ScalarProjection.lean) | K1 ⊆ K' is a NormedAlgebra. |
| LemD_5 | Lemma D.5 (p. 45) | Unique bounded extension of linear and multilinear maps from dense subspaces | [statement](Challenges/LemD_5.lean), [proof](Solutions/LemD_5.lean) | `denseLinearExtension` (Analysis/DenseMultilinearExtension.lean), `exists_denseMultilinearFamilyExtension_of_bound` | Any nontrivially normed field, which is more general. |
| LemD_6 | Lemma D.6 (pp. 45-46) | Projective base change: bounds, K'-norm, isometric ι_V, contraction Π_V | [statement](Challenges/LemD_6.lean), [proof](Solutions/LemD_6.lean) | `baseChangeSeminorm_*` (Analysis/ProjectiveBaseChange.lean, Analysis/CompletedBaseChange.lean), `denseLinearExtension` | Every completion is quantified. V and K' share one universe. |
| LemD_7 | Lemma D.7 (p. 46) | Base change of operators f ↦ f_{K'}, ‖f_{K'}‖ ≤ ‖f‖, K1-linear | [statement](Challenges/LemD_7.lean), [proof](Solutions/LemD_7.lean) | `baseChangeOperatorAlgebraic`, `norm_completedBaseChangeOperator_le` (Analysis/BaseChangeOperators.lean) | One universe. The extra IsUltrametricDist K1 follows from (H2). |
| LemD_8 | Lemma D.8 (pp. 46-47) | Base change of alternating forms m ↦ m_{K'} | [statement](Challenges/LemD_8.lean), [proof](Solutions/LemD_8.lean) | `baseChangeAlternatingForms` (Analysis/BaseChangeAlternatingForms.lean) | The library does not need F1 complete, so it is stronger. |
| PropD_9 | Proposition D.9 (p. 48) | Descent of a lift from K' to K1; nowhere-analyticity ascends | [statement](Challenges/PropD_9.lean), [proof](Solutions/PropD_9.lean) | `exists_baseChangeLiftDescent`, `not_analyticAt_completedBaseChange_of_not_analyticAt` (Analysis/BaseChangeLiftDescent.lean) | A local norm instance is used for the lift space. |
| LemD_11 | Lemma D.11 (pp. 48-49) | Over incomplete K, the map spaces and lifts agree with those over K̂ | [statement](Challenges/LemD_11.lean), [proof](Solutions/LemD_11.lean) | `denseScalarLinearEquiv`, `denseScalarAlternatingEquiv` (Analysis/DenseScalarRestriction.lean), `denseScalarLiftTransport` | K̂ is an abstract complete dense extension. Equalities are isometric equivalences. |
| PropE_1 | Proposition E.1 (pp. 49-50) | B (and F = B⊗̂K') has no equivalent nonarchimedean norm | [statement](Challenges/PropE_1.lean), [proof](Solutions/PropE_1.lean) | `norm_laurentBlockWedge` (Analysis/LaurentBlockNorms.lean), `laurentExterior_not_hasEquivalentUltrametricNorm`, `HasLinearUnitSumGrowth.not_hasEquivalentUltrametricNorm` | Six theorems. |
| RemE_2 | Remark E.2 (p. 50) | K1 = K̂ case: base change is trivial; direct F_q((u)) route to Theorem 6.1(1) | [statement](Challenges/RemE_2.lean), [proof](Solutions/RemE_2.lean) | `completedBaseChangeEmbedding_surjective_self` (Analysis/BaseChangeCompleteSelf.lean) | Part 1 generalized to every complete V. F_q((u)) = `LaurentField κ r`. |


## Appendix F

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| ThmF_1 | Theorem F.1 (p. 51) | K complete, not spherically complete, k! = 0: nonarchimedean Banach E, E' with scalar A^k analytic nowhere | [statement](Challenges/ThmF_1.lean), [proof](Solutions/ThmF_1.lean) | `ChainSpaces.abstractConclusion`, `ChainSpaces.sequenceConclusion` (Scalar/ChainSpaces/) | Abstract and sequence-space forms; ℓ^∞(Λ;K^n) = `lp`. Needs `maxSynthPendingDepth 2`. |
| LemF_2 | Lemma F.2 (pp. 51-52) | Bounded d-linear forms on ℓ^∞(I,K) are sums of null arrays; tail property; diagonal → 0 | [statement](Challenges/LemF_2.lean), [proof](Solutions/LemF_2.lean) | `Tails.multilinear_expansion`, `multilinear_tail`, `multilinear_diagonal_tendsto_zero` (Scalar/Tails/) | ℓ^∞(I,K) = `lp (fun _ : I => K) ∞`, e_i = `lp.single`. Ported from the author's earlier, unpublished characteristic-2 formalization. |
| LemF_3 | Lemma F.3 (p. 52) | Chain gap in the word tree L^{<ω} | [statement](Challenges/LemF_3.lean), [proof](Solutions/LemF_3.lean) | `ChainGap.labelChain_inter_subsingleton`, `iInter_nonempty_of_cofinite_on_chains` (Scalar/ChainGap.lean) | Λ = `List L`, extension = prefix; j-chains via `IsLabelChain`. |
| LemF_4 | Lemma F.4 (p. 53) | Finite fiber obstruction: no k-linear τ meets both conditions | [statement](Challenges/LemF_4.lean), [proof](Solutions/LemF_4.lean) | `FibreObstruction.not_exists_fibre_map` (Scalar/FibreObstruction.lean) | Algebraic alternating maps over κ, 0-based indices, δ′ = `Basis.det`. |
| LemF_5 | Lemma F.5 (p. 54) | Finite test certificate with threshold 1 | [statement](Challenges/LemF_5.lean), [proof](Solutions/LemF_5.lean) | `TestCertificate.exists_finite_test_certificate` (Scalar/TestCertificate.lean) | The hypothesis k! = 0 is `(k.factorial : K) = 0`. |

## Appendix G

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| PropG_1 | Proposition G.1 (pp. 56-57) | Homogeneous reflection in degree n ⟺ Δ_n(P) is complemented in T_n(P) | [statement](Challenges/PropG_1.lean), [proof](Solutions/PropG_1.lean) | `homogeneous_reflection_iff_projection` (Analysis/HomogeneousTensorReflection.lean:181), `exists_diagonal_lift_of_projection` | In part 1, targets are in Type u; part 2 allows any universe. |
| ThmG_3 | Theorem G.3 (p. 57) | Universal analytic reflection ⟺ projections R_n with limsup ‖R_n‖^{1/n} < ∞ | [statement](Challenges/ThmG_3.lean), [proof](Solutions/ThmG_3.lean) | `universal_analytic_reflection_iff_tensor_projections` (Analysis/UniversalAnalyticReflection.lean:309), `analyticAt_subtype_of_tensor_projections` | The limsup is in ENNReal. Part 2 allows targets in any universe. |
| PropG_4 | Proposition G.4 (p. 58) | For l1(I,K), the infimum of projection norms is n!, so no universal analytic reflection | [statement](Challenges/PropG_4.lean), [proof](Solutions/PropG_4.lean) | `L1Projection.sInf_norm_projection_eq_factorial`, `not_universalAnalyticReflection` (Tensor/L1Projection/) | ℓ¹ = `lp _ 1`. Infimum as a real `sInf`. Test targets in one universe. |
| CorG_5 | Corollary G.5 (pp. 58-59) | A map analytic into Z, C^∞ into W, not analytic into W, and a limit of entire polynomials | [statement](Challenges/CorG_5.lean), [proof](Solutions/CorG_5.lean) | `PolynomialApproximation.exists_smooth_nonanalytic_polynomial_limit` (Tensor/PolynomialApproximation/) | Z in the universe of P. Uniform convergence on every closed ball of radius < 1. |

## Appendix H

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| LemH_3 | Lemma H.3 (p. 60) | Split destinations give analytic actions; split pairs form an analytic domain | [statement](Challenges/LemH_3.lean), [proof](Solutions/LemH_3.lean) | `alternatingFunctor_analyticOnNhd_hom_of_split_destination`, `splitPairs_isAnalyticDomain` (Category/AnalyticDomains.lean) | The challenge imports, for its definitions, the library module that proves it. |
| ThmH_4 | Theorem H.4 (p. 60) | Over F_p(t), k ≥ p: no largest full analytic domain (four variants plus witnesses) | [statement](Challenges/ThmH_4.lean), [proof](Solutions/ThmH_4.lean) | `DeterminantPair.Padding.no_largest_full_analytic_domain` (Category/NoLargestAnalyticDomain.lean) | part1 is the existing comparator statement `no_largest_full_analytic_domain_charP`. |
| LemH_5 | Lemma H.5 (p. 61) | Rigidity of E: endomorphisms are scalars, dual is zero | [statement](Challenges/LemH_5.lean), [proof](Solutions/LemH_5.lean) | `RigidDenseSource.existsUnique_scalar`, `dual_eq_zero` (Analysis/RigidDenseSourceGeneric.lean) | Assumes only that the a_i are independent, so it is at least as strong. |
| LemH_6 | Lemma H.6 (p. 61) | Every bounded p-linear map D^p → G is alternating; (D,G) is split | [statement](Challenges/LemH_6.lean), [proof](Solutions/LemH_6.lean) | `DeterminantPairGeneral` (Category/DeterminantPairGeneral/) | Every jointly algebraically independent family, as in the paper. |
| LemH_7 | Lemma H.7 (p. 62) | Degree-one part of C_0 is zero | [statement](Challenges/LemH_7.lean), [proof](Solutions/LemH_7.lean) | `DeterminantQuadratic.homogeneous_linear_eq_zero` (Algebra/DeterminantQuadraticGap.lean) | Purely algebraic; uses RatFunc (ZMod p). |

## Appendix I

| ID | Paper | Claim | Lean | Proved by | Notes |
|---|---|---|---|---|---|
| PropI_1 | Proposition I.1 (pp. 64-65) | K complete nonarchimedean, E or D of countable type: scalar A^k analytic in every degree | [statement](Challenges/PropI_1.lean), [proof](Solutions/PropI_1.lean) | `CountableType.analyticAt_compContinuousLinearMapCLM_of_countableType_source`, `_target` (Coordinates/CountableType/) | "Countable type" defined in the file. Two parts: E or D of countable type. |
| PropI_2 | Proposition I.2 (pp. 65-66) | A continuous algebraic polynomial on c0 has a bounded lift with ‖q‖ ≤ C_{K,n}‖p‖_diag | [statement](Challenges/PropI_2.lean), [proof](Solutions/PropI_2.lean) | `AlgebraicPolynomialCZero.BoundedLift` (Coordinates/AlgebraicPolynomialCZero/) | ‖p‖_diag defined in the file. C quantified before I, Z, p. |
| RemI_3 | Remark I.3 (pp. 66-67) | A weighted, non-spherically-complete norm on c0 with analytic precomposition | [statement](Challenges/RemI_3.lean), [proof](Solutions/RemI_3.lean) | `WeightedNorm` (Coordinates/WeightedNorm/) | K = `LaurentField (ZMod p) (1/2)`. The weighted space is given through a model, with its existence as part 1. |


## The original comparator challenge

`challenge.lean`, `solution.lean` and `comparator.json` hold six statements chosen before the ledger existed. They correspond to these claims:

| Statement in `challenge.lean` | Claim |
|---|---|
| `false_of_contDiff_omega_compContinuousLinearMapCLM` | Thm6_1a, Cor6_2 |
| `false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach` | Thm6_1a, Cor6_2 |
| `contDiff_compContinuousLinearMapCLM_of_sphericallyComplete` | Thm4_2 |
| `contMDiffVectorBundle_alternating_of_finiteCoordinates` | Cor4_6, finite-coordinate row |
| `false_of_contMDiffVectorBundle_omega_alternating` | Prop6_4_bundle |
| `no_largest_full_analytic_domain_charP` | ThmH_4 |

## Scope notes

The last column of each row says how the Lean statement differs from the paper. The differences worth knowing about:

- **Theorem 2.1** had no formal statement when the ledger was created; its statement was written during formalization. It groups the variables by variance, uses the canonical trivializations, and does not state that the result is independent of the trivializing cover.
- **Theorem 7.2 and Proposition 7.3** are stated on open subsets of a normed space, because Mathlib has no differential forms on manifolds.
- **Corollary C.7** is stated for the explicit transition and section maps rather than as a bundle statement. **Corollary 4.6** states objects and morphisms in each setting but not the functor laws.
- **Theorem 4.5(1)**: the coefficient bound on a bounded linear retract is not stated in Lean; the retract clause is stated for analyticity.
- **Proposition 6.6** is not in the ledger. It has a written proof only.

## Verification (2026-10-09)

- `lake build` of every target succeeds with no `sorry` outside the challenge files.
- `scripts/check_claim.py` passes for all 76 claims (211 theorems; one, `Thm7_2.continuous_wedgeAlg`, is a helper proved in the challenge file because a definition uses it).
- All library modules can be imported together.
- No library file contains an `axiom` declaration, `native_decide` or `unsafe` code.
- The comparator ([leanprover/comparator](https://github.com/leanprover/comparator) at revision `19e111e`) was run on the original six-statement challenge (`comparator.json`), and CI repeats that run on every push. It has not been run on the 76 ledger pairs.

The first four checks were run locally, on the commit that the paper cites. CI (`.github/workflows/comparator.yml`) runs only the comparator.
