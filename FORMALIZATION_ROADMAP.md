# Formalization roadmap for the manuscript extensions

The original operator counterexample, factorial classification, spherical-target operator theorem, and supporting results remain proved in the existing Lean library. The later manuscript results about analytic families, bundles, parameter spaces, tensors, and analytic domains have mathematical proofs but **no new Lean declarations yet**. See [THEOREM_MAP.md](THEOREM_MAP.md) for the complete scope distinction.

Three Autoform proof-worker launches using the saved Claude backend failed authentication with HTTP 401 before proof generation and reported zero input/output tokens. No proof was generated or added by those attempts. The preparation below is a concrete implementation plan based on the pinned Mathlib API; it is not a claim of partial theorem verification.

## First independent milestones

1. Define the joint action `A(u,v)m = v ∘ m ∘ u^k` and prove its identity/composition laws. Define admissibility for ordinary analytic families and prove closure under analytic reparameterization and composition using bounded bilinear operator composition (`fam:prop:category`).
2. Define the product-space shear `g(u)(d,e) = (d + u e, e)`, with inverse `g(-u)`, and prove the exact operator identity `R ∘ g(u)^* ∘ J = Q(u)` (`fam:prop:shear`). Compose with the existing nonanalytic counterexample to obtain the invertible-family obstruction.
3. Prove diagonal coefficient membership for a power series whose represented function lands in a closed subspace. This is independently useful and has a short route through existing quotient and uniqueness APIs.

These milestones can proceed independently. They do not replace the full finite-coordinate reflection theorem.

## Finite-coordinate analytic reflection

Target `fam:thm:finite-reflection` first for a closed submodule `S ≤ Z` and parameters `Fin d → K`, then transport along a supplied continuous linear equivalence. No completeness, characteristic-zero, factorial-invertibility, or finite-dimensional target hypothesis belongs in the theorem. Over incomplete K, `FiniteDimensional K E` alone is insufficient.

### 1. Diagonal terms belong to the closed subspace

Postcompose an ambient formal multilinear series with the quotient map `S.mkQL`. The represented quotient-valued function is zero. Apply uniqueness of homogeneous diagonals and conclude that each original diagonal lies in S.

Relevant pinned APIs:

- `Submodule.Quotient.normedAddCommGroup`, with the closed-carrier instance, and `Submodule.Quotient.normedSpace`.
- `Submodule.mkQL` and `Submodule.Quotient.mk_eq_zero`.
- `ContinuousLinearMap.comp_hasFPowerSeriesOnBall` and `ContinuousLinearMap.compFormalMultilinearSeries`.
- `HasFPowerSeriesAt.apply_eq_zero` in `Mathlib/Analysis/Analytic/Uniqueness.lean`.

This step works for arbitrary normed parameter spaces. It requires only diagonal membership; do not attempt to prove that a chosen ambient multilinear coefficient lands in S on every tuple.

### 2. Build a bounded representative in finite coordinates

The principal missing lemma takes a bounded n-linear map B on `Fin d → K` whose diagonal lies in S and constructs an S-valued bounded n-linear C with the same diagonal and

`‖C‖ ≤ (d : ℝ)^n * ‖B‖`.

Group coordinate words `w : Fin n → Fin d` by their multiplicity vectors. Each grouped coefficient is a finite sum of B on coordinate-basis tuples. Prove its membership in S by applying algebraic linear functionals annihilating S and scalar polynomial uniqueness. Choose one representative word for each nonempty multiplicity class and use its coordinate-product map with that grouped coefficient.

Useful APIs are `ContinuousMultilinearMap.map_sum`, `map_smul_univ`, `MvPolynomial.funext`, `MvPolynomial.coeff_monomial`, and `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`. Coordinate products can be built with `ContinuousMultilinearMap.mkPiRing` and `compContinuousLinearMap`, using `norm_mkPiRing`, `norm_compContinuousLinearMap_le`, and continuous coordinate projections. The multiplicity classes partition the `d^n` words, giving the exponential bound without any extra factorial.

### 3. Assemble the analytic statement at each point

Apply the finite-coordinate lemma to every coefficient. Use `(max d 1)^n` for the radius argument so that `d = 0` causes no division issue. The relevant radius APIs are `FormalMultilinearSeries.le_mul_pow_of_radius_pos` and `FormalMultilinearSeries.le_radius_of_bound`.

Reflect the known sum through the subtype inclusion or linear isometry using `Topology.IsInducing.hasSum_iff`. Its limit is the actual given value of the function; no completeness of S or Z is required. For the linear-isometry version, first use the range submodule, then transport through `j.equivRange` and its continuous linear equivalence.

The proof initially gives analyticity **at the chosen point**. For an analytic map on an open domain, repeat it at every point. With incomplete targets, an expansion at one point must not be silently promoted to analyticity on a neighborhood. The pointwise coefficient criterion `fam:prop:coefficient-criterion` uses the same distinction.

## Families and vector bundles

After finite-coordinate reflection, construct the degree-`k+1` ambient multilinear representative of the joint action into operators valued in all multilinear maps. The alternating-valued operator space embeds isometrically with closed range, since alternation is expressed by closed evaluation conditions. Reflection then yields `fam:cor:finite-families`.

Apply that theorem on open base-chart overlaps to the pair of transition families `(g⁻¹,h)`. Functoriality preserves the cocycle identity, giving `fam:thm:finite-bundles`. Preserve arbitrary normed fibers and the explicit continuous-coordinate hypothesis on the base. The paper proves an open-chart result; it does not supply a generic analytic `WithinAt` reflection theorem on arbitrary subsets or an unrestricted infinite-dimensional-base theorem. The unconditional C∞ theorem is already in the pinned Mathlib.

## Further branches

| Branch | Main remaining construction | Scope to preserve |
|---|---|---|
| Nonarchimedean `c₀` parameters | Grouped coefficients and convergent sorted-word sums with norm at most the original coefficient norm | Arbitrary index set; complete reflected target and nonarchimedean ambient norm. These are parameter assumptions. |
| Ordinary `ℓ¹` parameters | Fixed-degree coefficient lift, then local factorization through a free `ℓ¹` space | Closed Banach output subspace; K may be incomplete. The auxiliary map is needed to be analytic at the chosen center. Only the fixed outer degree incurs a factorial bound. |
| Tensor reflection criterion | Separated completed ordinary projective tensors and diagonal-span projections; one `c₀`-sum test map for necessity | Complete K and Banach parameters/targets. Exponential projection bounds characterize universal reflection, which is stronger than alternating-family admissibility. |
| Universal-target core | Two factorizations of the joint action and retract/product transport | Core objects can be adjoined to every analytic domain; the statement does not classify all targets intrinsically. |
| No largest analytic domain | Algebraically independent Laurent scalars, completion rigidity, the all-prime degree-gap functional, and the padded split retraction | `K = F_p(t)`, all primes p and `k ≥ p`, incomplete finite algebraic dimensional witnesses. Complete-field and Banach versions remain open. |

The no-largest-domain construction is a separate proof project from the existing Banach counterexample. Completing its witnesses removes its obstruction, so scalar-completion transport from the old development must not be used to claim a Banach version.

Only completed, kernel-checked results should be added to the theorem map as Lean proofs or exposed as new challenge entries. The existing three-statement challenge remains unchanged and is checked only with Kim Morrison's comparator.
