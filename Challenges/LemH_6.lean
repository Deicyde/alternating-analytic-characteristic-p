import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Analysis.TruncatedPolynomialMaxNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Lemma H.6 (every bounded `p`-linear map `D^p → G` is alternating; `(D, G)` is split), p. 58

Setting (Appendix H.1): `p` is prime, `K = 𝔽_p(t)` with its `t`-adic absolute value,
`L = 𝔽_p((t))` its completion, `A = L[ε]/(ε^p)` with `e_i = ε^i` (`0 ≤ i < p`) and "the maximum
norm in this basis". "Choose elements `a_0, …, a_{p-1} ∈ L`, together with the finitely many
auxiliary scalars `τ_w` introduced below, algebraically independent over `K`." `a = ∑ a_i e_i`.
"Every subspace used below carries the norm induced by `A` or `L`." Define
`D_0 = span_K{e_i, ε^i a : 0 ≤ i < p} + K a²`,
`𝒲 = {e_i : 0 ≤ i < p} ∪ {e_i + e_j : 0 ≤ i < j < p}`,
`D = D_0 + ∑_{w ∈ 𝒲} K τ_w w`, `G = span_K{det(d_1, …, d_p) : d_i ∈ D} ⊆ L`, the determinant taken
in the basis `(e_0, …, e_{p-1})`. A pair `(E, F)` is split in degree `k` if the inclusion
`Alt^k(E;F) → Mult^k(E;F)` has a bounded linear retraction.

Paper statement: "Every bounded `p`-linear map `D^p → G` is alternating. Thus `(D, G)` is split in
degree `p`."

Formalization notes:
* `K` and `L` are the library's `AlternatingAnalytic.RationalField (ZMod p) r` and
  `AlternatingAnalytic.LaurentField (ZMod p) r` (`‖t‖ = r`, `0 < r < 1`), with the library's
  isometric dense inclusion `K → L`. `A` is the library's
  `AlternatingAnalytic.TruncatedPolynomial.A L p` (`AdjoinRoot (X^p)` over `L`) with the library's
  maximum coefficient norm in the basis `ε^i`; `ε` is `TruncatedPolynomial.epsilon` and
  coordinates are `TruncatedPolynomial.coeff`. These library files are imported for these
  definitions only. The `K`-normed structure on `A` (`instNormedSpaceKA`) is defined here by
  restricting scalars along `K → L`, and the field instances on `K`, `L` are pinned to those of
  their normed-field structures (as in the library).
* The auxiliary index set is `Tau p = Fin p ⊕ {(i, j) // i < j}`, `w (inl i) = e_i`,
  `w (inr (i, j)) = e_i + e_j` (this lists `𝒲`). The scalars are one family
  `z : Fin p ⊕ Tau p → L`, `a_i = z (inl i)`, `τ_w = z (inr w)`, assumed algebraically independent
  over `K` (the paper's hypothesis). The statements are for every such choice.
* `D z` and `G z` (defined here) are `K`-submodules of `A` and `L` with induced norms. `G` is
  the span of `det(d_1, …, d_p)` over all tuples from `D`, literally.
* `part1`: "alternating" means vanishing whenever two distinct argument slots are equal (Mathlib's
  convention for `ContinuousAlternatingMap`). "Bounded `p`-linear map `D^p → G`" is
  `ContinuousMultilinearMap K (fun _ : Fin p => D z) (G z)`.
  `part2`: `IsSplitInDegree` (defined here, as in Lemma H.3).
* Library status (no solution file): the library proves both assertions only for its own fixed
  choice `AlternatingAnalytic.DeterminantPair.z p r` of the scalars
  (`DeterminantPair.all_multilinear_maps_alternating` with its retraction `retractionR`, in
  `AlternatingAnalytic/Analysis/DeterminantPairAllAlternating.lean`, and
  `DeterminantPair.isSplit_unpaddedD` in `DeterminantPairSelfActions.lean`), not for an
  arbitrary algebraically independent family as stated here. At that choice the definitions `D`
  and `G` of this file agree with the library's `DeterminantPair.D p r` and `DeterminantPair.G p r`
  (checked in a scratch file).
-/

namespace AlternatingAnalyticChallenge.LemH_6

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators NNReal

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

/-- The `t`-adic rational field `𝔽_p(t)`, `‖t‖ = r`. -/
abbrev Kt := AlternatingAnalytic.RationalField (ZMod p) r

/-- Its completion `𝔽_p((t))`. -/
abbrev Lt := AlternatingAnalytic.LaurentField (ZMod p) r

local instance preferredNormedFieldK : NormedField (Kt p r) :=
  (inferInstance : NontriviallyNormedField (Kt p r)).toNormedField
local instance preferredFieldK : Field (Kt p r) :=
  (inferInstance : NontriviallyNormedField (Kt p r)).toField
local instance preferredFieldL : Field (Lt p r) :=
  (inferInstance : NontriviallyNormedField (Lt p r)).toField

/-- `A = L[ε]/(ε^p)` with the maximum norm in the basis `ε^i`. -/
abbrev A := AlternatingAnalytic.TruncatedPolynomial.A (Lt p r) p

/-- `A` as a normed `K`-space, by restriction of scalars along the isometry `K → L`. -/
noncomputable instance instNormedSpaceKA : NormedSpace (Kt p r) (A p r) :=
  { (inferInstance : Module (Kt p r) (A p r)) with
    norm_smul_le := fun c x => by
      rw [← algebraMap_smul (Lt p r) c x]
      exact (norm_smul_le (algebraMap (Kt p r) (Lt p r) c) x).trans_eq
        (by rw [norm_algebraMap']) }

/-- Index set of the auxiliary family `𝒲`: `e_i` and `e_i + e_j` for `i < j`. -/
abbrev Tau := Fin p ⊕ {ij : Fin p × Fin p // ij.1 < ij.2}

/-- The basis vector `e_i = ε^i`. -/
noncomputable def e (i : Fin p) : A p r :=
  AlternatingAnalytic.TruncatedPolynomial.epsilon (Lt p r) p ^ (i : ℕ)

variable {p r}

/-- `a = ∑ a_i e_i`, with `a_i = z (inl i)`. -/
noncomputable def a (z : Fin p ⊕ Tau p → Lt p r) : A p r :=
  ∑ i : Fin p, z (Sum.inl i) • e p r i

variable (p r) in
/-- The elements of `𝒲`. -/
noncomputable def w : Tau p → A p r
  | Sum.inl i => e p r i
  | Sum.inr ij => e p r ij.val.1 + e p r ij.val.2

/-- `D_0 = span_K{e_i, ε^i a : 0 ≤ i < p} + K a²`. -/
noncomputable def D₀ (z : Fin p ⊕ Tau p → Lt p r) : Submodule (Kt p r) (A p r) :=
  Submodule.span (Kt p r) (Set.range (Sum.elim (e p r) (fun i => e p r i * a z))) ⊔
    (Kt p r) ∙ (a z * a z)

/-- `D = D_0 + ∑_{w ∈ 𝒲} K τ_w w`, with `τ_w = z (inr w)`. -/
noncomputable def D (z : Fin p ⊕ Tau p → Lt p r) : Submodule (Kt p r) (A p r) :=
  D₀ z ⊔ Submodule.span (Kt p r) (Set.range (fun t => z (Sum.inr t) • w p r t))

variable (p r) in
/-- The determinant in the basis `(e_0, …, e_{p-1})`: column `j` is the coordinate vector of
`v j`. -/
noncomputable def det (v : Fin p → A p r) : Lt p r :=
  Matrix.det (Matrix.of (fun i j =>
    AlternatingAnalytic.TruncatedPolynomial.coeff (Lt p r) p (v j) i))

/-- `G = span_K{det(d_1, …, d_p) : d_i ∈ D} ⊆ L`. -/
noncomputable def G (z : Fin p ⊕ Tau p → Lt p r) : Submodule (Kt p r) (Lt p r) :=
  Submodule.span (Kt p r) (Set.range (fun d : Fin p → D z => det p r (fun i => d i)))

/-- `D` with the norm induced from `A`. -/
instance instNormedAddCommGroupD (z : Fin p ⊕ Tau p → Lt p r) : NormedAddCommGroup (D z) :=
  inferInstance

instance instNormedSpaceD (z : Fin p ⊕ Tau p → Lt p r) : NormedSpace (Kt p r) (D z) :=
  inferInstance

/-- `G` with the norm induced from `L`. -/
instance instNormedAddCommGroupG (z : Fin p ⊕ Tau p → Lt p r) : NormedAddCommGroup (G z) :=
  inferInstance

instance instNormedSpaceG (z : Fin p ⊕ Tau p → Lt p r) : NormedSpace (Kt p r) (G z) :=
  inferInstance

/-- The pair `(E, F)` is split in degree `k`: the inclusion
`Alt^k(E;F) → Mult^k(E;F)` has a bounded linear retraction. -/
def IsSplitInDegree (K : Type*) [NontriviallyNormedField K] (k : ℕ) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F] : Prop :=
  ∃ R : ContinuousMultilinearMap K (fun _ : Fin k => E) F →L[K] (E [⋀^Fin k]→L[K] F),
    ∀ m : E [⋀^Fin k]→L[K] F, R m.toContinuousMultilinearMap = m

/-- **Lemma H.6, first assertion.** For every choice of `a_i, τ_w ∈ L` algebraically independent
over `K`, every bounded `p`-linear map `D^p → G` is alternating. -/
theorem part1 (z : Fin p ⊕ Tau p → Lt p r) (hz : AlgebraicIndependent (Kt p r) z)
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z))
    (v : Fin p → D z) (i j : Fin p) (hv : v i = v j) (hij : i ≠ j) : m v = 0 := by
  sorry

/-- **Lemma H.6, second assertion.** For every such choice, `(D, G)` is split in degree `p`. -/
theorem part2 (z : Fin p ⊕ Tau p → Lt p r) (hz : AlgebraicIndependent (Kt p r) z) :
    IsSplitInDegree (Kt p r) p (D z) (G z) := by
  sorry

end

end AlternatingAnalyticChallenge.LemH_6
