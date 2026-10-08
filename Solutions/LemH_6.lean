import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Category.DeterminantPairGeneral.AllAlternating
import AlternatingAnalytic.Analysis.TruncatedPolynomialMaxNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Lemma H.6 (every bounded `p`-linear map `D^p → G` is alternating; `(D, G)` is split), p. 58

Solution: the statements of `Challenges/LemH_6.lean`, proved for an arbitrary algebraically
independent family `z` in `AlternatingAnalytic/Category/DeterminantPairGeneral/`:
* `part1`: `AlternatingAnalytic.DeterminantPairGeneral.map_eq_zero_of_eq` (`AllAlternating.lean`),
  from the gap `τ_w² G ∩ G = 0` (`eq_zero_of_tau_sq_mul_mem`, `Spaces.lean`) and polarization
  with `w = e_i + e_j`;
* `part2`: `AlternatingAnalytic.DeterminantPairGeneral.exists_retraction`.
The library's `D z`, `G z` are this file's, definitionally (same definitions, other namespace).
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
  exact AlternatingAnalytic.DeterminantPairGeneral.map_eq_zero_of_eq hz m v i j hv hij

/-- **Lemma H.6, second assertion.** For every such choice, `(D, G)` is split in degree `p`. -/
theorem part2 (z : Fin p ⊕ Tau p → Lt p r) (hz : AlgebraicIndependent (Kt p r) z) :
    IsSplitInDegree (Kt p r) p (D z) (G z) := by
  exact AlternatingAnalytic.DeterminantPairGeneral.exists_retraction hz

end

end AlternatingAnalyticChallenge.LemH_6
