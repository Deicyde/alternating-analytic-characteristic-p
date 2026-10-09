import AlternatingAnalytic.Category.DeterminantPairGeneral.Spaces
import AlternatingAnalytic.Analysis.DenseScalarFamilyExtension
import AlternatingAnalytic.Analysis.BasisAlternatingCriterion
import AlternatingAnalytic.Analysis.BaseChangeAlternatingCriterion

/-!
# Lemma H.6 for an arbitrary algebraically independent family

For every family `z` of scalars `a_i, τ_w ∈ 𝔽_p((t))` algebraically independent over `𝔽_p(t)`,
every bounded `p`-linear map `D^p → G` is alternating, and so `(D, G)` is split in degree `p`.
The proof extends `m` to an `L`-multilinear map on `A`. Its values on tuples from `D` stay in
`G`, so the gap `τ_w² G ∩ G = 0` kills its values on tuples with a repeated `w ∈ 𝒲`.
Polarization with `w = e_i + e_j`, which needs no division by two, gives alternation on `A`.
-/

namespace AlternatingAnalytic.DeterminantPairGeneral

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Function
open scoped BigOperators NNReal

variable {p : ℕ} [Fact p.Prime] {r : ℝ≥0} [Fact (0 < r)] [Fact (r < 1)]

local instance : NormedField (Kt p r) :=
  (inferInstance : NontriviallyNormedField (Kt p r)).toNormedField
local instance : Field (Kt p r) :=
  (inferInstance : NontriviallyNormedField (Kt p r)).toField
local instance : Field (Lt p r) :=
  (inferInstance : NontriviallyNormedField (Lt p r)).toField

variable (z : Fin p ⊕ Tau p → Lt p r)

/-- The `L`-multilinear extension to `A` of a bounded `K`-multilinear map `D^p → G`. -/
def multilinearExtension
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z)) :
    ContinuousMultilinearMap (Lt p r) (fun _ : Fin p => A p r) (Lt p r) :=
  denseScalarFamilyExtension (RationalField.denseRange_algebraMap (ZMod p) r)
    (fun _ => (D z).subtypeₗᵢ) (fun _ => denseRange_D_subtype z)
    ((G z).subtypeL.compContinuousMultilinearMap m)

@[simp]
theorem multilinearExtension_apply
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z))
    (x : Fin p → D z) :
    multilinearExtension z m (fun i => (x i : A p r)) = (m x : Lt p r) :=
  denseScalarFamilyExtension_apply _ _ _ _ x

theorem multilinearExtension_mem_G
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z))
    (x : Fin p → A p r) (hx : ∀ i, x i ∈ D z) :
    multilinearExtension z m x ∈ G z := by
  let d : Fin p → D z := fun i => ⟨x i, hx i⟩
  have h := multilinearExtension_apply z m d
  exact h.symm ▸ (m d).property

variable {z}

/-- The extension vanishes on basis tuples with a repeated element of `𝒲`. -/
theorem multilinearExtension_repeated_w_eq_zero (hz : AlgebraicIndependent (Kt p r) z)
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (t : Tau p) :
    multilinearExtension z m
      (update (update (fun k => e p r (f k)) i (w p r t)) j (w p r t)) = 0 := by
  classical
  have hc : multilinearExtension z m
      (update (update (fun k => e p r (f k)) i (w p r t)) j (w p r t)) ∈ G z := by
    apply multilinearExtension_mem_G
    intro k
    by_cases hkj : k = j
    · subst k
      simpa using w_mem_D z t
    by_cases hki : k = i
    · subst k
      simpa [hij] using w_mem_D z t
    simpa [hkj, hki] using e_mem_D z (f k)
  have hmem := multilinearExtension_mem_G z m
    (update (update (fun k => e p r (f k)) i (z (Sum.inr t) • w p r t))
      j (z (Sum.inr t) • w p r t)) (by
        intro k
        by_cases hkj : k = j
        · subst k
          simpa using tau_smul_w_mem_D z t
        by_cases hki : k = i
        · subst k
          simpa [hij] using tau_smul_w_mem_D z t
        simpa [hkj, hki] using e_mem_D z (f k))
  rw [multilinear_repeated_update_smul _ i j hij] at hmem
  have htc : z (Sum.inr t) ^ 2 * multilinearExtension z m
      (update (update (fun k => e p r (f k)) i (w p r t)) j (w p r t)) ∈ G z := by
    simpa only [smul_eq_mul, pow_two, mul_assoc] using hmem
  exact eq_zero_of_tau_sq_mul_mem z hz t hc htc

theorem multilinearExtension_repeated_basis_eq_zero (hz : AlgebraicIndependent (Kt p r) z)
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (b : Fin p) :
    multilinearExtension z m
      (update (update (fun k => TruncatedPolynomial.basis (Lt p r) p (f k)) i
        (TruncatedPolynomial.basis (Lt p r) p b)) j
        (TruncatedPolynomial.basis (Lt p r) p b)) = 0 := by
  simpa only [← e_eq_basis, w] using
    multilinearExtension_repeated_w_eq_zero hz m f i j hij (Sum.inl b)

theorem multilinearExtension_repeated_basis_add_eq_zero (hz : AlgebraicIndependent (Kt p r) z)
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (b c : Fin p) (hbc : b < c) :
    multilinearExtension z m
      (update (update (fun k => TruncatedPolynomial.basis (Lt p r) p (f k)) i
        (TruncatedPolynomial.basis (Lt p r) p b + TruncatedPolynomial.basis (Lt p r) p c))
        j (TruncatedPolynomial.basis (Lt p r) p b +
          TruncatedPolynomial.basis (Lt p r) p c)) = 0 := by
  simpa only [← e_eq_basis, w] using
    multilinearExtension_repeated_w_eq_zero hz m f i j hij (Sum.inr ⟨(b, c), hbc⟩)

/-- Lemma H.6, first part: every bounded `p`-linear map `D^p → G` is alternating. -/
theorem map_eq_zero_of_eq (hz : AlgebraicIndependent (Kt p r) z)
    (m : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z))
    (v : Fin p → D z) (i j : Fin p) (hv : v i = v j) (hij : i ≠ j) : m v = 0 := by
  apply Subtype.ext
  change (m v : Lt p r) = 0
  rw [← multilinearExtension_apply z m v]
  exact multilinear_alternating_of_basis_repeated (multilinearExtension z m)
    (TruncatedPolynomial.basis (Lt p r) p)
    (multilinearExtension_repeated_basis_eq_zero hz m)
    (multilinearExtension_repeated_basis_add_eq_zero hz m) (fun k => (v k : A p r)) i j
    (congrArg Subtype.val hv) hij

/-- Alternating and multilinear maps `D^p → G` agree, isometrically. -/
def allAlternatingEquiv (hz : AlgebraicIndependent (Kt p r) z) :
    (D z [⋀^Fin p]→L[Kt p r] G z) ≃ₗᵢ[Kt p r]
      ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z) :=
  LinearIsometryEquiv.ofSurjective ContinuousAlternatingMap.toContinuousMultilinearMapLI
    (fun m => ⟨{ toContinuousMultilinearMap := m
                 map_eq_zero_of_eq' := map_eq_zero_of_eq hz m }, rfl⟩)

/-- Lemma H.6, second part: `(D, G)` is split in degree `p`. -/
theorem exists_retraction (hz : AlgebraicIndependent (Kt p r) z) :
    ∃ R : ContinuousMultilinearMap (Kt p r) (fun _ : Fin p => D z) (G z) →L[Kt p r]
      (D z [⋀^Fin p]→L[Kt p r] G z),
      ∀ m : D z [⋀^Fin p]→L[Kt p r] G z, R m.toContinuousMultilinearMap = m :=
  ⟨(allAlternatingEquiv hz).symm.toLinearIsometry.toContinuousLinearMap,
    fun m => (allAlternatingEquiv hz).symm_apply_apply m⟩

end

end AlternatingAnalytic.DeterminantPairGeneral
