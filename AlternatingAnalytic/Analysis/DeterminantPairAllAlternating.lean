import AlternatingAnalytic.Analysis.DeterminantPairScalars
import AlternatingAnalytic.Analysis.DenseScalarFamilyExtension
import AlternatingAnalytic.Analysis.BasisAlternatingCriterion

/-!
# All multilinear maps on the determinant pair are alternating

This proves `dom:all-alt` for the actual determinant-generated subspaces. The
extension takes values in the complete Laurent field; its values belong to `G`
only on tuples from `D`. The auxiliary scalar gap supplies strong alternation,
including in characteristic two.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Function
open scoped NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

local instance : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField
local instance : Field (L p r) :=
  (inferInstance : NontriviallyNormedField (L p r)).toField

/-- The larger-field extension of an actual smaller-target multilinear map. -/
def multilinearExtension
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r)) :
    ContinuousMultilinearMap (L p r) (fun _ : Fin p => A p r) (L p r) :=
  denseScalarFamilyExtension (RationalField.denseRange_algebraMap (ZMod p) r)
    (fun _ => (D p r).subtypeₗᵢ) (fun _ => denseRange_D_subtype p r)
    ((G p r).subtypeL.compContinuousMultilinearMap m)

@[simp]
theorem multilinearExtension_apply
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (x : Fin p → D p r) :
    multilinearExtension p r m (fun i => (x i : A p r)) = (m x : L p r) :=
  denseScalarFamilyExtension_apply _ _ _ _ x

@[simp]
theorem norm_multilinearExtension
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r)) :
    ‖multilinearExtension p r m‖ = ‖m‖ :=
  norm_denseScalarFamilyExtension_comp _ _ _ (G p r).subtypeₗᵢ m

/-- Membership is asserted only on tuples whose entries actually lie in `D`. -/
theorem multilinearExtension_mem_G
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (x : Fin p → A p r) (hx : ∀ i, x i ∈ D p r) :
    multilinearExtension p r m x ∈ G p r := by
  let d : Fin p → D p r := fun i => ⟨x i, hx i⟩
  have h := multilinearExtension_apply p r m d
  exact h.symm ▸ (m d).property

theorem w_mem_D (t : Tau p) : w p r t ∈ D p r := by
  cases t with
  | inl b => exact e_mem_D p r b
  | inr bc => exact (D p r).add_mem (e_mem_D p r bc.val.1) (e_mem_D p r bc.val.2)

theorem tau_smul_w_mem_D (t : Tau p) : tau p r t • w p r t ∈ D p r :=
  gen_mem_D p r (Sum.inr (Sum.inr (Sum.inr t)))

/-- Both the repeated auxiliary vector and its twice-scaled tuple have values in
the actual determinant target. No ambient range assertion is used. -/
theorem multilinearExtension_repeated_w_certificates
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (t : Tau p) :
    let x := fun k => e p r (f k)
    let c := multilinearExtension p r m (update (update x i (w p r t)) j (w p r t))
    c ∈ G p r ∧ tau p r t ^ 2 * c ∈ G p r := by
  classical
  dsimp only
  constructor
  · apply multilinearExtension_mem_G
    intro k
    by_cases hkj : k = j
    · subst k
      simpa using w_mem_D p r t
    by_cases hki : k = i
    · subst k
      simpa [hij] using w_mem_D p r t
    simpa [hkj, hki] using e_mem_D p r (f k)
  · have hmem := multilinearExtension_mem_G p r m
      (update (update (fun k => e p r (f k)) i (tau p r t • w p r t))
        j (tau p r t • w p r t)) (by
          intro k
          by_cases hkj : k = j
          · subst k
            simpa using tau_smul_w_mem_D p r t
          by_cases hki : k = i
          · subst k
            simpa [hij] using tau_smul_w_mem_D p r t
          simpa [hkj, hki] using e_mem_D p r (f k))
    rw [multilinear_repeated_update_smul _ i j hij] at hmem
    simpa only [smul_eq_mul, pow_two, mul_assoc] using hmem

/-- The source-specific auxiliary square gap forces repeated-vector vanishing. -/
theorem multilinearExtension_repeated_w_eq_zero
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (t : Tau p) :
    multilinearExtension p r m
      (update (update (fun k => e p r (f k)) i (w p r t)) j (w p r t)) = 0 := by
  obtain ⟨hc, htc⟩ := multilinearExtension_repeated_w_certificates p r m f i j hij t
  exact eq_zero_of_tau_sq_mul_mem p r t hc htc

/-- The single-vector tags give the diagonal identities on basis tuples. -/
theorem multilinearExtension_repeated_basis_eq_zero
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (b : Fin p) :
    multilinearExtension p r m
      (update (update (fun k => e p r (f k)) i (e p r b)) j (e p r b)) = 0 :=
  multilinearExtension_repeated_w_eq_zero p r m f i j hij (Sum.inl b)

/-- The pair tags supply polarization without dividing by two. -/
theorem multilinearExtension_repeated_basis_add_eq_zero
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (b c : Fin p) (hbc : b < c) :
    multilinearExtension p r m
      (update (update (fun k => e p r (f k)) i (e p r b + e p r c))
        j (e p r b + e p r c)) = 0 :=
  multilinearExtension_repeated_w_eq_zero p r m f i j hij (Sum.inr ⟨(b, c), hbc⟩)

/-- The two cross terms sum to zero for every ordering, including equal indices. -/
theorem multilinearExtension_basis_cross_sum_zero
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (f : Fin p → Fin p) (i j : Fin p) (hij : i ≠ j) (b c : Fin p) :
    multilinearExtension p r m
        (update (update (fun k => e p r (f k)) i (e p r c)) j (e p r b)) +
      multilinearExtension p r m
        (update (update (fun k => e p r (f k)) i (e p r b)) j (e p r c)) = 0 :=
  multilinear_basis_cross_sum_zero (multilinearExtension p r m)
    (TruncatedPolynomial.basis (L p r) p)
    (multilinearExtension_repeated_basis_eq_zero p r m)
    (multilinearExtension_repeated_basis_add_eq_zero p r m) f i j hij b c

/-- The actual Laurent-valued extension is strongly alternating. -/
theorem multilinearExtension_map_eq_zero_of_eq
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (x : Fin p → A p r) (i j : Fin p) (hx : x i = x j) (hij : i ≠ j) :
    multilinearExtension p r m x = 0 :=
  multilinear_alternating_of_basis_repeated (multilinearExtension p r m)
    (TruncatedPolynomial.basis (L p r) p)
    (multilinearExtension_repeated_basis_eq_zero p r m)
    (multilinearExtension_repeated_basis_add_eq_zero p r m) x i j hx hij

/-- Every continuous multilinear map on the actual determinant pair is alternating. -/
theorem multilinear_map_eq_zero_of_eq
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (x : Fin p → D p r) (i j : Fin p) (hx : x i = x j) (hij : i ≠ j) : m x = 0 := by
  apply Subtype.ext
  change (m x : L p r) = 0
  rw [← multilinearExtension_apply p r m x]
  exact multilinearExtension_map_eq_zero_of_eq p r m (fun k => (x k : A p r)) i j
    (congrArg Subtype.val hx) hij

/-- The actual isometric inclusion of alternating maps. -/
def inclusionJ :
    (D p r [⋀^Fin p]→L[K p r] G p r) →ₗᵢ[K p r]
      ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r) :=
  ContinuousAlternatingMap.toContinuousMultilinearMapLI

/-- Strong vanishing proves surjectivity of Mathlib's actual inclusion isometry. -/
theorem toContinuousMultilinearMapLI_surjective :
    Function.Surjective (ContinuousAlternatingMap.toContinuousMultilinearMapLI :
      (D p r [⋀^Fin p]→L[K p r] G p r) →ₗᵢ[K p r]
        ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r)) := by
  intro m
  exact ⟨{ toContinuousMultilinearMap := m
           map_eq_zero_of_eq' := multilinear_map_eq_zero_of_eq p r m }, rfl⟩

/-- Alternating and multilinear maps on this pair are canonically linearly isometric. -/
def allAlternatingEquiv :
    (D p r [⋀^Fin p]→L[K p r] G p r) ≃ₗᵢ[K p r]
      ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r) :=
  LinearIsometryEquiv.ofSurjective (inclusionJ p r)
    (toContinuousMultilinearMapLI_surjective p r)

/-- The source splitness witness, as a concrete bounded linear operator. -/
def retractionR :
    ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r) →L[K p r]
      (D p r [⋀^Fin p]→L[K p r] G p r) :=
  (allAlternatingEquiv p r).symm.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem retractionR_inclusionJ (a : D p r [⋀^Fin p]→L[K p r] G p r) :
    retractionR p r (inclusionJ p r a) = a :=
  (allAlternatingEquiv p r).symm_apply_apply a

@[simp]
theorem inclusionJ_retractionR
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r)) :
    inclusionJ p r (retractionR p r m) = m :=
  (allAlternatingEquiv p r).apply_symm_apply m

@[simp]
theorem retractionR_apply
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
    (x : Fin p → D p r) : retractionR p r m x = m x :=
  congrArg (fun f => f x) (inclusionJ_retractionR p r m)

@[simp]
theorem norm_retractionR_apply
    (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r)) :
    ‖retractionR p r m‖ = ‖m‖ :=
  (allAlternatingEquiv p r).symm.norm_map m

theorem norm_retractionR_le : ‖retractionR p r‖ ≤ 1 :=
  (allAlternatingEquiv p r).symm.toLinearIsometry.norm_toContinuousLinearMap_le

/-- `dom:all-alt`, including extension, strong alternation, the isometric bijection,
and every evaluation and norm identity of its concrete inverse. No completeness
of the rational field or of the determinant target is assumed. -/
theorem all_multilinear_maps_alternating :
    (∀ (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
      (x : Fin p → D p r),
      multilinearExtension p r m (fun i => (x i : A p r)) = (m x : L p r)) ∧
    (∀ m, ‖multilinearExtension p r m‖ = ‖m‖) ∧
    (∀ m (x : Fin p → A p r) (i j : Fin p), x i = x j → i ≠ j →
      multilinearExtension p r m x = 0) ∧
    (∀ (m : ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r))
      (x : Fin p → D p r) (i j : Fin p), x i = x j → i ≠ j → m x = 0) ∧
    Function.Surjective (ContinuousAlternatingMap.toContinuousMultilinearMapLI :
      (D p r [⋀^Fin p]→L[K p r] G p r) →ₗᵢ[K p r]
        ContinuousMultilinearMap (K p r) (fun _ : Fin p => D p r) (G p r)) ∧
    (∀ a, allAlternatingEquiv p r a = inclusionJ p r a) ∧
    (∀ a, retractionR p r (inclusionJ p r a) = a) ∧
    (∀ m, inclusionJ p r (retractionR p r m) = m) ∧
    (∀ m x, retractionR p r m x = m x) ∧
    (∀ m, ‖retractionR p r m‖ = ‖m‖) ∧ ‖retractionR p r‖ ≤ 1 := by
  exact ⟨multilinearExtension_apply p r, norm_multilinearExtension p r,
    multilinearExtension_map_eq_zero_of_eq p r, multilinear_map_eq_zero_of_eq p r,
    toContinuousMultilinearMapLI_surjective p r, fun _ => rfl,
    retractionR_inclusionJ p r, inclusionJ_retractionR p r, retractionR_apply p r,
    norm_retractionR_apply p r, norm_retractionR_le p r⟩

end AlternatingAnalytic.DeterminantPair
