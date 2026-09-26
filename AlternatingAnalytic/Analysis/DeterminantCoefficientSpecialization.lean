import AlternatingAnalytic.Analysis.DeterminantPairScalars

/-!
# Algebraic models and specialization of determinant coefficients

The coefficient subspaces carry their inherited norms. Polynomial representatives
and substitution in the auxiliary variables are purely algebraic constructions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

local instance specializationNormedFieldK : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance specializationFieldK : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField
local instance specializationFieldL : Field (L p r) :=
  (inferInstance : NontriviallyNormedField (L p r)).toField

/-- The actual scalar coefficient space, with its subtype norm. -/
def C : Submodule (K p r) (L p r) :=
  G p r ⊓ ⨅ i : Fin p,
    (G p r).comap (LinearMap.mulLeft (K p r) (z p r (Sum.inl i)))

@[simp] theorem mem_C {c : L p r} :
    c ∈ C p r ↔ c ∈ G p r ∧ ∀ i : Fin p, z p r (Sum.inl i) * c ∈ G p r := by
  simp [C]

/-- The polynomial coefficient space in the jointly independent coordinates. -/
def Cpoly : Submodule (K p r) (Poly p r) :=
  Gpoly p r ⊓ ⨅ i : Fin p,
    (Gpoly p r).comap (LinearMap.mulLeft (K p r) (MvPolynomial.X (Sum.inl i)))

@[simp] theorem mem_Cpoly {P : Poly p r} :
    P ∈ Cpoly p r ↔ P ∈ Gpoly p r ∧
      ∀ i : Fin p, MvPolynomial.X (Sum.inl i) * P ∈ Gpoly p r := by
  simp [Cpoly]

@[simp] theorem evaluation_X (i : Fin p) :
    evaluation p r (MvPolynomial.X (Sum.inl i)) = z p r (Sum.inl i) := by
  simp [evaluation]

@[simp] theorem evaluation_C (c : K p r) :
    evaluation p r (MvPolynomial.C c) = algebraMap (K p r) (L p r) c := by
  simp [evaluation]

@[simp] theorem evaluation_mem_G_iff (P : Poly p r) :
    evaluation p r P ∈ G p r ↔ P ∈ Gpoly p r := by
  rw [← map_Gpoly]
  constructor
  · rintro ⟨Q, hQ, heq⟩
    exact evaluation_injective p r heq ▸ hQ
  · intro hP
    exact ⟨P, hP, rfl⟩

@[simp] theorem evaluation_mem_C_iff (P : Poly p r) :
    evaluation p r P ∈ C p r ↔ P ∈ Cpoly p r := by
  simp only [mem_C, mem_Cpoly, evaluation_mem_G_iff]
  apply and_congr_right
  intro _
  exact forall_congr' fun i => by
    rw [← evaluation_X p r i, ← map_mul, evaluation_mem_G_iff]

/-- Evaluation identifies exactly the polynomial and scalar coefficient spaces. -/
theorem map_Cpoly : (Cpoly p r).map (evaluation p r).toLinearMap = C p r := by
  ext c
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact (evaluation_mem_C_iff p r P).2 hP
  · intro hc
    obtain ⟨P, hP, hPc⟩ := (Submodule.mem_map.mp
      ((map_Gpoly p r).symm ▸ (mem_C p r).mp hc |>.1))
    refine ⟨P, ?_, hPc⟩
    apply (evaluation_mem_C_iff p r P).1
    change evaluation p r P = c at hPc
    rwa [hPc]

/-- Coefficients have unique polynomial representatives without any continuity claim. -/
theorem existsUnique_coefficient_polynomial_representative {c : L p r}
    (hc : c ∈ C p r) :
    ∃! P : Poly p r, P ∈ Cpoly p r ∧ evaluation p r P = c := by
  apply existsUnique_polynomial_rep_of_mem_map (z p r) (algebraicIndependent_z p r)
    (Cpoly p r)
  rwa [← map_Cpoly] at hc

/-- Polynomials in the non-auxiliary coordinates alone. -/
abbrev Poly0 := MvPolynomial (Fin p) (K p r)

/-- The literal substitution `Xᵢ ↦ Xᵢ`, `Y_w ↦ 0`. -/
def specialization : Poly p r →ₐ[K p r] Poly0 p r :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X fun _ => 0)

@[simp] theorem specialization_X (i : Fin p) :
    specialization p r (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i := by
  simp [specialization]

@[simp] theorem specialization_Y (w : Tau p) :
    specialization p r (MvPolynomial.X (Sum.inr w)) = 0 := by
  simp [specialization]

@[simp] theorem specialization_C (c : K p r) :
    specialization p r (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [specialization]

@[simp] theorem specialization_mul (P Q : Poly p r) :
    specialization p r (P * Q) = specialization p r P * specialization p r Q :=
  map_mul _ _ _

/-- Tags of the actual symbolic generators of `D₀`. -/
abbrev Generator0Index := Fin p ⊕ (Fin p ⊕ Unit)

def includeGenerator0 : Generator0Index p → GeneratorIndex p
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr (Sum.inl u))

/-- Literal coordinate polynomials of the `D₀` generators. -/
def gen0Poly : Generator0Index p → Fin p → Poly0 p r
  | Sum.inl i => fun k => if i = k then 1 else 0
  | Sum.inr (Sum.inl i) => fun k =>
      ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ) then MvPolynomial.X j else 0
  | Sum.inr (Sum.inr _) => fun k =>
      ∑ i : Fin p, ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ)
        then MvPolynomial.X i * MvPolynomial.X j else 0

/-- The non-auxiliary symbolic determinant generators. -/
def det0Poly (s : Fin p → Generator0Index p) : Poly0 p r :=
  Matrix.det (Matrix.of (fun i j => gen0Poly p r (s j) i))

/-- The manuscript's polynomial model before adjoining the auxiliary scalars. -/
def G0poly : Submodule (K p r) (Poly0 p r) :=
  Submodule.span (K p r) (Set.range (det0Poly p r))

def C0poly : Submodule (K p r) (Poly0 p r) :=
  G0poly p r ⊓ ⨅ i : Fin p,
    (G0poly p r).comap (LinearMap.mulLeft (K p r) (MvPolynomial.X i))

@[simp] theorem mem_C0poly {P : Poly0 p r} :
    P ∈ C0poly p r ↔ P ∈ G0poly p r ∧
      ∀ i : Fin p, MvPolynomial.X i * P ∈ G0poly p r := by
  simp [C0poly]

@[simp] theorem specialization_genPoly_include (j : Generator0Index p) (k : Fin p) :
    specialization p r (genPoly p r (includeGenerator0 p j) k) = gen0Poly p r j k := by
  rcases j with i | (i | u) <;>
    simp [includeGenerator0, genPoly, gen0Poly, ePoly, apply_ite]

@[simp] theorem specialization_genPoly_auxiliary (w : Tau p) (k : Fin p) :
    specialization p r (genPoly p r (Sum.inr (Sum.inr (Sum.inr w))) k) = 0 := by
  simp [genPoly]

@[simp] theorem specialization_detPoly_include (s : Fin p → Generator0Index p) :
    specialization p r (detPoly p r (includeGenerator0 p ∘ s)) = det0Poly p r s := by
  rw [detPoly, AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact specialization_genPoly_include p r (s j) i

/-- Each auxiliary generator specializes to a zero column; the other tuples are
exactly the symbolic `D₀` tuples. -/
theorem specialization_detPoly_mem (s : Fin p → GeneratorIndex p) :
    specialization p r (detPoly p r s) ∈ G0poly p r := by
  classical
  by_cases h : ∀ j, ∃ j0, s j = includeGenerator0 p j0
  · choose t ht using h
    have hs : s = includeGenerator0 p ∘ t := funext ht
    rw [hs, specialization_detPoly_include]
    exact Submodule.subset_span ⟨t, rfl⟩
  · push Not at h
    obtain ⟨j, hj⟩ := h
    have hz : ∃ w, s j = Sum.inr (Sum.inr (Sum.inr w)) := by
      rcases hsj : s j with i | (i | (u | w))
      · exact (hj (Sum.inl i) hsj).elim
      · exact (hj (Sum.inr (Sum.inl i)) hsj).elim
      · exact (hj (Sum.inr (Sum.inr u)) hsj).elim
      · exact ⟨w, rfl⟩
    obtain ⟨w, hw⟩ := hz
    have hzero : specialization p r (detPoly p r s) = 0 := by
      rw [detPoly, AlgHom.map_det]
      apply Matrix.det_eq_zero_of_column_eq_zero j
      intro i
      change specialization p r (genPoly p r (s j) i) = 0
      rw [hw, specialization_genPoly_auxiliary]
    rw [hzero]
    exact (G0poly p r).zero_mem

theorem specialization_mem_Gpoly {P : Poly p r} (hP : P ∈ Gpoly p r) :
    specialization p r P ∈ G0poly p r := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨s, rfl⟩ := hP
      exact specialization_detPoly_mem p r s
  | zero => simp
  | add P Q hP hQ ihP ihQ => simpa using (G0poly p r).add_mem ihP ihQ
  | smul c P hP ihP => simpa using (G0poly p r).smul_mem c ihP

/-- Algebraic specialization maps the whole determinant space onto the original
non-auxiliary determinant space. -/
theorem map_specialization_Gpoly :
    (Gpoly p r).map (specialization p r).toLinearMap = G0poly p r := by
  apply le_antisymm
  · rintro P ⟨Q, hQ, rfl⟩
    exact specialization_mem_Gpoly p r hQ
  · apply Submodule.span_le.mpr
    rintro P ⟨s, rfl⟩
    exact ⟨detPoly p r (includeGenerator0 p ∘ s),
      Submodule.subset_span ⟨includeGenerator0 p ∘ s, rfl⟩,
      specialization_detPoly_include p r s⟩

/-- Coefficient membership is preserved by the algebraic substitution. -/
theorem specialization_mem_Cpoly {P : Poly p r} (hP : P ∈ Cpoly p r) :
    specialization p r P ∈ C0poly p r := by
  obtain ⟨hP, hX⟩ := (mem_Cpoly p r).mp hP
  apply (mem_C0poly p r).mpr
  refine ⟨specialization_mem_Gpoly p r hP, fun i => ?_⟩
  simpa using specialization_mem_Gpoly p r (hX i)

theorem map_specialization_Cpoly_le :
    (Cpoly p r).map (specialization p r).toLinearMap ≤ C0poly p r := by
  rintro P ⟨Q, hQ, rfl⟩
  exact specialization_mem_Cpoly p r hQ

/-- The inherited coefficient norm is exactly the Laurent-field norm. -/
theorem norm_C (c : C p r) : ‖c‖ = ‖(c : L p r)‖ := rfl

/-- Polynomial evaluation gives an algebraic linear equivalence onto `G`. -/
def polynomialEquivG : Gpoly p r ≃ₗ[K p r] G p r :=
  (Submodule.equivMapOfInjective (evaluation p r).toLinearMap
    (evaluation_injective p r) (Gpoly p r)).trans (LinearEquiv.ofEq _ _ (map_Gpoly p r))

@[simp] theorem polynomialEquivG_apply (P : Gpoly p r) :
    (polynomialEquivG p r P : L p r) = evaluation p r P := rfl

/-- Polynomial evaluation gives an algebraic linear equivalence onto `C`.
No continuity of this map or of its inverse is asserted. -/
def polynomialEquivC : Cpoly p r ≃ₗ[K p r] C p r :=
  (Submodule.equivMapOfInjective (evaluation p r).toLinearMap
    (evaluation_injective p r) (Cpoly p r)).trans (LinearEquiv.ofEq _ _ (map_Cpoly p r))

@[simp] theorem polynomialEquivC_apply (P : Cpoly p r) :
    (polynomialEquivC p r P : L p r) = evaluation p r P := rfl

@[simp] theorem evaluation_polynomialEquivC_symm (c : C p r) :
    evaluation p r ((polynomialEquivC p r).symm c : Poly p r) = (c : L p r) := by
  rw [← polynomialEquivC_apply, LinearEquiv.apply_symm_apply]

/-- Algebraic specialization restricted to the coefficient space. -/
def coefficientSpecialization : Cpoly p r →ₗ[K p r] C0poly p r :=
  ((specialization p r).toLinearMap.comp (Cpoly p r).subtype).codRestrict
    (C0poly p r) (fun P => specialization_mem_Cpoly p r P.property)

@[simp] theorem coefficientSpecialization_apply (P : Cpoly p r) :
    (coefficientSpecialization p r P : Poly0 p r) = specialization p r P := rfl

/-- The full algebraic specialization statement for the actual scalar and
polynomial models. All maps displayed here are algebraic. -/
theorem coefficient_polynomial_specialization :
    (∀ c : L p r, c ∈ C p r ↔
      c ∈ G p r ∧ ∀ i : Fin p, z p r (Sum.inl i) * c ∈ G p r) ∧
    (∀ c : C p r, ‖c‖ = ‖(c : L p r)‖) ∧
    (Gpoly p r).map (evaluation p r).toLinearMap = G p r ∧
    (Cpoly p r).map (evaluation p r).toLinearMap = C p r ∧
    Function.Injective (evaluation p r) ∧
    (∀ P : Poly p r, evaluation p r P ∈ G p r ↔ P ∈ Gpoly p r) ∧
    (∀ P : Poly p r, evaluation p r P ∈ C p r ↔ P ∈ Cpoly p r) ∧
    (∀ c : L p r, c ∈ C p r →
      ∃! P : Poly p r, P ∈ Cpoly p r ∧ evaluation p r P = c) ∧
    (∀ i : Fin p, specialization p r (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i) ∧
    (∀ w : Tau p, specialization p r (MvPolynomial.X (Sum.inr w)) = 0) ∧
    (∀ c : K p r, specialization p r (MvPolynomial.C c) = MvPolynomial.C c) ∧
    (∀ P Q : Poly p r,
      specialization p r (P * Q) = specialization p r P * specialization p r Q) ∧
    (Gpoly p r).map (specialization p r).toLinearMap = G0poly p r ∧
    (Cpoly p r).map (specialization p r).toLinearMap ≤ C0poly p r ∧
    (∀ P : Gpoly p r, (polynomialEquivG p r P : L p r) = evaluation p r P) ∧
    (∀ P : Cpoly p r, (polynomialEquivC p r P : L p r) = evaluation p r P) ∧
    (∀ P : Cpoly p r,
      (coefficientSpecialization p r P : Poly0 p r) = specialization p r P) := by
  exact ⟨fun _ => mem_C p r, norm_C p r, map_Gpoly p r, map_Cpoly p r,
    evaluation_injective p r, evaluation_mem_G_iff p r, evaluation_mem_C_iff p r,
    fun _ => existsUnique_coefficient_polynomial_representative p r,
    specialization_X p r, specialization_Y p r, specialization_C p r,
    specialization_mul p r, map_specialization_Gpoly p r, map_specialization_Cpoly_le p r,
    polynomialEquivG_apply p r, polynomialEquivC_apply p r,
    coefficientSpecialization_apply p r⟩

end AlternatingAnalytic.DeterminantPair
