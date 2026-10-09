import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Analysis.TruncatedPolynomialMaxNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import AlternatingAnalytic.Analysis.DeterminantSpan
import AlternatingAnalytic.Analysis.DeterminantDensity
import AlternatingAnalytic.Analysis.DeterminantPolynomialDegree

/-!
# Determinant-generated spaces and the auxiliary scalar gap

The construction of Appendix H. Over `K = F_p(t)` with completion `L = F_p((t))`, with
`A = L[ε]/(ε^p)` in the maximum norm, this defines the scalars `a_i` and `τ_w` (one
algebraically independent family `z`), the vector `a = ∑ a_i e_i`, the `K`-subspaces
`D₀ ⊆ D ⊆ A` and `G ⊆ L`, and the polynomial model of `G`. It proves the gap (H.1):
`τ_w² G ∩ G = {0}`.

## Main results

* `determinant_spaces_properties`: the spaces, their norms, density and polynomial model.
* `tau_gap`: equation (H.1).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

abbrev K := RationalField (ZMod p) r
abbrev L := LaurentField (ZMod p) r
local instance preferredNormedFieldK : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance preferredFieldK : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField
local instance preferredFieldL : Field (L p r) :=
  (inferInstance : NontriviallyNormedField (L p r)).toField

abbrev A := TruncatedPolynomial.A (L p r) p
abbrev Tau := RationalLaurentScalars.AuxiliaryIndex p

instance : Fintype (Tau p) := Fintype.ofFinite _
instance : DecidableEq (Tau p) := Classical.decEq _

instance instNormedSpaceK : NormedSpace (K p r) (A p r) :=
  { (inferInstance : Module (K p r) (A p r)) with
    norm_smul_le := fun c x => by
      rw [← algebraMap_smul (L p r) c x]
      exact (norm_smul_le (algebraMap (K p r) (L p r) c) x).trans_eq
        (by rw [norm_algebraMap']) }

/-- The algebraically independent family of scalars: `a_i` at `inl i`, `τ_w` at `inr w`. -/
def z : Fin p ⊕ Tau p → L p r := RationalLaurentScalars.jointFamily p r (Tau p)

theorem algebraicIndependent_z : AlgebraicIndependent (K p r) (z p r) :=
  RationalLaurentScalars.algebraicIndependent_jointFamily p r (Tau p)

def tau (w : Tau p) : L p r := z p r (Sum.inr w)
def e (i : Fin p) : A p r := TruncatedPolynomial.basis (L p r) p i
def a : A p r := (TruncatedPolynomial.coeff (L p r) p).symm
  (fun i => z p r (Sum.inl i))

theorem e_eq_epsilon_pow (i : Fin p) :
    e p r i = TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ) :=
  TruncatedPolynomial.basis_eq_pow (L p r) p i

theorem a_expansion : a p r = ∑ i : Fin p, z p r (Sum.inl i) • e p r i :=
  (TruncatedPolynomial.basis (L p r) p).equivFun_symm_apply _

@[simp] theorem coeff_a (i : Fin p) :
    TruncatedPolynomial.coeff (L p r) p (a p r) i = z p r (Sum.inl i) := by
  simp [a]

/-- The vectors `w ∈ 𝒲`: `e_i`, and `e_i + e_j` for `i < j`. -/
def w : Tau p → A p r
  | Sum.inl i => e p r i
  | Sum.inr ij => e p r ij.val.1 + e p r ij.val.2

/-- `D₀ = span_K {e_i, ε^i a} + K a²`. -/
def D₀ : Submodule (K p r) (A p r) :=
  Submodule.span (K p r) (Set.range (Sum.elim (e p r) (fun i => e p r i * a p r))) ⊔
    (K p r) ∙ (a p r * a p r)

/-- `D = D₀ + ∑_w K τ_w w`, with the norm of `A`. -/
def D : Submodule (K p r) (A p r) :=
  D₀ p r ⊔ Submodule.span (K p r) (Set.range (fun t => tau p r t • w p r t))

/-- Indices of the generators of `D`. Equal generators with different indices stay distinct. -/
abbrev GeneratorIndex := Fin p ⊕ (Fin p ⊕ (Unit ⊕ Tau p))

def gen : GeneratorIndex p → A p r
  | Sum.inl i => e p r i
  | Sum.inr (Sum.inl i) => e p r i * a p r
  | Sum.inr (Sum.inr (Sum.inl _)) => a p r * a p r
  | Sum.inr (Sum.inr (Sum.inr t)) => tau p r t • w p r t

theorem D_eq_span_gen : D p r = Submodule.span (K p r) (Set.range (gen p r)) := by
  have hr : Set.range (gen p r) =
      Set.range (Sum.elim (e p r) (fun i => e p r i * a p r)) ∪
        {a p r * a p r} ∪ Set.range (fun t => tau p r t • w p r t) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases i with i | i
      · exact Or.inl (Or.inl ⟨Sum.inl i, rfl⟩)
      rcases i with i | i
      · exact Or.inl (Or.inl ⟨Sum.inr i, rfl⟩)
      rcases i with i | i
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨i, rfl⟩
    · rintro ((⟨i, rfl⟩ | rfl) | ⟨i, rfl⟩)
      · cases i with
        | inl i => exact ⟨Sum.inl i, rfl⟩
        | inr i => exact ⟨Sum.inr (Sum.inl i), rfl⟩
      · exact ⟨Sum.inr (Sum.inr (Sum.inl ())), rfl⟩
      · exact ⟨Sum.inr (Sum.inr (Sum.inr i)), rfl⟩
  rw [hr, Submodule.span_union, Submodule.span_union]
  rfl

theorem gen_mem_D (j : GeneratorIndex p) : gen p r j ∈ D p r := by
  rw [D_eq_span_gen]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem e_mem_D (i : Fin p) : e p r i ∈ D p r := gen_mem_D p r (Sum.inl i)

instance finiteDimensional_D : FiniteDimensional (K p r) (D p r) := by
  rw [D_eq_span_gen]
  exact FiniteDimensional.span_of_finite _ (Set.finite_range _)

/-- The determinant in the basis `e_i = ε^i`. -/
def delta (v : Fin p → A p r) : L p r :=
  Matrix.det (Matrix.of (fun i j => TruncatedPolynomial.coeff (L p r) p (v j) i))

/-- `G`, the `K`-span of determinants of tuples from `D`. -/
def G : Submodule (K p r) (L p r) :=
  Submodule.span (K p r) (Set.range (fun d : Fin p → D p r => delta p r (fun i => d i)))

/-- `G` carries the norm of `L`. -/
instance instNormedAddCommGroupG : NormedAddCommGroup (G p r) := inferInstance

instance instNormedSpaceG : NormedSpace (K p r) (G p r) := inferInstance

theorem delta_e : delta p r (e p r) = 1 := by
  have h : Matrix.of (fun i j => TruncatedPolynomial.coeff (L p r) p (e p r j) i) =
      (1 : Matrix (Fin p) (Fin p) (L p r)) := by
    ext i j
    simp [e, TruncatedPolynomial.coeff_basis, Matrix.one_apply, eq_comm]
  rw [delta, h, Matrix.det_one]

theorem one_mem_G : (1 : L p r) ∈ G p r := by
  rw [← delta_e p r]
  exact Submodule.subset_span ⟨fun i => ⟨e p r i, e_mem_D p r i⟩, rfl⟩

theorem G_eq_span_determinants : G p r = Submodule.span (K p r)
    (Set.range (fun s : Fin p → GeneratorIndex p => delta p r (fun i => gen p r (s i)))) := by
  unfold G
  rw [D_eq_span_gen]
  exact determinant_span_generator_tuples
    (TruncatedPolynomial.coeff (L p r) p).toLinearMap (gen p r)

instance finiteDimensional_G : FiniteDimensional (K p r) (G p r) := by
  rw [G_eq_span_determinants]
  exact FiniteDimensional.span_of_finite _ (Set.finite_range _)

theorem denseRange_D_subtype : DenseRange (D p r).subtypeₗᵢ := by
  apply denseRange_subtype_of_coordinate_basis
    (TruncatedPolynomial.coefficientIsometry (L p r) p) (D p r)
    (RationalField.denseRange_algebraMap (ZMod p) r)
  intro i
  have h : (TruncatedPolynomial.coefficientIsometry (L p r) p).symm
      (Pi.single i 1) = e p r i := by
    apply (TruncatedPolynomial.coefficientIsometry (L p r) p).injective
    ext j
    simp [e, TruncatedPolynomial.coeff_basis, Pi.single_apply, eq_comm]
  rw [h]
  exact e_mem_D p r i

theorem denseRange_G_subtype : DenseRange (G p r).subtypeₗᵢ :=
  denseRange_subtype_of_one (G p r)
    (RationalField.denseRange_algebraMap (ZMod p) r) (one_mem_G p r)

theorem norm_D (d : D p r) :
    ‖d‖ = (Finset.univ.sup fun i : Fin p =>
      ‖TruncatedPolynomial.coeff (L p r) p (d : A p r) i‖₊ : ℝ≥0) := rfl

theorem norm_G (c : G p r) : ‖c‖ = ‖(c : L p r)‖ := rfl

/-- The completion of `D` is `A`. -/
def completionD : UniformSpace.Completion (D p r) ≃ₗᵢ[K p r] A p r :=
  denseSubmoduleCompletionEquiv (D p r) (denseRange_D_subtype p r)

/-- The completion of `G` is `L`. -/
def completionG : UniformSpace.Completion (G p r) ≃ₗᵢ[K p r] L p r :=
  denseSubmoduleCompletionEquiv (G p r) (denseRange_G_subtype p r)

@[simp] theorem completionD_apply_coe (d : D p r) :
    completionD p r (d : UniformSpace.Completion (D p r)) = (d : A p r) :=
  denseSubmoduleCompletionEquiv_apply_coe _ _ d

@[simp] theorem completionG_apply_coe (c : G p r) :
    completionG p r (c : UniformSpace.Completion (G p r)) = (c : L p r) :=
  denseSubmoduleCompletionEquiv_apply_coe _ _ c

abbrev Poly := MvPolynomial (Fin p ⊕ Tau p) (K p r)

/-- Evaluation of polynomials at the family `z`, in `L`. -/
def evaluation : Poly p r →ₐ[K p r] L p r := MvPolynomial.aeval (z p r)

theorem evaluation_injective : Function.Injective (evaluation p r) :=
  algebraicIndependent_z p r

def ePoly (i k : Fin p) : Poly p r := if i = k then 1 else 0

def wPoly : Tau p → Fin p → Poly p r
  | Sum.inl i => ePoly p r i
  | Sum.inr ij => fun k => ePoly p r ij.val.1 k + ePoly p r ij.val.2 k

/-- Coordinate polynomials of the generators of `D`. -/
def genPoly : GeneratorIndex p → Fin p → Poly p r
  | Sum.inl i => ePoly p r i
  | Sum.inr (Sum.inl i) => fun k =>
      ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ)
        then MvPolynomial.X (Sum.inl j) else 0
  | Sum.inr (Sum.inr (Sum.inl _)) => fun k =>
      ∑ i : Fin p, ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ)
        then MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inl j) else 0
  | Sum.inr (Sum.inr (Sum.inr t)) => fun k =>
      MvPolynomial.X (Sum.inr t) * wPoly p r t k

@[simp] theorem evaluation_ePoly (i k : Fin p) :
    evaluation p r (ePoly p r i k) = TruncatedPolynomial.coeff (L p r) p (e p r i) k := by
  simp [ePoly, e, TruncatedPolynomial.coeff_basis, apply_ite]

@[simp] theorem evaluation_wPoly (t : Tau p) (k : Fin p) :
    evaluation p r (wPoly p r t k) = TruncatedPolynomial.coeff (L p r) p (w p r t) k := by
  cases t with
  | inl i => exact evaluation_ePoly p r i k
  | inr ij => simp [wPoly, w, map_add]

theorem evaluation_genPoly (j : GeneratorIndex p) (k : Fin p) :
    evaluation p r (genPoly p r j k) =
      TruncatedPolynomial.coeff (L p r) p (gen p r j) k := by
  rcases j with i | j
  · exact evaluation_ePoly p r i k
  rcases j with i | j
  · have hshift : TruncatedPolynomial.coeff (L p r) p (e p r i * a p r) k =
        ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ)
          then z p r (Sum.inl j) else 0 := by
      rw [TruncatedPolynomial.coeff_mul]
      simp only [e, TruncatedPolynomial.coeff_basis, coeff_a, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    simpa [genPoly, gen, apply_ite, evaluation] using hshift.symm
  rcases j with u | t
  · simp [genPoly, gen, TruncatedPolynomial.coeff_mul, apply_ite, evaluation]
  · simp [genPoly, gen, evaluation, tau, map_smul, smul_eq_mul,
      ← evaluation_wPoly]

/-- The polynomial determinant of a tuple of generators of `D`. -/
def detPoly (s : Fin p → GeneratorIndex p) : Poly p r :=
  Matrix.det (Matrix.of (fun i j => genPoly p r (s j) i))

def Gpoly : Submodule (K p r) (Poly p r) :=
  Submodule.span (K p r) (Set.range (detPoly p r))

theorem evaluation_detPoly (s : Fin p → GeneratorIndex p) :
    evaluation p r (detPoly p r s) = delta p r (fun i => gen p r (s i)) := by
  rw [detPoly, AlgHom.map_det]
  congr 1
  ext i j
  exact evaluation_genPoly p r (s j) i

instance finiteDimensional_Gpoly : FiniteDimensional (K p r) (Gpoly p r) :=
  FiniteDimensional.span_of_finite _ (Set.finite_range _)

theorem map_Gpoly : (Gpoly p r).map (evaluation p r).toLinearMap = G p r := by
  rw [Gpoly, Submodule.map_span, ← Set.range_comp, G_eq_span_determinants]
  congr 1
  ext c
  constructor <;> rintro ⟨s, rfl⟩ <;> refine ⟨s, ?_⟩
  · exact (evaluation_detPoly p r s).symm
  · exact evaluation_detPoly p r s

theorem existsUnique_polynomial_representative {c : L p r} (hc : c ∈ G p r) :
    ∃! P : Poly p r, P ∈ Gpoly p r ∧ evaluation p r P = c := by
  apply existsUnique_polynomial_rep_of_mem_map (z p r) (algebraicIndependent_z p r)
    (Gpoly p r)
  rwa [← map_Gpoly] at hc

open MvPolynomial

theorem degreeOf_ePoly_auxiliary (t : Tau p) (i k : Fin p) :
    degreeOf (Sum.inr t) (ePoly p r i k) ≤ 0 := by
  classical
  by_cases h : i = k <;> simp [ePoly, h]

theorem degreeOf_wPoly_auxiliary (t u : Tau p) (k : Fin p) :
    degreeOf (Sum.inr t) (wPoly p r u k) ≤ 0 := by
  cases u with
  | inl i => exact degreeOf_ePoly_auxiliary p r t i k
  | inr ij =>
      exact (degreeOf_add_le _ _ _).trans
        (max_le (degreeOf_ePoly_auxiliary p r t ij.val.1 k)
          (degreeOf_ePoly_auxiliary p r t ij.val.2 k))

theorem genPoly_degree_auxiliary_bound (t : Tau p) (j : GeneratorIndex p) (k : Fin p) :
    degreeOf (Sum.inr t) (genPoly p r j k) ≤
      if j = Sum.inr (Sum.inr (Sum.inr t)) then 1 else 0 := by
  classical
  rcases j with i | j
  · simpa only [genPoly, Sum.inr.injEq, reduceCtorEq, ↓reduceIte] using
      degreeOf_ePoly_auxiliary p r t i k
  rcases j with i | j
  · simp only [genPoly, Sum.inr.injEq, reduceCtorEq, ↓reduceIte]
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le ?_)
    intro b _
    split_ifs <;> simp [degreeOf_X]
  rcases j with u | u
  · simp only [genPoly, Sum.inr.injEq, reduceCtorEq, ↓reduceIte]
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le ?_)
    intro b _
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le ?_)
    intro c _
    split_ifs
    · exact (degreeOf_mul_le _ _ _).trans (by simp [degreeOf_X])
    · simp
  · simp only [genPoly, Sum.inr.injEq]
    refine (degreeOf_mul_le _ _ _).trans ?_
    have hw := degreeOf_wPoly_auxiliary p r t u k
    rw [Nat.le_zero] at hw
    rw [hw, Nat.add_zero]
    simp [degreeOf_X, eq_comm]

theorem degreeOf_mem_Gpoly (P : Poly p r) (hP : P ∈ Gpoly p r) (t : Tau p) :
    degreeOf (Sum.inr t) P ≤ 1 := by
  classical
  exact degreeOf_mem_span_det_column_family_le_one
    (genPoly p r) (Sum.inr (Sum.inr (Sum.inr t))) (Sum.inr t)
    (genPoly_degree_auxiliary_bound p r t) hP

/-- The properties of `D` and `G` stated before (H.1), collected: definitions, finite
dimension, norms, density, completions, and the polynomial model with degree at most one
in each `τ_w`. -/
theorem determinant_spaces_properties :
    AlgebraicIndependent (K p r) (z p r) ∧
    ¬ CompleteSpace (K p r) ∧ CompleteSpace (A p r) ∧ CompleteSpace (L p r) ∧
    (∀ i : Fin p, e p r i = TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ)) ∧
    a p r = ∑ i : Fin p, z p r (Sum.inl i) • e p r i ∧
    D₀ p r = Submodule.span (K p r)
      (Set.range (Sum.elim (e p r) (fun i => e p r i * a p r))) ⊔
        (K p r) ∙ (a p r * a p r) ∧
    D p r = D₀ p r ⊔ Submodule.span (K p r)
      (Set.range (fun t => tau p r t • w p r t)) ∧
    D p r = Submodule.span (K p r) (Set.range (gen p r)) ∧
    G p r = Submodule.span (K p r)
      (Set.range (fun d : Fin p → D p r => delta p r (fun i => d i))) ∧
    G p r = Submodule.span (K p r) (Set.range
      (fun s : Fin p → GeneratorIndex p => delta p r (fun i => gen p r (s i)))) ∧
    FiniteDimensional (K p r) (D p r) ∧ FiniteDimensional (K p r) (G p r) ∧
    (∀ i : Fin p, e p r i ∈ D p r) ∧ delta p r (e p r) = 1 ∧ (1 : L p r) ∈ G p r ∧
    (∀ d : D p r, ‖d‖ = (Finset.univ.sup fun i : Fin p =>
      ‖TruncatedPolynomial.coeff (L p r) p (d : A p r) i‖₊ : ℝ≥0)) ∧
    (∀ c : G p r, ‖c‖ = ‖(c : L p r)‖) ∧
    Isometry (D p r).subtypeₗᵢ ∧ DenseRange (D p r).subtypeₗᵢ ∧
    Isometry (G p r).subtypeₗᵢ ∧ DenseRange (G p r).subtypeₗᵢ ∧
    Isometry (completionD p r) ∧
    (∀ d : D p r, completionD p r (d : UniformSpace.Completion (D p r)) = (d : A p r)) ∧
    Isometry (completionG p r) ∧
    (∀ c : G p r, completionG p r (c : UniformSpace.Completion (G p r)) = (c : L p r)) ∧
    (∀ (j : GeneratorIndex p) (k : Fin p), evaluation p r (genPoly p r j k) =
      TruncatedPolynomial.coeff (L p r) p (gen p r j) k) ∧
    Gpoly p r = Submodule.span (K p r) (Set.range (detPoly p r)) ∧
    FiniteDimensional (K p r) (Gpoly p r) ∧
    (Gpoly p r).map (evaluation p r).toLinearMap = G p r ∧
    Function.Injective (evaluation p r) ∧
    (∀ c : L p r, c ∈ G p r →
      ∃! P : Poly p r, P ∈ Gpoly p r ∧ evaluation p r P = c) ∧
    (∀ P : Poly p r, P ∈ Gpoly p r → ∀ t : Tau p, degreeOf (Sum.inr t) P ≤ 1) := by
  exact ⟨algebraicIndependent_z p r, RationalField.not_completeSpace (ZMod p) r,
    inferInstance, inferInstance, e_eq_epsilon_pow p r, a_expansion p r,
    rfl, rfl, D_eq_span_gen p r, rfl, G_eq_span_determinants p r,
    inferInstance, inferInstance, e_mem_D p r, delta_e p r, one_mem_G p r,
    norm_D p r, norm_G p r, (D p r).subtypeₗᵢ.isometry, denseRange_D_subtype p r,
    (G p r).subtypeₗᵢ.isometry, denseRange_G_subtype p r,
    (completionD p r).isometry, completionD_apply_coe p r,
    (completionG p r).isometry, completionG_apply_coe p r,
    evaluation_genPoly p r, rfl, inferInstance, map_Gpoly p r, evaluation_injective p r,
    fun _ => existsUnique_polynomial_representative p r, degreeOf_mem_Gpoly p r⟩

/-- If `c ∈ G` and `τ_w² c ∈ G`, then `c = 0`. -/
theorem eq_zero_of_tau_sq_mul_mem (t : Tau p) {c : L p r}
    (hc : c ∈ G p r) (htc : tau p r t ^ 2 * c ∈ G p r) : c = 0 := by
  rw [← map_Gpoly] at hc htc
  exact aeval_square_scalar_gap (z p r) (algebraicIndependent_z p r) (Gpoly p r)
    (Sum.inr t) (fun P hP => degreeOf_mem_Gpoly p r P hP t) hc htc

/-- Equation (H.1): `τ_w² G ∩ G = {0}`. -/
theorem tau_sq_image_intersection (t : Tau p) :
    (fun c : L p r => tau p r t ^ 2 * c) '' (G p r : Set (L p r)) ∩
      (G p r : Set (L p r)) = {0} := by
  rw [← map_Gpoly]
  exact aeval_square_scalar_image_intersection (z p r) (algebraicIndependent_z p r)
    (Gpoly p r) (Sum.inr t) (fun P hP => degreeOf_mem_Gpoly p r P hP t)

/-- Both forms of the gap (H.1). -/
theorem tau_gap :
    (∀ (t : Tau p) (c : L p r), c ∈ G p r → tau p r t ^ 2 * c ∈ G p r → c = 0) ∧
    (∀ t : Tau p, (fun c : L p r => tau p r t ^ 2 * c) '' (G p r : Set (L p r)) ∩
      (G p r : Set (L p r)) = {0}) :=
  ⟨fun t _ => eq_zero_of_tau_sq_mul_mem p r t, tau_sq_image_intersection p r⟩

end AlternatingAnalytic.DeterminantPair
