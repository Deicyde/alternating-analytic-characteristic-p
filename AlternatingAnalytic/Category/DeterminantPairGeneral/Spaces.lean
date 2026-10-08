import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Analysis.TruncatedPolynomialMaxNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import AlternatingAnalytic.Analysis.DeterminantSpan
import AlternatingAnalytic.Analysis.DeterminantDensity
import AlternatingAnalytic.Analysis.DeterminantPolynomialDegree

/-!
# Determinant pairs for an arbitrary algebraically independent family

This file sets up the determinant pair `(D, G)` of Appendix H.1 for an arbitrary family
`z : Fin p ⊕ Tau p → 𝔽_p((t))` of scalars `a_i = z (inl i)`, `τ_w = z (inr w)`, with the
definitions spelled exactly as in the ledger challenge for Lemma H.6. When `z` is algebraically
independent over `𝔽_p(t)`, every element of `G` has a unique polynomial representative of degree
at most one in each auxiliary variable, which gives the gap `τ_w² G ∩ G = 0` (H.1).
-/

namespace AlternatingAnalytic.DeterminantPairGeneral

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

/-! ### Generators -/

variable (z : Fin p ⊕ Tau p → Lt p r)

theorem e_eq_basis (i : Fin p) :
    e p r i = TruncatedPolynomial.basis (Lt p r) p i :=
  (TruncatedPolynomial.basis_eq_pow (Lt p r) p i).symm

@[simp] theorem coeff_e (i k : Fin p) :
    TruncatedPolynomial.coeff (Lt p r) p (e p r i) k = if i = k then 1 else 0 := by
  rw [e_eq_basis, TruncatedPolynomial.coeff_basis]

@[simp] theorem coeff_a (i : Fin p) :
    TruncatedPolynomial.coeff (Lt p r) p (a z) i = z (Sum.inl i) := by
  simp [a, map_sum, Finset.sum_apply, Pi.smul_apply]

variable (p) in
/-- Tagged generators of `D`. -/
abbrev GeneratorIndex := Fin p ⊕ (Fin p ⊕ (Unit ⊕ Tau p))

instance : DecidableEq (GeneratorIndex p) :=
  have : DecidableEq (Tau p) := inferInstance
  have : DecidableEq (Unit ⊕ Tau p) := inferInstance
  have : DecidableEq (Fin p ⊕ (Unit ⊕ Tau p)) := inferInstance
  inferInstanceAs (DecidableEq (Fin p ⊕ (Fin p ⊕ (Unit ⊕ Tau p))))

/-- The listed generators of `D`. -/
def gen : GeneratorIndex p → A p r
  | Sum.inl i => e p r i
  | Sum.inr (Sum.inl i) => e p r i * a z
  | Sum.inr (Sum.inr (Sum.inl _)) => a z * a z
  | Sum.inr (Sum.inr (Sum.inr t)) => z (Sum.inr t) • w p r t

theorem D_eq_span_gen : D z = Submodule.span (Kt p r) (Set.range (gen z)) := by
  have hr : Set.range (gen z) =
      Set.range (Sum.elim (e p r) (fun i => e p r i * a z)) ∪
        {a z * a z} ∪ Set.range (fun t => z (Sum.inr t) • w p r t) := by
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

theorem gen_mem_D (j : GeneratorIndex p) : gen z j ∈ D z := by
  rw [D_eq_span_gen]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem e_mem_D (i : Fin p) : e p r i ∈ D z := gen_mem_D z (Sum.inl i)

theorem w_mem_D (t : Tau p) : w p r t ∈ D z := by
  cases t with
  | inl b => exact e_mem_D z b
  | inr bc => exact (D z).add_mem (e_mem_D z bc.val.1) (e_mem_D z bc.val.2)

theorem tau_smul_w_mem_D (t : Tau p) : z (Sum.inr t) • w p r t ∈ D z :=
  gen_mem_D z (Sum.inr (Sum.inr (Sum.inr t)))

theorem G_eq_span_determinants : G z = Submodule.span (Kt p r)
    (Set.range (fun s : Fin p → GeneratorIndex p => det p r (fun i => gen z (s i)))) := by
  unfold G
  rw [D_eq_span_gen]
  exact determinant_span_generator_tuples
    (TruncatedPolynomial.coeff (Lt p r) p).toLinearMap (gen z)

theorem denseRange_D_subtype : DenseRange (D z).subtypeₗᵢ := by
  apply denseRange_subtype_of_coordinate_basis
    (TruncatedPolynomial.coefficientIsometry (Lt p r) p) (D z)
    (RationalField.denseRange_algebraMap (ZMod p) r)
  intro i
  have h : (TruncatedPolynomial.coefficientIsometry (Lt p r) p).symm
      (Pi.single i 1) = e p r i := by
    apply (TruncatedPolynomial.coefficientIsometry (Lt p r) p).injective
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [h]
  exact e_mem_D z i

/-! ### Polynomial representatives -/

variable (p r) in
/-- Polynomials in the joint family of variables. -/
abbrev Poly := MvPolynomial (Fin p ⊕ Tau p) (Kt p r)

/-- Evaluation at the family `z`. -/
def evaluation : Poly p r →ₐ[Kt p r] Lt p r := MvPolynomial.aeval z

variable (p r) in
/-- Coordinates of `e_i`. -/
def ePoly (i k : Fin p) : Poly p r := if i = k then 1 else 0

variable (p r) in
/-- Coordinates of the elements of `𝒲`. -/
def wPoly : Tau p → Fin p → Poly p r
  | Sum.inl i => ePoly p r i
  | Sum.inr ij => fun k => ePoly p r ij.val.1 k + ePoly p r ij.val.2 k

variable (p r) in
/-- Coordinate lifts of the generators, using truncated convolution. -/
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
    evaluation z (ePoly p r i k) = TruncatedPolynomial.coeff (Lt p r) p (e p r i) k := by
  simp [ePoly, apply_ite]

@[simp] theorem evaluation_wPoly (t : Tau p) (k : Fin p) :
    evaluation z (wPoly p r t k) = TruncatedPolynomial.coeff (Lt p r) p (w p r t) k := by
  cases t with
  | inl i => exact evaluation_ePoly z i k
  | inr ij => simp only [wPoly, w, map_add, evaluation_ePoly, Pi.add_apply]

theorem evaluation_genPoly (j : GeneratorIndex p) (k : Fin p) :
    evaluation z (genPoly p r j k) =
      TruncatedPolynomial.coeff (Lt p r) p (gen z j) k := by
  rcases j with i | j
  · exact evaluation_ePoly z i k
  rcases j with i | j
  · have hshift : TruncatedPolynomial.coeff (Lt p r) p (e p r i * a z) k =
        ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ)
          then z (Sum.inl j) else 0 := by
      rw [TruncatedPolynomial.coeff_mul]
      simp only [coeff_e, coeff_a, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    simpa [genPoly, gen, apply_ite, evaluation] using hshift.symm
  rcases j with u | t
  · simp [genPoly, gen, TruncatedPolynomial.coeff_mul, apply_ite, evaluation]
  · have h := evaluation_wPoly z t k
    simp only [genPoly, gen, map_mul, map_smul, Pi.smul_apply, smul_eq_mul, ← h]
    simp [evaluation]

/-- Symbolic determinants of tuples of generators. -/
def detPoly (s : Fin p → GeneratorIndex p) : Poly p r :=
  Matrix.det (Matrix.of (fun i j => genPoly p r (s j) i))

variable (p r) in
/-- The polynomial model of `G`. -/
def Gpoly : Submodule (Kt p r) (Poly p r) :=
  Submodule.span (Kt p r) (Set.range (detPoly (p := p) (r := r)))

theorem evaluation_detPoly (s : Fin p → GeneratorIndex p) :
    evaluation z (detPoly s) = det p r (fun i => gen z (s i)) := by
  rw [detPoly, AlgHom.map_det]
  congr 1
  ext i j
  exact evaluation_genPoly z (s j) i

theorem map_Gpoly : (Gpoly p r).map (evaluation z).toLinearMap = G z := by
  rw [Gpoly, Submodule.map_span, ← Set.range_comp, G_eq_span_determinants]
  congr 1
  ext c
  constructor <;> rintro ⟨s, rfl⟩ <;> refine ⟨s, ?_⟩
  · exact (evaluation_detPoly z s).symm
  · exact evaluation_detPoly z s

open MvPolynomial

theorem degreeOf_ePoly_auxiliary (t : Tau p) (i k : Fin p) :
    degreeOf (Sum.inr t) (ePoly p r i k) ≤ 0 := by
  classical
  by_cases h : i = k <;> simp [ePoly, h]

theorem degreeOf_wPoly_auxiliary (t u : Tau p) (k : Fin p) :
    degreeOf (Sum.inr t) (wPoly p r u k) ≤ 0 := by
  cases u with
  | inl i => exact degreeOf_ePoly_auxiliary t i k
  | inr ij =>
      exact (degreeOf_add_le _ _ _).trans
        (max_le (degreeOf_ePoly_auxiliary t ij.val.1 k)
          (degreeOf_ePoly_auxiliary t ij.val.2 k))

theorem genPoly_degree_auxiliary_bound (t : Tau p) (j : GeneratorIndex p) (k : Fin p) :
    degreeOf (Sum.inr t) (genPoly p r j k) ≤
      if j = Sum.inr (Sum.inr (Sum.inr t)) then 1 else 0 := by
  classical
  rcases j with i | j
  · simpa only [genPoly, Sum.inr.injEq, reduceCtorEq, ↓reduceIte] using
      degreeOf_ePoly_auxiliary (p := p) (r := r) t i k
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
    have hw := degreeOf_wPoly_auxiliary (p := p) (r := r) t u k
    rw [Nat.le_zero] at hw
    rw [hw, Nat.add_zero]
    simp [degreeOf_X, eq_comm]

theorem degreeOf_mem_Gpoly (P : Poly p r) (hP : P ∈ Gpoly p r) (t : Tau p) :
    degreeOf (Sum.inr t) P ≤ 1 := by
  exact degreeOf_mem_span_det_column_family_le_one
    (genPoly p r) (Sum.inr (Sum.inr (Sum.inr t))) (Sum.inr t)
    (genPoly_degree_auxiliary_bound t) hP

/-- (H.1): for an algebraically independent family, `τ_w² c ∈ G` with `c ∈ G` forces `c = 0`. -/
theorem eq_zero_of_tau_sq_mul_mem (hz : AlgebraicIndependent (Kt p r) z) (t : Tau p)
    {c : Lt p r} (hc : c ∈ G z) (htc : z (Sum.inr t) ^ 2 * c ∈ G z) : c = 0 := by
  rw [← map_Gpoly] at hc htc
  exact aeval_square_scalar_gap z hz (Gpoly p r)
    (Sum.inr t) (fun P hP => degreeOf_mem_Gpoly P hP t) hc htc

end

end AlternatingAnalytic.DeterminantPairGeneral
