import AlternatingAnalytic.Analysis.LaurentEvaluation
import AlternatingAnalytic.Analysis.DenseIsometricExtension

/-! Isometric Laurent fields in prescribed complete ultrametric fields. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal nonZeroDivisors RatFunc

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] [Finite κ]
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Rational-function evaluation is defined because a small nonzero element is transcendental. -/
def ratFuncEvaluation (f : κ →+* K) (t : K) (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1) :
    RatFunc κ →+* K :=
  RatFunc.liftRingHom (Polynomial.eval₂RingHom f t) (by
    intro p hp
    change Polynomial.eval₂RingHom f t p ∈ nonZeroDivisors K
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hz
    apply nonZeroDivisors.ne_zero hp
    apply polynomial_eval₂_injective f t ht0 ht1
    simpa using hz)

@[simp]
theorem ratFuncEvaluation_polynomial (f : κ →+* K) (t : K)
    (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1) (p : Polynomial κ) :
    ratFuncEvaluation κ f t ht0 ht1 (algebraMap (Polynomial κ) (RatFunc κ) p) = p.eval₂ f t :=
  RatFunc.liftRingHom_algebraMap _ _ _

variable (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

theorem norm_ratFuncEvaluation (f : κ →+* K) (t : K) (ht0 : t ≠ 0)
    (ht1 : ‖t‖ < 1) (ht : ‖t‖ = r) (q : RatFunc κ) :
    ‖ratFuncEvaluation κ f t ht0 ht1 q‖ = ‖ratFuncToLaurentField κ r q‖ := by
  induction q using RatFunc.induction_on with
  | f p q hq =>
    rw [map_div₀, map_div₀, norm_div, norm_div,
      ratFuncEvaluation_polynomial, ratFuncEvaluation_polynomial,
      ratFuncToLaurentField_polynomial, ratFuncToLaurentField_polynomial,
      norm_polynomial_eval₂_eq_laurent κ r f t ht p,
      norm_polynomial_eval₂_eq_laurent κ r f t ht q]

variable [CompleteSpace K]

/-- A complete ultrametric field contains the Laurent field at every finite-field small parameter. -/
theorem exists_isometric_laurentField_embedding (f : κ →+* K) (t : K) (ht : ‖t‖ = r) :
    ∃ g : LaurentField κ r →+* K, Isometry g ∧
      IsClosed (Set.range g) ∧
      closure (Set.range (g.comp (ratFuncToLaurentField κ r))) = Set.range g ∧
      (∀ c : κ, g (algebraMap κ (LaurentField κ r) c) = f c) ∧
      g (polynomialToLaurentField κ r Polynomial.X) = t := by
  let i := ratFuncToLaurentField κ r
  let : NormedField (RatFunc κ) := NormedField.induced (RatFunc κ) (LaurentField κ r) i i.injective
  have hi : Isometry i := AddMonoidHomClass.isometry_of_norm i (fun _ => rfl)
  have hd : DenseRange i := LaurentSeries.coe_range_dense
  have ht0 : t ≠ 0 := norm_pos_iff.mp
    (ht.symm ▸ (show (0 : ℝ) < r from (show 0 < r from Fact.out)))
  have ht1 : ‖t‖ < 1 := ht.symm ▸ (show (r : ℝ) < 1 from (show r < 1 from Fact.out))
  let e := ratFuncEvaluation κ f t ht0 ht1
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e (norm_ratFuncEvaluation κ r f t ht0 ht1 ht)
  obtain ⟨g, hg, hfix⟩ := exists_isometric_ringHom_extension i e hi hd he
  refine ⟨g, hg, hg.isClosedEmbedding.isClosed_range,
    closure_range_comp_eq_range i g hd hg, ?_, ?_⟩
  · intro c
    have h := hfix (algebraMap (Polynomial κ) (RatFunc κ) (Polynomial.C c))
    simpa only [i, e, ratFuncToLaurentField_polynomial, polynomialToLaurentField_C,
      ratFuncEvaluation_polynomial, Polynomial.eval₂_C] using h
  · have h := hfix (algebraMap (Polynomial κ) (RatFunc κ) Polynomial.X)
    simpa only [i, e, ratFuncToLaurentField_polynomial, ratFuncEvaluation_polynomial,
      Polynomial.eval₂_X] using h

/-- The isometric embedding supplies the normed algebra used for projective base change. -/
@[instance_reducible]
def laurentFieldNormedAlgebra (g : LaurentField κ r →+* K) (hg : Isometry g) :
    NormedAlgebra (LaurentField κ r) K where
  __ := g.toAlgebra
  norm_smul_le c x := by
    change ‖g c * x‖ ≤ ‖c‖ * ‖x‖
    rw [norm_mul, (AddMonoidHomClass.isometry_iff_norm g).mp hg]

/-- Every prescribed complete positive-characteristic field admits an isometric Laurent base. -/
theorem exists_laurentField_normedAlgebra (K' : Type*) [NontriviallyNormedField K']
    [CompleteSpace K'] (p : ℕ) [Fact p.Prime] [CharP K' p] :
    ∃ (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1),
      letI : Fact (0 < r) := ⟨hr0⟩
      letI : Fact (r < 1) := ⟨hr1⟩
      Nonempty (NormedAlgebra (LaurentField (ZMod p) r) K') := by
  let : IsUltrametricDist K' := charP_isUltrametricDist p
  obtain ⟨t, ht0, ht1⟩ := NormedField.exists_nnnorm_lt_one K'
  refine ⟨‖t‖₊, ht0, ht1, ?_⟩
  let : Fact (0 < ‖t‖₊) := ⟨ht0⟩
  let : Fact (‖t‖₊ < 1) := ⟨ht1⟩
  obtain ⟨g, hg, -⟩ := exists_isometric_laurentField_embedding (ZMod p) ‖t‖₊
    (ZMod.castHom (dvd_refl p) K') t rfl
  exact ⟨laurentFieldNormedAlgebra (ZMod p) ‖t‖₊ g hg⟩

end AlternatingAnalytic
