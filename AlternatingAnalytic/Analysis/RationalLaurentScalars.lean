import AlternatingAnalytic.Analysis.LaurentEvaluation
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The fields `K = F_p(t)` and `L = F_p((t))` with an `X`-adic norm

`RationalField κ r` is `RatFunc κ` with the norm `‖q‖ = r ^ ord q` induced from the Laurent
field. It is countable, incomplete and dense in `LaurentField κ r`, which is uncountable. Hence
`L` contains algebraically independent tuples over `K` of every finite size. This is the scalar
setup of Appendix H, before Lemma H.5.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal Cardinal

namespace AlternatingAnalytic

/-- Rational functions over `κ`; the radius `r` of the norm is part of the type. -/
def RationalField (κ : Type*) [Field κ] (_r : ℝ≥0) := RatFunc κ

namespace RationalField

variable (κ : Type*) [Field κ] (r : ℝ≥0)

instance : Field (RationalField κ r) := inferInstanceAs (Field (RatFunc κ))

instance : Algebra κ (RationalField κ r) := inferInstanceAs (Algebra κ (RatFunc κ))

instance (p : ℕ) [CharP κ p] : CharP (RationalField κ r) p :=
  inferInstanceAs (CharP (RatFunc κ) p)

/-- The inclusion of rational functions into the Laurent field. -/
def toLaurentField : RationalField κ r →+* LaurentField κ r :=
  ratFuncToLaurentField κ r

/-- The variable `X` as a rational function. -/
def X : RationalField κ r := algebraMap (Polynomial κ) (RatFunc κ) Polynomial.X

@[simp]
theorem toLaurentField_X :
    toLaurentField κ r (X κ r) = polynomialToLaurentField κ r Polynomial.X :=
  ratFuncToLaurentField_polynomial κ r Polynomial.X

instance : Algebra (RationalField κ r) (LaurentField κ r) :=
  (toLaurentField κ r).toAlgebra

@[simp]
theorem algebraMap_eq :
    algebraMap (RationalField κ r) (LaurentField κ r) = toLaurentField κ r := rfl

/-- The valuation is the `X`-adic valuation of rational functions. -/
theorem valuation_eq (q : RationalField κ r) :
    RatFunc.polynomialValuationX κ q =
      Valued.v (show LaurentSeries κ from toLaurentField κ r q) :=
  RatFunc.valuation_eq_LaurentSeries_valuation κ q

instance [Countable κ] : Countable (RationalField κ r) := by
  change Countable (RatFunc κ)
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [IsFractionRing.cardinalMk (Polynomial κ) (RatFunc κ),
    Polynomial.cardinalMk_eq_max]
  exact max_le Cardinal.mk_le_aleph0 le_rfl

variable [Fact (0 < r)] [Fact (r < 1)]

instance : NormedField (RationalField κ r) :=
  NormedField.induced (RationalField κ r) (LaurentField κ r)
    (toLaurentField κ r) (toLaurentField κ r).injective

@[simp]
theorem norm_toLaurentField (q : RationalField κ r) :
    ‖toLaurentField κ r q‖ = ‖q‖ := rfl

@[simp]
theorem norm_X : ‖X κ r‖ = r := by
  rw [← norm_toLaurentField, toLaurentField_X, norm_polynomialToLaurentField_X]

instance : NontriviallyNormedField (RationalField κ r) :=
  .ofNormNeOne ⟨X κ r,
    norm_pos_iff.mp (by rw [norm_X]; exact NNReal.coe_pos.mpr Fact.out),
    by rw [norm_X]; exact ne_of_lt (NNReal.coe_lt_one.mpr Fact.out)⟩

instance : NormedAlgebra (RationalField κ r) (LaurentField κ r) where
  __ := (toLaurentField κ r).toAlgebra
  norm_smul_le q x := by
    change ‖toLaurentField κ r q * x‖ ≤ ‖q‖ * ‖x‖
    rw [norm_mul, norm_toLaurentField]

/-- The inclusion into the Laurent field is an isometry. -/
theorem isometry_toLaurentField : Isometry (toLaurentField κ r) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_toLaurentField κ r)

/-- Rational functions are dense in the Laurent field. -/
theorem denseRange_toLaurentField : DenseRange (toLaurentField κ r) :=
  LaurentSeries.coe_range_dense

theorem isometry_algebraMap :
    Isometry (algebraMap (RationalField κ r) (LaurentField κ r)) :=
  isometry_toLaurentField κ r

theorem denseRange_algebraMap :
    DenseRange (algebraMap (RationalField κ r) (LaurentField κ r)) :=
  denseRange_toLaurentField κ r

/-- `‖q‖ = r ^ ord q`, the order taken in the Laurent expansion. -/
theorem norm_of_ne_zero (q : RationalField κ r) (hq : q ≠ 0) :
    ‖q‖ = (r : ℝ) ^ (show LaurentSeries κ from toLaurentField κ r q).order :=
  LaurentField.norm_of_ne_zero κ r _ ((map_ne_zero (toLaurentField κ r)).mpr hq)

instance : IsUltrametricDist (RationalField κ r) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (fun x y => by
    simpa only [← norm_toLaurentField, map_add] using
      IsUltrametricDist.norm_add_le_max (toLaurentField κ r x) (toLaurentField κ r y))

/-- Over a countable field `κ`, the rational field is not complete. -/
theorem not_completeSpace [Countable κ] : ¬ CompleteSpace (RationalField κ r) := by
  intro h
  let := h
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum)
    ((continuum_le_cardinal_of_nontriviallyNormedField (RationalField κ r)).trans
      Cardinal.mk_le_aleph0)

end RationalField

/-- The Laurent field is uncountable, being complete and nontrivially normed. -/
theorem laurentField_uncountable (κ : Type*) [Field κ] (r : ℝ≥0)
    [Fact (0 < r)] [Fact (r < 1)] : Uncountable (LaurentField κ r) :=
  Cardinal.aleph0_lt_mk_iff.mp (Cardinal.aleph0_lt_continuum.trans_le
    (continuum_le_cardinal_of_nontriviallyNormedField (LaurentField κ r)))

/-- An uncountable extension of a countable field contains algebraically independent tuples
of every finite size. -/
theorem exists_finite_algebraicIndependent_of_uncountable
    (K L : Type) [Field K] [Field L] [Algebra K L] [Countable K]
    (hL : Cardinal.aleph0 < Cardinal.mk L) (I : Type*) [Finite I] :
    ∃ z : I → L, AlgebraicIndependent K z := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  have htrans : Algebra.Transcendental K L := by
    rw [Algebra.transcendental_iff_not_isAlgebraic]
    intro h_alg
    let : Algebra.IsAlgebraic K L := h_alg
    have hcard := Algebra.IsAlgebraic.cardinalMk_le_max K L
    exact (not_le_of_gt hL) (hcard.trans (max_le Cardinal.mk_le_aleph0 le_rfl))
  let : Nonempty s := hs.nonempty_iff_transcendental.mpr htrans
  have hinf : Infinite s := by
    rw [Cardinal.infinite_iff]
    by_contra h
    have hs_card : Cardinal.mk s ≤ Cardinal.aleph0 := (lt_of_not_ge h).le
    have hcard : Cardinal.mk L = Cardinal.mk K ⊔ Cardinal.mk s ⊔ Cardinal.aleph0 := by
      simpa only [Cardinal.lift_id] using hs.lift_cardinalMk_eq_max_lift
    exact (not_le_of_gt hL) (hcard.le.trans
      (max_le (max_le Cardinal.mk_le_aleph0 hs_card) le_rfl))
  let : Infinite s := hinf
  let : Fintype I := Fintype.ofFinite I
  let e : I ↪ s := (Fintype.equivFin I).toEmbedding.trans
    (Fin.valEmbedding.trans (Infinite.natEmbedding s))
  exact ⟨Subtype.val ∘ e, hs.1.comp e e.injective⟩

namespace RationalLaurentScalars

/-- Indices for the vectors `e_i` and `e_i + e_j` (`i < j`) of the set `𝒲` in Appendix H. -/
def AuxiliaryIndex (p : ℕ) := Fin p ⊕ {ij : Fin p × Fin p // ij.1 < ij.2}

instance (p : ℕ) : Finite (AuxiliaryIndex p) :=
  inferInstanceAs (Finite (Fin p ⊕ {ij : Fin p × Fin p // ij.1 < ij.2}))

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

/-- The scalars `a_i` and the auxiliary scalars `τ_w` can be chosen jointly algebraically
independent over `K`. -/
theorem exists_jointly_algebraicIndependent (Tau : Type*) [Finite Tau] :
    ∃ z : Fin p ⊕ Tau → LaurentField (ZMod p) r,
      AlgebraicIndependent (RationalField (ZMod p) r) z :=
  exists_finite_algebraicIndependent_of_uncountable
    (RationalField (ZMod p) r) (LaurentField (ZMod p) r)
    (Cardinal.aleph0_lt_mk_iff.mpr (laurentField_uncountable (ZMod p) r)) (Fin p ⊕ Tau)

/-- A chosen jointly independent family of scalars `a_i` and `τ_w`. -/
def jointFamily (Tau : Type*) [Finite Tau] : Fin p ⊕ Tau → LaurentField (ZMod p) r :=
  Classical.choose (exists_jointly_algebraicIndependent p r Tau)

theorem algebraicIndependent_jointFamily (Tau : Type*) [Finite Tau] :
    AlgebraicIndependent (RationalField (ZMod p) r) (jointFamily p r Tau) :=
  Classical.choose_spec (exists_jointly_algebraicIndependent p r Tau)

/-- The scalars `a_i`. -/
def a (Tau : Type*) [Finite Tau] (i : Fin p) : LaurentField (ZMod p) r :=
  jointFamily p r Tau (Sum.inl i)

/-- The auxiliary scalars `τ_w`. -/
def tau (Tau : Type*) [Finite Tau] (w : Tau) : LaurentField (ZMod p) r :=
  jointFamily p r Tau (Sum.inr w)

theorem algebraicIndependent_a_tau (Tau : Type*) [Finite Tau] :
    AlgebraicIndependent (RationalField (ZMod p) r)
      (Sum.elim (a p r Tau) (tau p r Tau)) := by
  convert algebraicIndependent_jointFamily p r Tau using 1
  funext i
  cases i <;> rfl

theorem algebraicIndependent_a (Tau : Type*) [Finite Tau] :
    AlgebraicIndependent (RationalField (ZMod p) r) (a p r Tau) :=
  (algebraicIndependent_jointFamily p r Tau).comp Sum.inl Sum.inl_injective

theorem algebraicIndependent_tau (Tau : Type*) [Finite Tau] :
    AlgebraicIndependent (RationalField (ZMod p) r) (tau p r Tau) :=
  (algebraicIndependent_jointFamily p r Tau).comp Sum.inr Sum.inr_injective

/-- The `a_i` and `τ_w`, `w ∈ 𝒲`, are jointly algebraically independent over `K`. -/
theorem algebraicIndependent_auxiliaryScalars :
    AlgebraicIndependent (RationalField (ZMod p) r)
      (Sum.elim (a p r (AuxiliaryIndex p)) (tau p r (AuxiliaryIndex p))) :=
  algebraicIndependent_a_tau p r (AuxiliaryIndex p)

/-- The field and scalar setup of Appendix H preceding Lemma H.5: `K` countable and incomplete,
dense and isometric in the complete uncountable `L`, and the scalars `a_i`, `τ_w` restricted from
one algebraically independent family `z`. -/
theorem concrete_setup :
    let K := RationalField (ZMod p) r
    let L := LaurentField (ZMod p) r
    let ι := RationalField.toLaurentField (ZMod p) r
    let z := jointFamily p r (AuxiliaryIndex p)
    Nonempty (NontriviallyNormedField K) ∧
    Nonempty (NontriviallyNormedField L) ∧
    Nonempty (NormedAlgebra K L) ∧
    (∃ q : K, 1 < ‖q‖) ∧
    (∃ x : L, 1 < ‖x‖) ∧
    CharP K p ∧ CharP L p ∧
    IsUltrametricDist K ∧ IsUltrametricDist L ∧
    Countable K ∧ Uncountable L ∧
    ¬ CompleteSpace K ∧ CompleteSpace L ∧
    ι = ratFuncToLaurentField (ZMod p) r ∧
    algebraMap K L = ι ∧
    Isometry ι ∧ DenseRange ι ∧
    Isometry (algebraMap K L) ∧ DenseRange (algebraMap K L) ∧
    (∀ q : K, ‖ι q‖ = ‖q‖) ∧
    (∀ (q : K) (x : L), ‖q • x‖ = ‖q‖ * ‖x‖) ∧
    ι (RationalField.X (ZMod p) r) = polynomialToLaurentField (ZMod p) r Polynomial.X ∧
    ‖RationalField.X (ZMod p) r‖ = (r : ℝ) ∧
    (∀ q : K, RatFunc.polynomialValuationX (ZMod p) q =
      Valued.v (show LaurentSeries (ZMod p) from ι q)) ∧
    (∀ q : K, q ≠ 0 →
      ‖q‖ = (r : ℝ) ^ (show LaurentSeries (ZMod p) from ι q).order) ∧
    (∀ x : L, x ≠ 0 →
      ‖x‖ = (r : ℝ) ^ (show LaurentSeries (ZMod p) from x).order) ∧
    (∀ (Tau : Type*) [Finite Tau],
      ∃ family : Fin p ⊕ Tau → L, AlgebraicIndependent K family) ∧
    AlgebraicIndependent K z ∧
    (∀ i, a p r (AuxiliaryIndex p) i = z (Sum.inl i)) ∧
    (∀ w, tau p r (AuxiliaryIndex p) w = z (Sum.inr w)) ∧
    Sum.elim (a p r (AuxiliaryIndex p)) (tau p r (AuxiliaryIndex p)) = z ∧
    AlgebraicIndependent K
      (Sum.elim (a p r (AuxiliaryIndex p)) (tau p r (AuxiliaryIndex p))) ∧
    AlgebraicIndependent K (a p r (AuxiliaryIndex p)) ∧
    AlgebraicIndependent K (tau p r (AuxiliaryIndex p)) := by
  refine ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
    NormedField.exists_one_lt_norm _, NormedField.exists_one_lt_norm _,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, laurentField_uncountable (ZMod p) r,
    RationalField.not_completeSpace (ZMod p) r, inferInstance,
    rfl, RationalField.algebraMap_eq (ZMod p) r,
    RationalField.isometry_toLaurentField (ZMod p) r,
    RationalField.denseRange_toLaurentField (ZMod p) r,
    RationalField.isometry_algebraMap (ZMod p) r,
    RationalField.denseRange_algebraMap (ZMod p) r,
    RationalField.norm_toLaurentField (ZMod p) r, fun q x => norm_smul q x,
    RationalField.toLaurentField_X (ZMod p) r, RationalField.norm_X (ZMod p) r,
    RationalField.valuation_eq (ZMod p) r, RationalField.norm_of_ne_zero (ZMod p) r,
    LaurentField.norm_of_ne_zero (ZMod p) r, exists_jointly_algebraicIndependent p r,
    algebraicIndependent_jointFamily p r (AuxiliaryIndex p),
    fun _ => rfl, fun _ => rfl, ?_, algebraicIndependent_auxiliaryScalars p r,
    algebraicIndependent_a p r (AuxiliaryIndex p),
    algebraicIndependent_tau p r (AuxiliaryIndex p)⟩
  funext i
  cases i <;> rfl

end RationalLaurentScalars

end AlternatingAnalytic
