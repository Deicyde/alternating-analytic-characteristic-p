import AlternatingAnalytic.Analysis.DeterminantPairScalars
import AlternatingAnalytic.Analysis.RigidDenseSourceConcrete
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant values on the rigid source

The rigid source `E = K^p + K a` lies in `D`, and determinants of tuples from `E` span
`span_K {1, a_0, ..., a_{p-1}}` (`delta_span_E`). This is the span computation behind
equation (H.2) in Appendix H.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

abbrev E := RigidDenseSource.Concrete.source p r

@[simp] theorem concrete_a_eq (i : Fin p) :
    RigidDenseSource.Concrete.a p r i = z p r (Sum.inl i) := rfl

@[simp] theorem concrete_vector_eq : RigidDenseSource.Concrete.vector p r = a p r := rfl

theorem e_mem_E (i : Fin p) : e p r i ∈ E p r := by
  rw [e_eq_epsilon_pow]
  exact RigidDenseSource.Concrete.coe_standard p r i ▸
    (RigidDenseSource.Concrete.standard p r i).property

theorem a_mem_E : a p r ∈ E p r := by
  apply (RigidDenseSource.Concrete.mem_source p r _).mpr
  exact ⟨0, 1, by simp⟩

def sourceGen : Fin p ⊕ Unit → A p r := Sum.elim (e p r) (fun _ => a p r)

theorem E_eq_span_sourceGen : E p r = Submodule.span (K p r) (Set.range (sourceGen p r)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, s, rfl⟩ := (RigidDenseSource.Concrete.mem_source p r x).mp hx
    apply Submodule.add_mem
    · apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      rw [← e_eq_epsilon_pow]
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨Sum.inr (), rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i => exact e_mem_E p r i
    | inr i => exact a_mem_E p r

theorem a_mem_D : a p r ∈ D p r := by
  let i : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  have h := gen_mem_D p r (Sum.inr (Sum.inl i))
  simpa [gen, e_eq_epsilon_pow, i] using h

theorem E_le_D : E p r ≤ D p r := by
  rw [E_eq_span_sourceGen]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i => exact e_mem_D p r i
  | inr i => exact a_mem_D p r

/-- The determinant on `A`, as an `L`-alternating map. -/
def deltaAlternating : (A p r) [⋀^Fin p]→ₗ[L p r] (L p r) :=
  Matrix.detRowAlternating.compLinearMap (TruncatedPolynomial.coeff (L p r) p).toLinearMap

@[simp] theorem deltaAlternating_apply (v : Fin p → A p r) :
    deltaAlternating p r v = delta p r v := by
  change Matrix.det (fun i j => TruncatedPolynomial.coeff (L p r) p (v i) j) = _
  exact Matrix.det_transpose _ |>.symm

theorem delta_update_e_a (i : Fin p) :
    delta p r (Function.update (e p r) i (a p r)) = z p r (Sum.inl i) := by
  have h : Matrix.of (fun k j => TruncatedPolynomial.coeff (L p r) p
      (Function.update (e p r) i (a p r) j) k) =
      Matrix.updateCol (1 : Matrix (Fin p) (Fin p) (L p r)) i
        (fun k => z p r (Sum.inl k)) := by
    ext k j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj, e,
        TruncatedPolynomial.coeff_basis, Matrix.one_apply, eq_comm]
  rw [delta, h]
  have hcol : (fun k => z p r (Sum.inl k)) =
      (fun k => ∑ j : Fin p, z p r (Sum.inl j) • (1 : Matrix (Fin p) (Fin p) (L p r)) k j) := by
    ext k
    simp [Matrix.one_apply]
  rw [hcol, Matrix.det_updateCol_sum, Matrix.det_one, smul_eq_mul, mul_one]

theorem primary_mem_G (i : Fin p) : z p r (Sum.inl i) ∈ G p r := by
  rw [← delta_update_e_a p r i]
  apply Submodule.subset_span
  refine ⟨fun j => ⟨Function.update (e p r) i (a p r) j, ?_⟩, rfl⟩
  by_cases hj : j = i
  · subst j; simpa using a_mem_D p r
  · simpa [Function.update_of_ne hj] using e_mem_D p r j

theorem delta_eq_basis_det (v : Fin p → A p r) :
    delta p r v = (TruncatedPolynomial.basis (L p r) p).det v := rfl

/-- The `K`-span of `1, a_0, ..., a_{p-1}` in `L`. -/
def primarySpan : Submodule (K p r) (L p r) :=
  Submodule.span (K p r) ({1} ∪ Set.range (fun i : Fin p => z p r (Sum.inl i)))

theorem delta_standard_tuple (t : Fin p → Fin p) :
    delta p r (fun j => e p r (t j)) = algebraMap (K p r) (L p r)
      (Matrix.det (fun i j => if t j = i then (1 : K p r) else 0)) := by
  rw [delta, RingHom.map_det]
  congr 1
  ext i j
  simp [e, TruncatedPolynomial.coeff_basis, apply_ite]

private theorem delta_standard_tuple_mem (t : Fin p → Fin p) :
    delta p r (fun j => e p r (t j)) ∈ primarySpan p r := by
  rw [delta_standard_tuple]
  have h : (1 : L p r) ∈ primarySpan p r := Submodule.subset_span (Or.inl rfl)
  simpa [Algebra.smul_def] using (primarySpan p r).smul_mem
    (Matrix.det (fun i j => if t j = i then (1 : K p r) else 0)) h

private theorem delta_sourceGen_tuple_mem (s : Fin p → Fin p ⊕ Unit) :
    delta p r (fun i => sourceGen p r (s i)) ∈ primarySpan p r := by
  classical
  by_cases hex : ∃ i, s i = Sum.inr ()
  · obtain ⟨i, hi⟩ := hex
    by_cases hdup : ∃ j, j ≠ i ∧ s j = Sum.inr ()
    · obtain ⟨j, hji, hj⟩ := hdup
      have hz := (deltaAlternating p r).map_eq_zero_of_eq
        (fun k => sourceGen p r (s k)) (i := j) (j := i) (by rw [hi, hj]) hji
      rw [deltaAlternating_apply] at hz
      rw [hz]
      exact Submodule.zero_mem _
    · have ho : ∀ j, j ≠ i → ∃ k, s j = Sum.inl k := by
        intro j hji
        cases hs : s j with
        | inl k => exact ⟨k, rfl⟩
        | inr u => exact False.elim (hdup ⟨j, hji, by cases u; exact hs⟩)
      let t : Fin p → Fin p := fun j => if hji : j = i then i else Classical.choose (ho j hji)
      have heq : (fun j => sourceGen p r (s j)) =
          Function.update (fun j => e p r (t j)) i (a p r) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [hi, sourceGen]
        · rw [Function.update_of_ne hji]
          dsimp [t]
          rw [dite_eq_right hji]
          exact congrArg (sourceGen p r) (Classical.choose_spec (ho j hji))
      rw [heq, ← deltaAlternating_apply, a_expansion,
        (deltaAlternating p r).map_update_sum]
      apply Submodule.sum_mem
      intro j _
      rw [(deltaAlternating p r).map_update_smul, deltaAlternating_apply]
      have hup : Function.update (fun j => e p r (t j)) i (e p r j) =
          (fun k => e p r (Function.update t i j k)) := by
        funext k
        by_cases hki : k = i <;> simp [hki]
      rw [hup, delta_standard_tuple, smul_eq_mul, mul_comm]
      simpa only [Algebra.smul_def] using (primarySpan p r).smul_mem
        (Matrix.det (fun k l => if Function.update t i j l = k then (1 : K p r) else 0))
        (Submodule.subset_span (Or.inr ⟨j, rfl⟩) : z p r (Sum.inl j) ∈ primarySpan p r)
  · have ho : ∀ j, ∃ k, s j = Sum.inl k := by
      intro j
      cases hs : s j with
      | inl k => exact ⟨k, rfl⟩
      | inr u => exact False.elim (hex ⟨j, by cases u; exact hs⟩)
    choose t ht using ho
    have heq : (fun j => sourceGen p r (s j)) = (fun j => e p r (t j)) := by
      funext j
      rw [ht j]
      rfl
    rw [heq]
    exact delta_standard_tuple_mem p r t

theorem delta_span_E :
    Submodule.span (K p r) (Set.range (fun v : Fin p → E p r =>
      delta p r (fun i => (v i : A p r)))) = primarySpan p r := by
  apply le_antisymm
  · rw [E_eq_span_sourceGen]
    apply (determinant_span_generator_tuples (K := K p r)
      (TruncatedPolynomial.coeff (L p r) p).toLinearMap (sourceGen p r)).le.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact delta_sourceGen_tuple_mem p r s
  · apply Submodule.span_le.mpr
    rintro x (hx | ⟨i, rfl⟩)
    · have hx' : x = 1 := hx
      rw [hx', ← delta_e p r]
      exact Submodule.subset_span ⟨fun i => ⟨e p r i, e_mem_E p r i⟩, rfl⟩
    · dsimp only
      rw [← delta_update_e_a p r i]
      apply Submodule.subset_span
      refine ⟨fun j => ⟨Function.update (e p r) i (a p r) j, ?_⟩, rfl⟩
      by_cases hj : j = i
      · subst j; simpa using a_mem_E p r
      · simpa [Function.update_of_ne hj] using e_mem_E p r j

theorem delta_mem_primarySpan (v : Fin p → E p r) :
    delta p r (fun i => (v i : A p r)) ∈ primarySpan p r := by
  rw [← delta_span_E]
  exact Submodule.subset_span ⟨v, rfl⟩

theorem delta_mem_G_E (v : Fin p → E p r) :
    delta p r (fun i => (v i : A p r)) ∈ G p r :=
  Submodule.subset_span ⟨fun i => ⟨v i, E_le_D p r (v i).property⟩, rfl⟩

end AlternatingAnalytic.DeterminantPair
