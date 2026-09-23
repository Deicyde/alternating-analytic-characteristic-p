import AlternatingAnalytic.Analysis.CompletedBaseChange
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Strong alternation after completed scalar extension

A continuous multilinear map on completed base change is alternating if its
values on the original space agree with an alternating map. The proof retains
equal-input vanishing in characteristic two; antisymmetry alone is insufficient.
-/

open scoped TensorProduct
open Function

namespace AlternatingAnalytic

section DenseSpan

variable {L V G I : Type*} [NontriviallyNormedField L]
  [NormedAddCommGroup V] [NormedSpace L V]
  [NormedAddCommGroup G] [NormedSpace L G] [Fintype I] [DecidableEq I]

omit [Fintype I] in
/-- A continuous multilinear map vanishes if it vanishes when the coordinates
in a finite set lie in a set with dense linear span, and the others are fixed. -/
theorem multilinear_zero_of_dense_span_on
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (S : Set V) (hS : Dense (Submodule.span L S : Set V))
    (s : Finset I) (x : I → V)
    (h : ∀ y : I → V, (∀ i ∈ s, y i ∈ S) →
      (∀ i ∉ s, y i = x i) → g y = 0) : g x = 0 := by
  classical
  induction s using Finset.induction generalizing x with
  | empty => exact h x (by simp) (by simp)
  | @insert a s ha ih =>
    have hlin : g.toContinuousLinearMap x a = 0 := by
      apply ContinuousLinearMap.ext_on hS
      intro z hz
      change g (update x a z) = 0
      apply ih
      intro y hy hyfix
      apply h y
      · intro i hi
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          rw [hyfix a ha, update_self]
          exact hz
        · exact hy i hi
      · intro i hi
        have hi' : i ≠ a ∧ i ∉ s := by simpa only [Finset.mem_insert, not_or] using hi
        exact (hyfix i hi'.2).trans (update_of_ne hi'.1 z x)
    have hv := congrArg (fun f : V →L[L] G => f (x a)) hlin
    simpa using hv

/-- Continuous multilinear maps are determined by a set with dense linear span. -/
theorem multilinear_zero_of_dense_span
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (S : Set V) (hS : Dense (Submodule.span L S : Set V))
    (h : ∀ y : I → V, (∀ i, y i ∈ S) → g y = 0) : g = 0 := by
  classical
  ext x
  apply multilinear_zero_of_dense_span_on g S hS Finset.univ x
  intro y hy _
  exact h y (fun i => hy i (Finset.mem_univ i))

omit [Fintype I] in
/-- With the swap identity, the expression obtained by repeating a variable in
two distinct slots is additive. This identity does not divide by two. -/
theorem multilinear_repeated_update_add
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (i j : I) (hij : i ≠ j)
    (hswap : ∀ x, g (x ∘ Equiv.swap i j) + g x = 0)
    (x : I → V) (a b : V) :
    g (update (update x i (a + b)) j (a + b)) =
      g (update (update x i a) j a) + g (update (update x i b) j b) := by
  classical
  have hswaparg : update (update x i a) j b ∘ Equiv.swap i j =
      update (update x i b) j a := by
    funext t
    by_cases hti : t = i
    · subst t; simp [hij]
    by_cases htj : t = j
    · subst t; simp [hij]
    simp [Equiv.swap_apply_of_ne_of_ne hti htj, hti, htj]
  have hcross := hswap (update (update x i a) j b)
  rw [hswaparg] at hcross
  rw [g.map_update_add, update_comm hij (a + b) a x,
    update_comm hij (a + b) b x, g.map_update_add, g.map_update_add,
    update_comm hij.symm a a x, update_comm hij.symm a b x,
    update_comm hij.symm b a x, update_comm hij.symm b b x]
  calc
    _ = g (update (update x i a) j a) +
        (g (update (update x i b) j a) + g (update (update x i a) j b)) +
          g (update (update x i b) j b) := by abel
    _ = _ := by rw [hcross]; simp

omit [Fintype I] in
/-- Repeating a scalar multiple in two slots scales the value twice. -/
theorem multilinear_repeated_update_smul
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (i j : I) (hij : i ≠ j) (x : I → V) (c : L) (z : V) :
    g (update (update x i (c • z)) j (c • z)) =
      c • c • g (update (update x i z) j z) := by
  classical
  rw [g.map_update_smul, update_comm hij (c • z) z x, g.map_update_smul,
    update_comm hij.symm z z x]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Module K G]

/-- Strong alternation extends from an injectively parametrized set with dense
linear span. The given alternating map need not be continuous. -/
theorem alternating_of_dense_span_range
    (f : E → V) (hf : Function.Injective f)
    (hS : Dense (Submodule.span L (Set.range f) : Set V))
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (m : E [⋀^I]→ₗ[K] G) (h : ∀ x : I → E, g (fun i => f (x i)) = m x)
    (x : I → V) (i j : I) (hijvalue : x i = x j) (hij : i ≠ j) : g x = 0 := by
  classical
  have hswap : ∀ y : I → V, g (y ∘ Equiv.swap i j) + g y = 0 := by
    have hz : g.domDomCongr (Equiv.swap i j) + g = 0 := by
      apply multilinear_zero_of_dense_span _ (Set.range f) hS
      intro y hy
      choose z hz using hy
      have hyz : y = fun a => f (z a) := funext (fun a => (hz a).symm)
      rw [hyz]
      change g (fun a => f (z (Equiv.swap i j a))) + g (fun a => f (z a)) = 0
      rw [h, h]
      exact m.map_swap_add z hij
    intro y
    exact congrArg (fun q : ContinuousMultilinearMap L (fun _ : I => V) G => q y) hz
  have hseed : ∀ z : E, g (update (update x i (f z)) j (f z)) = 0 := by
    intro z
    let t := update (update x i (f z)) j (f z)
    apply multilinear_zero_of_dense_span_on g (Set.range f) hS ({i, j}ᶜ) t
    intro y hy hyfix
    have hyi : y i = f z := by
      rw [hyfix i (by simp)]
      simp [t, hij]
    have hyj : y j = f z := by
      rw [hyfix j (by simp)]
      simp [t]
    have hyrange : ∀ a, y a ∈ Set.range f := by
      intro a
      by_cases hai : a = i
      · subst a; exact ⟨z, hyi.symm⟩
      by_cases haj : a = j
      · subst a; exact ⟨z, hyj.symm⟩
      exact hy a (by simp [hai, haj])
    choose v hv using hyrange
    have hyv : y = fun a => f (v a) := funext (fun a => (hv a).symm)
    rw [hyv, h]
    exact m.map_eq_zero_of_eq v (hf ((hv i).trans (hyi.trans (hyj.symm.trans (hv j).symm)))) hij
  let P : Submodule L V :=
    { carrier := {z | g (update (update x i z) j z) = 0}
      zero_mem' := g.map_coord_zero j (by simp)
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [multilinear_repeated_update_add g i j hij hswap x a b, ha, hb, zero_add]
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_ofPred_eq] at hz ⊢
        rw [multilinear_repeated_update_smul g i j hij x c z, hz, smul_zero, smul_zero] }
  have hPclosed : IsClosed (P : Set V) :=
    isClosed_eq (g.cont.comp
      (((continuous_const : Continuous (fun _ : V => x)).update i continuous_id).update j
        continuous_id)) continuous_const
  have hspan : (Submodule.span L (Set.range f) : Set V) ⊆ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact hseed z
  have hx : x i ∈ P := closure_minimal hspan hPclosed (hS (x i))
  change g (update (update x i (x i)) j (x i)) = 0 at hx
  rw [update_eq_self, hijvalue, update_eq_self] at hx
  exact hx

end DenseSpan

universe u

section BaseChange

variable (K : Type*) (E L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [NontriviallyNormedField L]
  [NormedAlgebra K L] [CompleteSpace K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K] [IsUltrametricDist L]

attribute [local instance] baseChangeModule baseChangeNormedAddCommGroup
  baseChangeNormedSpaceRestrictScalars baseChangeNormedSpace baseChangeIsScalarTower

/-- The original space has dense extension-field linear span in its actual
completed projective scalar extension. -/
theorem dense_span_completedBaseChangeEmbedding :
    Dense (Submodule.span L (Set.range (completedBaseChangeEmbedding K E L)) :
      Set (CompletedBaseChange K E L)) := by
  refine Dense.mono ?_ (denseRange_baseChangeToCompletion K E L)
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x l =>
    have heq : baseChangeToCompletion K E L (x ⊗ₜ[K] l) =
        l • completedBaseChangeEmbedding K E L x := by
      change baseChangeToCompletion K E L (x ⊗ₜ[K] l) =
        l • baseChangeToCompletion K E L (x ⊗ₜ[K] (1 : L))
      rw [← map_smul, baseChange_smul_tmul, mul_one]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace K G] [NormedSpace L G]

/-- A continuous multilinear map on completed scalar extension is strongly
alternating when its values on embedded tuples agree with an alternating map.
No completeness assumption on the output space is needed. -/
theorem alternating_of_baseChangeEmbedding {n : ℕ}
    (g : (CompletedBaseChange K E L) [×n]→L[L] G)
    (m : E [⋀^Fin n]→L[K] G)
    (h : ∀ x : Fin n → E, g (fun i => completedBaseChangeEmbedding K E L (x i)) = m x) :
    ∀ (x : Fin n → CompletedBaseChange K E L) (i j : Fin n),
      x i = x j → i ≠ j → g x = 0 :=
  alternating_of_dense_span_range (completedBaseChangeEmbedding K E L)
    (completedBaseChangeEmbedding K E L).injective
    (dense_span_completedBaseChangeEmbedding K E L) g m.toAlternatingMap h

end BaseChange

end AlternatingAnalytic
