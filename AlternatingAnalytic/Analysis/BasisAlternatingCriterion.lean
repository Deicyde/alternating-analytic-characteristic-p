import AlternatingAnalytic.Analysis.BaseChangeAlternatingCriterion
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# A basis criterion for alternation

A continuous multilinear map is alternating if it vanishes whenever a basis vector, or
a sum of two distinct basis vectors, is repeated in two slots. The proof does not divide
by two, so it works in characteristic two.
-/

open Function

namespace AlternatingAnalytic

section BasisCriterion

variable {L V G I B : Type*} [NontriviallyNormedField L]
  [NormedAddCommGroup V] [NormedSpace L V]
  [NormedAddCommGroup G] [NormedSpace L G]
  [Fintype I] [DecidableEq I] [LinearOrder B]

omit [Fintype I] in
/-- Under the basis hypotheses, the two cross terms sum to zero. -/
theorem multilinear_basis_cross_sum_zero
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (e : Module.Basis B L V)
    (hdiag : ∀ (f : I → B) (i j : I), i ≠ j → ∀ b,
      g (update (update (fun t => e (f t)) i (e b)) j (e b)) = 0)
    (hsum : ∀ (f : I → B) (i j : I), i ≠ j → ∀ b c, b < c →
      g (update (update (fun t => e (f t)) i (e b + e c)) j (e b + e c)) = 0)
    (f : I → B) (i j : I) (hij : i ≠ j) (b c : B) :
    g (update (update (fun t => e (f t)) i (e c)) j (e b)) +
      g (update (update (fun t => e (f t)) i (e b)) j (e c)) = 0 := by
  have hordered (b c : B) (hbc : b < c) :
      g (update (update (fun t => e (f t)) i (e c)) j (e b)) +
        g (update (update (fun t => e (f t)) i (e b)) j (e c)) = 0 := by
    have h := hsum f i j hij b c hbc
    rw [g.map_update_add, update_comm hij (e b + e c) (e b) (fun t => e (f t)),
      update_comm hij (e b + e c) (e c) (fun t => e (f t)), g.map_update_add, g.map_update_add,
      update_comm hij.symm (e b) (e b) (fun t => e (f t)), update_comm hij.symm (e b) (e c) (fun t => e (f t)),
      update_comm hij.symm (e c) (e b) (fun t => e (f t)), update_comm hij.symm (e c) (e c) (fun t => e (f t))] at h
    simpa only [hdiag f i j hij b, hdiag f i j hij c, zero_add, add_zero] using h
  rcases lt_trichotomy b c with hbc | hbc | hcb
  · exact hordered b c hbc
  · subst c
    simp only [hdiag f i j hij b, zero_add]
  · simpa only [add_comm] using hordered c b hcb

/-- Under the basis hypotheses, swapping two slots negates `g`. -/
theorem multilinear_basis_swap_add
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (e : Module.Basis B L V)
    (hdiag : ∀ (f : I → B) (i j : I), i ≠ j → ∀ b,
      g (update (update (fun t => e (f t)) i (e b)) j (e b)) = 0)
    (hsum : ∀ (f : I → B) (i j : I), i ≠ j → ∀ b c, b < c →
      g (update (update (fun t => e (f t)) i (e b + e c)) j (e b + e c)) = 0)
    (i j : I) (hij : i ≠ j) (x : I → V) :
    g (x ∘ Equiv.swap i j) + g x = 0 := by
  classical
  have hS : Dense (Submodule.span L (Set.range e) : Set V) := by
    rw [e.span_eq]
    simp
  have hz : g.domDomCongr (Equiv.swap i j) + g = 0 := by
    apply multilinear_zero_of_dense_span _ (Set.range e) hS
    intro y hy
    choose f hf using hy
    have hyf : y = fun t => e (f t) := funext (fun t => (hf t).symm)
    have hcross := multilinear_basis_cross_sum_zero g e hdiag hsum f i j hij (f i) (f j)
    have hswaparg : update (update (fun t => e (f t)) i (e (f j))) j (e (f i)) =
        (fun t => e (f t)) ∘ Equiv.swap i j := by
      funext t
      by_cases hti : t = i
      · subst t; simp [hij]
      by_cases htj : t = j
      · subst t; simp
      simp [Equiv.swap_apply_of_ne_of_ne hti htj, hti, htj]
    change g (y ∘ Equiv.swap i j) + g y = 0
    rw [hyf]
    simpa only [hswaparg, update_eq_self] using hcross
  exact congrArg (fun q : ContinuousMultilinearMap L (fun _ : I => V) G => q x) hz

/-- `g` is alternating if it vanishes when a basis vector or a sum of two distinct basis
vectors is repeated. The basis may be infinite. -/
theorem multilinear_alternating_of_basis_repeated
    (g : ContinuousMultilinearMap L (fun _ : I => V) G)
    (e : Module.Basis B L V)
    (hdiag : ∀ (f : I → B) (i j : I), i ≠ j → ∀ b,
      g (update (update (fun t => e (f t)) i (e b)) j (e b)) = 0)
    (hsum : ∀ (f : I → B) (i j : I), i ≠ j → ∀ b c, b < c →
      g (update (update (fun t => e (f t)) i (e b + e c)) j (e b + e c)) = 0)
    (x : I → V) (i j : I) (hvalue : x i = x j) (hij : i ≠ j) : g x = 0 := by
  classical
  have hS : Dense (Submodule.span L (Set.range e) : Set V) := by
    rw [e.span_eq]
    simp
  have hswap := multilinear_basis_swap_add g e hdiag hsum i j hij
  have hseed : ∀ b : B, g (update (update x i (e b)) j (e b)) = 0 := by
    intro b
    let t := update (update x i (e b)) j (e b)
    apply multilinear_zero_of_dense_span_on g (Set.range e) hS ({i, j}ᶜ) t
    intro y hy hyfix
    have hyi : y i = e b := by
      rw [hyfix i (by simp)]
      simp [t, hij]
    have hyj : y j = e b := by
      rw [hyfix j (by simp)]
      simp [t]
    have hyrange : ∀ a, y a ∈ Set.range e := by
      intro a
      by_cases hai : a = i
      · subst a; exact ⟨b, hyi.symm⟩
      by_cases haj : a = j
      · subst a; exact ⟨b, hyj.symm⟩
      exact hy a (by simp [hai, haj])
    choose f hf using hyrange
    have hyf : (fun a => e (f a)) = y := funext hf
    have h := hdiag f i j hij b
    rw [hyf, ← hyi, update_eq_self, hyi, ← hyj, update_eq_self] at h
    exact h
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
  have hspan : Submodule.span L (Set.range e) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact hseed b
  rw [e.span_eq] at hspan
  have hx : x i ∈ P := hspan (Submodule.mem_top)
  change g (update (update x i (x i)) j (x i)) = 0 at hx
  rw [update_eq_self, hvalue, update_eq_self] at hx
  exact hx

end BasisCriterion

end AlternatingAnalytic
