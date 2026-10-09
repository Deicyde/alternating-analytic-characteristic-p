import AlternatingAnalytic.Analysis.LaurentResiduePolarization

/-!
# Lemma C.4

Collects (Ψ2), (Ψ3) and (Ψ4) of Lemma C.4 for the coefficient lift `Ψ` in one statement.
(Ψ1) holds by the type of `laurentResidueLift`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped NNReal BoundedContinuousFunction Classical

namespace AlternatingAnalytic

universe v

/-- Lemma C.4: `Ψ` is alternating in its last `k` slots, has uniformly bounded support
dimension, and satisfies the grouped polarization identity (Ψ4). -/
theorem laurentResidueLift_full_properties
    (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (k : ℕ) (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (hP : ∀ f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r),
      P (fun _ => f) = Round24Transfer.Q (LaurentField κ r) (Fin k)
        (ℕ →ᵇ LaurentField κ r) (ℕ →ᵇ LaurentField κ r)
        (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) f) :
    (∀ (u x : Fin k → ℕ → κ) {i j : Fin k}, i ≠ j → x i = x j →
      laurentResidueLift κ r k α P u x = 0) ∧
    (∃ d : ℕ, ∀ u x : Fin k → ℕ → κ,
      exteriorSupportDim (laurentResidueLift κ r k α P u x) ≤ d) ∧
    (∀ (J : Type v) [Fintype J] (b : J → ℕ → κ) (ν : J → ℕ) (x : Fin k → ℕ → κ),
      (∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = ν),
        laurentResidueLift κ r k α P (fun i => b (f i)) x) =
      ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = ν),
        exteriorPower.ιMulti κ k (fun i => b (f i) * x i)) := by
  exact ⟨fun u x _ _ hij hx => laurentResidueLift_alternating κ r k α P u x hij hx,
    ⟨_, laurentResidueLift_support_le κ r k α P⟩,
    fun _ _ b ν x => laurentResidueLift_pol κ r k α P hP b ν x⟩

end AlternatingAnalytic
