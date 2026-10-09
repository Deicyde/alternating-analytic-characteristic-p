import AlternatingAnalytic.Analysis.LaurentResidueLift
import AlternatingAnalytic.Algebra.FullPolarization

/-!
# The polarization identity (Ψ4)

Proves (Ψ4) of Lemma C.4: the grouped polarization identity for `Ψ`, for every finite family
`b` and every multiplicity `ν`. As in the paper, the identity is first proved in `B` over the
infinite field `κ((X))`, and only then is the coefficient map applied, so `κ` may be finite.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped NNReal BoundedContinuousFunction Classical

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)

local notation "K" => LaurentField κ r
local notation "E" => (ℕ →ᵇ LaurentField κ r)
local notation "B" => ProjectiveExteriorCompletion (LaurentField κ r) ℕ k

/-- `Φ` with its last `k` arguments fixed, as a `κ((X))`-multilinear map. -/
def laurentLiftFixedVectors (P : LaurentLiftCandidate κ r k) (x : Fin k → E) :
    MultilinearMap K (fun _ : Fin k => E) B where
  toFun a := laurentLiftAlternating κ r k P a x
  map_update_add' a i u v := congrArg (fun f => f x)
    ((laurentLiftAlternating κ r k P).map_update_add a i u v)
  map_update_smul' a i c u := congrArg (fun f => f x)
    ((laurentLiftAlternating κ r k P).map_update_smul a i c u)

/-- The grouped polarization identity for `Φ` in `B`, before applying `η`. -/
theorem laurentLift_grouped (P : LaurentLiftCandidate κ r k)
    (hP : ∀ f : E →L[K] E, P (fun _ => f) = Round24Transfer.Q K (Fin k) E E B f)
    {J : Type*} [Fintype J] (b : J → E) (ν : J → ℕ) (x : Fin k → E) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = ν),
      P (fun i => boundedSequenceMultiplier K ℕ (b (f i)))
        (completedExteriorWedge K ℕ k) x) =
    ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = ν),
      completedExteriorWedge K ℕ k
        (fun i => boundedSequenceMultiplier K ℕ (b (f i)) (x i)) := by
  classical
  have hd (a : E) : laurentLiftFixedVectors κ r k P x (fun _ => a) =
      completedExteriorWedge K ℕ k (fun i => boundedSequenceMultiplier K ℕ a (x i)) := by
    change P (fun _ => boundedSequenceMultiplier K ℕ a) (completedExteriorWedge K ℕ k) x = _
    rw [hP]
    rfl
  exact MultilinearMap.sumOfType_eq_of_multiplier_diagonal
    (laurentLiftFixedVectors κ r k P x) (completedExteriorWedge K ℕ k).toMultilinearMap
    (boundedSequenceMultiplier K ℕ).toLinearMap₁₂ x hd b ν

/-- (Ψ4) The grouped polarization identity for `Ψ`. -/
theorem laurentResidueLift_pol (α : Fin k) (P : LaurentLiftCandidate κ r k)
    (hP : ∀ f : E →L[K] E, P (fun _ => f) = Round24Transfer.Q K (Fin k) E E B f)
    {J : Type*} [Fintype J] (b : J → ℕ → κ) (ν : J → ℕ) (x : Fin k → ℕ → κ) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = ν),
      laurentResidueLift κ r k α P (fun i => b (f i)) x) =
    ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = ν),
      exteriorPower.ιMulti κ k (fun i => b (f i) * x i) := by
  classical
  have h := congrArg (completedLaurentCoefficient κ r ℕ k α)
    (laurentLift_grouped κ r k P hP (fun j => constantLaurentArray κ r (b j)) ν
      (fun i => constantLaurentArray κ r (x i)))
  simpa only [map_sum, boundedSequenceMultiplier_constant,
    completedLaurentCoefficient_constant_wedge, laurentResidueLift_apply] using h

end AlternatingAnalytic
