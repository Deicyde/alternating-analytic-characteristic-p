import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import AlternatingAnalytic.Coordinates.WeightedNorm.SupNorm
import AlternatingAnalytic.Coordinates.WeightedNorm.Balls

/-!
# Remark I.3 (a nonspherical target norm with analytic precomposition), p. 63

Solution: the statements of `Challenges/RemI_3.lean`, proved from the library
(`AlternatingAnalytic/Coordinates/WeightedNorm/`):
* `part1`: the weighted copy `WeightedNorm.WeightedC0` (`Basic.lean`);
* `part2`, `part3`: `WeightedNorm.model_norm_bounds`, `WeightedNorm.model_isUltrametricDist`,
  `WeightedNorm.model_completeSpace` (`Model.lean`);
* `part4`: `WeightedNorm.sphericallyCompleteSpace` (`SupNorm.lean`; sup norms lie in `2^ℤ`);
* `part5`, `part6`: `WeightedNorm.ball_family`, `WeightedNorm.model_not_sphericallyCompleteSpace`
  (`Balls.lean`);
* `part7`, `part8`: `WeightedNorm.analyticAt_compContinuousLinearMapCLM` (`SupNorm.lean`, from
  `analyticAt_of_equivalentUltrametricNorm_discreteValueGroup`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped ZeroAtInfty NNReal

namespace AlternatingAnalyticChallenge.RemI_3

universe uE uE'

instance fact_half_pos : Fact (0 < (1 / 2 : ℝ≥0)) := ⟨by norm_num⟩

instance fact_half_lt_one : Fact ((1 / 2 : ℝ≥0) < 1) := ⟨by norm_num⟩

/-- `K = F_p((t))` with `|t| = 1/2`. -/
abbrev Kp (p : ℕ) [Fact p.Prime] : Type :=
  AlternatingAnalytic.LaurentField (ZMod p) (1 / 2)

/-- `c₀(ℕ,K)` with its supremum norm, as a type synonym of `C₀(ℕ, Kp p)` carrying exactly the
normed-group and normed-space instances of `C₀(ℕ, Kp p)` (used as a target of alternating maps). -/
def SupF (p : ℕ) [Fact p.Prime] : Type := C₀(ℕ, Kp p)

noncomputable instance (p : ℕ) [Fact p.Prime] : NormedAddCommGroup (SupF p) :=
  inferInstanceAs (NormedAddCommGroup C₀(ℕ, Kp p))

noncomputable instance (p : ℕ) [Fact p.Prime] : NormedSpace (Kp p) (SupF p) :=
  inferInstanceAs (NormedSpace (Kp p) C₀(ℕ, Kp p))

/-- The weights `w_j = 1 + 1/(j+2)`. -/
noncomputable def weight (j : ℕ) : ℝ := 1 + 1 / ((j : ℝ) + 2)

/-- The weighted norm `‖x‖_w = sup_j w_j |x_j|` of a null sequence. -/
noncomputable def weightedNorm (p : ℕ) [Fact p.Prime] (x : C₀(ℕ, Kp p)) : ℝ :=
  ⨆ j : ℕ, weight j * ‖x j‖

/-- `G` with `e : G ≃ₗ c₀(ℕ,K)` is a model of `(c₀(ℕ,K), ‖·‖_w)`: the norm of `G` is the
weighted norm transported along `e`. -/
def IsWeightedModel (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) : Prop :=
  ∀ g : G, ‖g‖ = weightedNorm p (e g)

/-- The closed weighted ball `B_n = B̄_w(a_n, w_n)` with `a_n = ∑_{j<n} e_j`. -/
def weightedBall (p : ℕ) [Fact p.Prime] (n : ℕ) : Set C₀(ℕ, Kp p) :=
  {x | (⨆ j : ℕ, weight j * ‖x j - (if j < n then (1 : Kp p) else 0)‖) ≤ weight n}

/-- **Remark I.3, the weighted norm is a norm.** There is a normed `K`-space `G` and a linear
isomorphism `e : G ≃ c₀(ℕ,K)` such that the norm of `G` is `‖e ·‖_w`. -/
theorem part1 (p : ℕ) [Fact p.Prime] :
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : NormedSpace (Kp p) G)
      (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)), IsWeightedModel p G e := by
  exact ⟨AlternatingAnalytic.WeightedNorm.WeightedC0 (Kp p), inferInstance, inferInstance,
    AlternatingAnalytic.WeightedNorm.WeightedC0.equiv (Kp p) (Kp p), fun _ => rfl⟩

/-- **Remark I.3, norm comparison.** `‖x‖_∞ ≤ ‖x‖_w ≤ (3/2) ‖x‖_∞`. -/
theorem part2 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e)
    (g : G) :
    ‖e g‖ ≤ ‖g‖ ∧ ‖g‖ ≤ 3 / 2 * ‖e g‖ := by
  exact AlternatingAnalytic.WeightedNorm.model_norm_bounds e he g

/-- **Remark I.3, the weighted norm is nonarchimedean and Banach.** -/
theorem part3 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e) :
    IsUltrametricDist G ∧ CompleteSpace G := by
  exact ⟨AlternatingAnalytic.WeightedNorm.model_isUltrametricDist e he,
    AlternatingAnalytic.WeightedNorm.model_completeSpace e he⟩

/-- **Remark I.3, the supremum norm is spherically complete.** -/
theorem part4 (p : ℕ) [Fact p.Prime] : SphericallyCompleteSpace C₀(ℕ, Kp p) := by
  exact AlternatingAnalytic.WeightedNorm.sphericallyCompleteSpace (ZMod p) (1 / 2)

/-- **Remark I.3, the explicit ball family.** The weighted balls `B_n` are nonempty, nested,
and have empty intersection. -/
theorem part5 (p : ℕ) [Fact p.Prime] :
    (∀ n, (weightedBall p n).Nonempty) ∧
      (∀ n, weightedBall p (n + 1) ⊆ weightedBall p n) ∧
      (⋂ n, weightedBall p n) = ∅ := by
  exact AlternatingAnalytic.WeightedNorm.ball_family (𝕜 := Kp p)

/-- **Remark I.3, the weighted norm is not spherically complete.** -/
theorem part6 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e) :
    ¬ SphericallyCompleteSpace G := by
  exact AlternatingAnalytic.WeightedNorm.model_not_sphericallyCompleteSpace e he

/-- **Remark I.3, analyticity for the supremum norm.** Precomposition into `c₀(ℕ,K)` with
its supremum norm is analytic at every point, in every degree, for all normed `E, E'`. -/
theorem part7 (p : ℕ) [Fact p.Prime] (E : Type uE) (E' : Type uE')
    [NormedAddCommGroup E] [NormedSpace (Kp p) E] [NormedAddCommGroup E'] [NormedSpace (Kp p) E']
    (k : ℕ) (f₀ : E →L[Kp p] E') :
    AnalyticAt (Kp p)
      (fun f : E →L[Kp p] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[Kp p] SupF p) →L[Kp p] (E [⋀^Fin k]→L[Kp p] SupF p))) f₀ := by
  have : CompleteSpace (SupF p) := inferInstanceAs (CompleteSpace C₀(ℕ, Kp p))
  exact AlternatingAnalytic.WeightedNorm.analyticAt_compContinuousLinearMapCLM (ZMod p) (1 / 2)
    (F := SupF p) (fun x y => AlternatingAnalytic.WeightedNorm.norm_add_le_max (β := Kp p) x y)
    k f₀

/-- **Remark I.3, analyticity for the weighted norm.** Precomposition into `(c₀(ℕ,K), ‖·‖_w)`
is analytic at every point, in every degree, for all normed `E, E'`, although this target is
not spherically complete (`part6`). -/
theorem part8 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e)
    (E : Type uE) (E' : Type uE')
    [NormedAddCommGroup E] [NormedSpace (Kp p) E] [NormedAddCommGroup E'] [NormedSpace (Kp p) E']
    (k : ℕ) (f₀ : E →L[Kp p] E') :
    AnalyticAt (Kp p)
      (fun f : E →L[Kp p] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[Kp p] G) →L[Kp p] (E [⋀^Fin k]→L[Kp p] G))) f₀ := by
  have := AlternatingAnalytic.WeightedNorm.model_completeSpace e he
  exact AlternatingAnalytic.WeightedNorm.analyticAt_compContinuousLinearMapCLM (ZMod p) (1 / 2)
    (AlternatingAnalytic.WeightedNorm.model_norm_add_le_max e he) k f₀

end AlternatingAnalyticChallenge.RemI_3
