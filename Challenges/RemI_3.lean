import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic

/-!
# Remark I.3 (a nonspherical target norm with analytic precomposition), p. 64

Paper statement (Appendix I.3): Spherical completeness of the given target norm is not
necessary for analyticity, even in degrees at least the characteristic. Let `K = F_p((t))` with
`|t| = 1/2` and let `F = c₀(ℕ,K)`, the space of sequences tending to zero. Define
`w_j = 1 + 1/(j+2)` and `‖x‖_w = sup_{j ≥ 0} w_j |x_j|`. This is a nonarchimedean norm
satisfying `‖x‖_∞ ≤ ‖x‖_w ≤ (3/2) ‖x‖_∞`. Thus `F` is Banach for either norm. The usual
supremum norm [...] is spherically complete, and precomposition into `F` is analytic in every
finite degree, for all normed `E, E'`, for that norm. Equivalent norms
preserve analyticity, so precomposition remains analytic for `‖·‖_w`. Nevertheless, the weighted
norm is not spherically complete: with `a_n = ∑_{j<n} e_j` and `B_n = B̄_w(a_n, w_n)`, the
balls are nested (`B_{n+1} ⊆ B_n`) and their intersection is empty.

## Formalization notes
* `K` is the library's `LaurentField (ZMod p) (1/2)` (abbreviation `Kp p`), with
  `‖x‖ = (1/2)^(order x)`. `AlternatingAnalytic.Analysis.LaurentField` is imported for this
  definition and for the class `SphericallyCompleteSpace`; it proves no part of the remark.
* `F` with the supremum norm is `C₀(ℕ, Kp p)`. In `part7` it is the synonym `SupF p`, with the
  same norm, because instance synthesis on operator spaces into `C₀(ℕ, Kp p)` fails.
* The weighted norm is given through a model: `IsWeightedModel p G e` says
  `e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)` and `‖g‖ = weightedNorm (e g)`. `part1` says a model exists;
  `part2`, `part3`, `part6`, `part8` hold for every model.
* `part5` states the ball family directly on `C₀(ℕ, Kp p)`.
* "Every finite degree, for all normed `E, E'`": index type `Fin k` for all `k`, `AnalyticAt` at
  every point, `E, E'` arbitrary normed `Kp p`-spaces.
* The step "sup-norm values lie in `2^ℤ`" is not stated separately.
* `backward.isDefEq.respectTransparency false` is needed for instance unification on `Kp p`.
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

/-- `c₀(ℕ,K)` with its supremum norm, as a type synonym of `C₀(ℕ, Kp p)` with the same norm. -/
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

/-- The weighted norm is a norm: some normed `K`-space `G` is a model of it. -/
theorem part1 (p : ℕ) [Fact p.Prime] :
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : NormedSpace (Kp p) G)
      (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)), IsWeightedModel p G e := by
  sorry

/-- `‖x‖_∞ ≤ ‖x‖_w ≤ (3/2) ‖x‖_∞`. -/
theorem part2 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e)
    (g : G) :
    ‖e g‖ ≤ ‖g‖ ∧ ‖g‖ ≤ 3 / 2 * ‖e g‖ := by
  sorry

/-- The weighted norm is nonarchimedean and complete. -/
theorem part3 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e) :
    IsUltrametricDist G ∧ CompleteSpace G := by
  sorry

/-- The supremum norm on `c₀(ℕ,K)` is spherically complete. -/
theorem part4 (p : ℕ) [Fact p.Prime] : SphericallyCompleteSpace C₀(ℕ, Kp p) := by
  sorry

/-- The weighted balls `B_n` are nonempty and nested, with empty intersection. -/
theorem part5 (p : ℕ) [Fact p.Prime] :
    (∀ n, (weightedBall p n).Nonempty) ∧
      (∀ n, weightedBall p (n + 1) ⊆ weightedBall p n) ∧
      (⋂ n, weightedBall p n) = ∅ := by
  sorry

/-- The weighted norm is not spherically complete. -/
theorem part6 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e) :
    ¬ SphericallyCompleteSpace G := by
  sorry

/-- Precomposition into `c₀(ℕ,K)` with the supremum norm is analytic at every point. -/
theorem part7 (p : ℕ) [Fact p.Prime] (E : Type uE) (E' : Type uE')
    [NormedAddCommGroup E] [NormedSpace (Kp p) E] [NormedAddCommGroup E'] [NormedSpace (Kp p) E']
    (k : ℕ) (f₀ : E →L[Kp p] E') :
    AnalyticAt (Kp p)
      (fun f : E →L[Kp p] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[Kp p] SupF p) →L[Kp p] (E [⋀^Fin k]→L[Kp p] SupF p))) f₀ := by
  sorry

/-- Precomposition into `c₀(ℕ,K)` with the weighted norm is analytic at every point. -/
theorem part8 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e)
    (E : Type uE) (E' : Type uE')
    [NormedAddCommGroup E] [NormedSpace (Kp p) E] [NormedAddCommGroup E'] [NormedSpace (Kp p) E']
    (k : ℕ) (f₀ : E →L[Kp p] E') :
    AnalyticAt (Kp p)
      (fun f : E →L[Kp p] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[Kp p] G) →L[Kp p] (E [⋀^Fin k]→L[Kp p] G))) f₀ := by
  sorry

end AlternatingAnalyticChallenge.RemI_3
