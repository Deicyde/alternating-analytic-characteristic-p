import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic

/-!
# Remark I.3 (a nonspherical target norm with analytic precomposition), p. 63

Paper statement (Appendix I.3, `rem:nonspherical-analytic-target`): Spherical completeness of
the given target norm is not necessary for analyticity, even in degrees at least the
characteristic. Let `K = F_p((t))` with `|t| = 1/2` and let `F = c₀(ℕ,K)`, the space of
sequences tending to zero. Define `w_j = 1 + 1/(j+2)` and `‖x‖_w = sup_{j ≥ 0} w_j |x_j|`.
This is a nonarchimedean norm satisfying `‖x‖_∞ ≤ ‖x‖_w ≤ (3/2) ‖x‖_∞`. Thus `F` is Banach for
either norm. The usual supremum norm [...] is spherically complete, and precomposition into `F`
is analytic in every finite degree, for all normed `E, E'`, for that norm. Equivalent norms
preserve analyticity, so precomposition remains analytic for `‖·‖_w`. Nevertheless, the weighted
norm is not spherically complete: with `a_n = ∑_{j<n} e_j` and `B_n = B̄_w(a_n, w_n)`, the
balls are nested (`B_{n+1} ⊆ B_n`) and their intersection is empty.

## Formalization notes
* `K = F_p((t))` with `|t| = 1/2` is the library's `AlternatingAnalytic.LaurentField (ZMod p) (1/2)`
  (abbreviation `Kp p` below, `p` prime via `[Fact p.Prime]`), whose norm is
  `‖x‖ = (1/2)^(order x)`; in particular `‖t‖ = 1/2`. It is complete, ultrametric and
  spherically complete (library instances). The module `AlternatingAnalytic.Analysis.LaurentField`
  is imported for this definition and for the class `SphericallyCompleteSpace` (defined in
  `AlternatingAnalytic.Analysis.SphericalCompleteness`: every nonempty family of pairwise
  intersecting closed balls has a common point). Neither module proves any part of the remark.
  The two `Fact` instances `0 < 1/2` and `1/2 < 1` needed by `LaurentField` are declared below.
* `F = c₀(ℕ,K)` with the supremum norm is Mathlib's `C₀(ℕ, Kp p)` (ℕ discrete). In `part7`
  (analyticity into the sup-norm target) it appears through the type synonym `SupF p`, which
  carries exactly the `NormedAddCommGroup` and `NormedSpace` instances of `C₀(ℕ, Kp p)`
  (`inferInstanceAs`): with `C₀(ℕ, Kp p)` itself, instance synthesis for operator spaces such as
  `(E' [⋀^Fin k]→L C₀(ℕ, Kp p)) →L (E [⋀^Fin k]→L C₀(ℕ, Kp p))` fails (an instance-path clash
  with Mathlib's `Valued` structure on Laurent series). The synonym does not change the norm.
* The weighted norm cannot be installed on `C₀(ℕ, Kp p)` itself (it already carries the sup
  norm), and constructing it as a normed-space instance is part of what the remark asserts.
  It is therefore stated through a *model*: `IsWeightedModel p G e` says that `G` is a normed
  `Kp p`-space and `e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)` is a linear isomorphism with
  `‖g‖ = weightedNorm (e g) = ⨆ j, w_j ‖(e g) j‖` for all `g`. `part1` asserts that a model
  exists (so the remaining parts are not vacuous); `part2`, `part3`, `part6`, `part8` assert the
  remark's claims for every model.
* Parts: `part1` the weighted norm is a norm (a model exists); `part2` the norm comparison
  `‖x‖_∞ ≤ ‖x‖_w ≤ (3/2)‖x‖_∞`; `part3` the weighted norm is nonarchimedean and Banach;
  `part4` the supremum norm is spherically complete; `part5` the explicit balls `B_n` are
  nonempty, nested and have empty intersection, stated directly on `C₀(ℕ, Kp p)` with
  `B_n = {x | ⨆ j, w_j ‖x_j - (a_n)_j‖ ≤ w_n}`, `(a_n)_j = 1` for `j < n` and `0` otherwise;
  `part6` the weighted norm is not spherically complete; `part7` precomposition into the
  sup-norm `F` is analytic; `part8` precomposition into the weighted `F` is analytic.
* "Analytic in every finite degree, for all normed `E, E'`": index type `Fin k` for every
  `k : ℕ`, `AnalyticAt` at every point of `L(E,E')`, `E, E'` arbitrary normed `Kp p`-spaces
  (no completeness, no ultrametric norm) in arbitrary universes. "Even in degrees at least the
  characteristic" is covered since all `k` are included.
* `set_option backward.isDefEq.respectTransparency false` (as in the library's Laurent files)
  is needed for instance unification on `Kp p`; it does not change the statements.
* The remark's intermediate step (sup-norm values lie in `2^ℤ`) and its closing commentary are
  not separately stated. The ambient space `G` of a model lives in `Type` (as `C₀(ℕ, Kp p)` does).
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
  sorry

/-- **Remark I.3, norm comparison.** `‖x‖_∞ ≤ ‖x‖_w ≤ (3/2) ‖x‖_∞`. -/
theorem part2 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e)
    (g : G) :
    ‖e g‖ ≤ ‖g‖ ∧ ‖g‖ ≤ 3 / 2 * ‖e g‖ := by
  sorry

/-- **Remark I.3, the weighted norm is nonarchimedean and Banach.** -/
theorem part3 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e) :
    IsUltrametricDist G ∧ CompleteSpace G := by
  sorry

/-- **Remark I.3, the supremum norm is spherically complete.** -/
theorem part4 (p : ℕ) [Fact p.Prime] : SphericallyCompleteSpace C₀(ℕ, Kp p) := by
  sorry

/-- **Remark I.3, the explicit ball family.** The weighted balls `B_n` are nonempty, nested,
and have empty intersection. -/
theorem part5 (p : ℕ) [Fact p.Prime] :
    (∀ n, (weightedBall p n).Nonempty) ∧
      (∀ n, weightedBall p (n + 1) ⊆ weightedBall p n) ∧
      (⋂ n, weightedBall p n) = ∅ := by
  sorry

/-- **Remark I.3, the weighted norm is not spherically complete.** -/
theorem part6 (p : ℕ) [Fact p.Prime] (G : Type) [NormedAddCommGroup G]
    [NormedSpace (Kp p) G] (e : G ≃ₗ[Kp p] C₀(ℕ, Kp p)) (he : IsWeightedModel p G e) :
    ¬ SphericallyCompleteSpace G := by
  sorry

/-- **Remark I.3, analyticity for the supremum norm.** Precomposition into `c₀(ℕ,K)` with
its supremum norm is analytic at every point, in every degree, for all normed `E, E'`. -/
theorem part7 (p : ℕ) [Fact p.Prime] (E : Type uE) (E' : Type uE')
    [NormedAddCommGroup E] [NormedSpace (Kp p) E] [NormedAddCommGroup E'] [NormedSpace (Kp p) E']
    (k : ℕ) (f₀ : E →L[Kp p] E') :
    AnalyticAt (Kp p)
      (fun f : E →L[Kp p] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[Kp p] SupF p) →L[Kp p] (E [⋀^Fin k]→L[Kp p] SupF p))) f₀ := by
  sorry

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
  sorry

end AlternatingAnalyticChallenge.RemI_3
