import AlternatingAnalytic.Coordinates.CountableType.Dominated
import AlternatingAnalytic.Analysis.DenseMultilinearExtension
import AlternatingAnalytic.Analysis.FactorialInvertible
import AlternatingAnalytic.Analysis.SortedBasisLift

/-!
# Countable-type sources and targets: analytic scalar precomposition

Let `K` be complete and nonarchimedean. For a normed space `V` of countable type (a countable
set with dense span), `exists_sortedLift_of_countableType` produces a bounded linear operator `S`
on scalar `k`-linear forms with `alternatization (S m) = m` for every alternating `m`: descend
from the countable span `V₀` to its image in the bidual, apply the sorted lift for a van der Put
basis there, pull back, and extend from `V₀` by density. Neither completeness nor an ultrametric
norm is required of `V`.

As in the proof of Proposition I.1, `R = alternatization ∘ S` lifts
`A^k_{E,D;K}` when `E` has countable type, and `u ↦ alternatization (S_D m ∘ u)` lifts it when
`D` has countable type. Hence precomposition on scalar alternating forms is analytic in every
degree in both cases (`analyticAt_compContinuousLinearMapCLM_of_countableType_source`,
`analyticAt_compContinuousLinearMapCLM_of_countableType_target`).
-/

noncomputable section

open scoped BigOperators

namespace AlternatingAnalytic.CountableType

attribute [local instance] isUltrametricDist_continuousLinearMap

variable {K V E D : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup V] [NormedSpace K V] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup D] [NormedSpace K D]

/-- On a space of countable type, some bounded linear operator on scalar `k`-linear forms has
alternatization equal to the identity on alternating forms. -/
theorem exists_sortedLift_of_countableType [IsUltrametricDist K] [CompleteSpace K]
    (hV : ∃ S : Set V, S.Countable ∧ Dense (Submodule.span K S : Set V)) (k : ℕ) :
    ∃ L : ContinuousMultilinearMap K (fun _ : Fin k => V) K →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => V) K,
      ∀ g : V [⋀^Fin k]→L[K] K,
        ContinuousMultilinearMap.alternatization (L g.toContinuousMultilinearMap) = g := by
  obtain ⟨S, hS, hdense⟩ := hV
  let V₀ := Submodule.span K S
  have hd : DenseRange V₀.subtypeₗᵢ := by
    change Dense (Set.range V₀.subtypeₗᵢ)
    simpa using hdense
  obtain ⟨L₀, hL₀⟩ := exists_sortedLift_of_dominated (K := K) (V₀ := V₀)
    (Z := (V₀ →L[K] K) →L[K] K) (bidualEval K V₀) (Subtype.val ⁻¹' S)
    (hS.preimage Subtype.val_injective) (Submodule.span_span_coe_preimage) k
    (fun g v => by exact norm_le_mul_prod_bidualEval k g v)
  refine ⟨(denseMultilinearExtension V₀.subtypeₗᵢ hd k).comp (L₀.comp
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => V₀.subtypeL))),
    fun g => ?_⟩
  set L := (denseMultilinearExtension V₀.subtypeₗᵢ hd k).comp (L₀.comp
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => V₀.subtypeL)))
  let g₀ : V₀ [⋀^Fin k]→L[K] K := g.compContinuousLinearMap V₀.subtypeL
  have hL : ∀ y : Fin k → V₀, L g.toContinuousMultilinearMap (fun i => V₀.subtypeₗᵢ (y i)) =
      L₀ g₀.toContinuousMultilinearMap y := by
    intro y
    simp only [L, ContinuousLinearMap.comp_apply]
    rw [denseMultilinearExtension_apply]
    rfl
  have heq := (DenseRange.piMap (fun _ : Fin k => hd)).equalizer
    (ContinuousMultilinearMap.alternatization (L g.toContinuousMultilinearMap)).cont g.cont
    (funext fun x => by
      change ContinuousMultilinearMap.alternatization (L g.toContinuousMultilinearMap)
          (fun i => V₀.subtypeₗᵢ (x i)) = g (fun i => V₀.subtypeₗᵢ (x i))
      rw [ContinuousMultilinearMap.alternatization_apply_apply]
      calc ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
            L g.toContinuousMultilinearMap ((fun i => V₀.subtypeₗᵢ (x i)) ∘ σ)
          = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
            L₀ g₀.toContinuousMultilinearMap (x ∘ σ) :=
            Finset.sum_congr rfl fun σ _ => by
              rw [show ((fun i => V₀.subtypeₗᵢ (x i)) ∘ σ) =
                fun i => V₀.subtypeₗᵢ ((x ∘ σ) i) from rfl, hL]
        _ = ContinuousMultilinearMap.alternatization (L₀ g₀.toContinuousMultilinearMap) x :=
            (ContinuousMultilinearMap.alternatization_apply_apply _ _).symm
        _ = g₀ x := by rw [hL₀]
        _ = g (fun i => V₀.subtypeₗᵢ (x i)) := rfl)
  ext v
  exact congrFun heq v

/-- Proposition I.1, source case: if `E` has countable type, precomposition on scalar
alternating `k`-forms is analytic at every point. -/
theorem analyticAt_compContinuousLinearMapCLM_of_countableType_source
    [IsUltrametricDist K] [CompleteSpace K]
    (hE : ∃ S : Set E, S.Countable ∧ Dense (Submodule.span K S : Set E)) (k : ℕ)
    (u₀ : E →L[K] D) :
    AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  obtain ⟨L, hL⟩ := exists_sortedLift_of_countableType hE k
  let r := (ContinuousMultilinearMap.alternatizationCLM K E K).comp L
  exact (Round24Transfer.cpolynomialAt_of_lift (contractingRetractionLift (E' := D) k r)
    (contractingRetractionLift_diag k r hL) u₀).analyticAt

/-- The target-side lift `(u₁, …, u_k) ↦ (m ↦ alternatization (S m ∘ (u₁, …, u_k)))`. -/
def targetLift (k : ℕ)
    (L : ContinuousMultilinearMap K (fun _ : Fin k => D) K →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => D) K) :
    ContinuousMultilinearMap K (fun _ : Fin k => E →L[K] D)
      ((D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K)) :=
  (((ContinuousLinearMap.compL K (D [⋀^Fin k]→L[K] K)
      (ContinuousMultilinearMap K (fun _ : Fin k => D) K) (E [⋀^Fin k]→L[K] K)).flip
      (L.comp (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K))).comp
    (ContinuousLinearMap.compL K (ContinuousMultilinearMap K (fun _ : Fin k => D) K)
      (ContinuousMultilinearMap K (fun _ : Fin k => E) K) (E [⋀^Fin k]→L[K] K)
      (ContinuousMultilinearMap.alternatizationCLM K E K))).compContinuousMultilinearMap
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear K
      (fun _ : Fin k => E) (fun _ => D) K)

theorem targetLift_apply (k : ℕ)
    (L : ContinuousMultilinearMap K (fun _ : Fin k => D) K →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => D) K)
    (u : Fin k → E →L[K] D) (m : D [⋀^Fin k]→L[K] K) :
    targetLift k L u m = ContinuousMultilinearMap.alternatization
      ((L m.toContinuousMultilinearMap).compContinuousLinearMap u) := rfl

theorem targetLift_diag (k : ℕ)
    (L : ContinuousMultilinearMap K (fun _ : Fin k => D) K →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => D) K)
    (hL : ∀ g : D [⋀^Fin k]→L[K] K,
      ContinuousMultilinearMap.alternatization (L g.toContinuousMultilinearMap) = g)
    (u : E →L[K] D) :
    targetLift k L (fun _ => u) = Round24Transfer.Q K (Fin k) E D K u := by
  ext m x
  rw [targetLift_apply, ContinuousMultilinearMap.alternatization_apply_apply]
  change _ = m (fun i => u (x i))
  rw [← DFunLike.congr_fun (hL m) (fun i => u (x i)),
    ContinuousMultilinearMap.alternatization_apply_apply]
  rfl

/-- Proposition I.1, target case: if `D` has countable type, precomposition on scalar
alternating `k`-forms is analytic at every point. -/
theorem analyticAt_compContinuousLinearMapCLM_of_countableType_target
    [IsUltrametricDist K] [CompleteSpace K]
    (hD : ∃ S : Set D, S.Countable ∧ Dense (Submodule.span K S : Set D)) (k : ℕ)
    (u₀ : E →L[K] D) :
    AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  obtain ⟨L, hL⟩ := exists_sortedLift_of_countableType hD k
  exact (Round24Transfer.cpolynomialAt_of_lift (targetLift (E := E) k L)
    (targetLift_diag k L hL) u₀).analyticAt

end AlternatingAnalytic.CountableType
