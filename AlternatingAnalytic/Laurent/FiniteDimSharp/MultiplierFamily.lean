import AlternatingAnalytic.Laurent.FiniteDimSharp.Renorm
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Algebra.Module.Alternating.Topology

/-!
# A non-analytic multiplier family on an infinite-dimensional model space

Let `K` be a complete discretely valued ultrametric field, `E = ℓ^∞(ℕ, K)`, `D_a ∈ L(E, E)`
coordinatewise multiplication and `A(f) = (m ↦ m ∘ (f, …, f))` on `Alt^k(E; B)`. Suppose that
`a ↦ A(u₀ + D_a)` is analytic at no point of `c₀(ℕ, K)` (Proposition C.6 for `K = κ((X))`). If
`P` is an infinite-dimensional Banach space with an equivalent ultrametric norm, a complemented
copy `ι : c₀(ℕ, K) → P`, `π ∘ ι = id` (`exists_cZero_retraction_of_discrete`) gives the
continuous linear family `U x = D_{π x}`, and `x ↦ A(U x)` is not analytic at `ι 0`.
-/

open scoped BoundedContinuousFunction ZeroAtInfty

namespace AlternatingAnalytic.FiniteDimSharp

/-- The inclusion `c₀(ℕ, K) → ℓ^∞(ℕ, K)` as a continuous linear map. -/
noncomputable def cZeroToBCF (K : Type*) [NontriviallyNormedField K] :
    C₀(ℕ, K) →L[K] (ℕ →ᵇ K) where
  toFun := ZeroAtInftyContinuousMap.toBCF
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ZeroAtInftyContinuousMap.isometry_toBCF.continuous

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {e : ℝ}

/-- On an infinite-dimensional `P` with an equivalent ultrametric norm, the non-analyticity of
`a ↦ A(u₀ + D_a)` on `c₀(ℕ, K)` yields a continuous linear family `U : P →L L(ℓ^∞, ℓ^∞)` such
that `x ↦ A(U x)` is not analytic at some point. -/
theorem exists_not_analyticAt_of_not_finiteDimensional (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (hK : ∀ n : ℤ, ∃ c : K, ‖c‖ = e ^ n)
    (B : Type*) [NormedAddCommGroup B] [NormedSpace K B] (k : ℕ)
    (hC6 : ∀ (u₀ : (ℕ →ᵇ K) →L[K] (ℕ →ᵇ K)) (a₀ : C₀(ℕ, K)),
      ¬ AnalyticAt K (fun a : C₀(ℕ, K) =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (u₀ + ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF) :
          ((ℕ →ᵇ K) [⋀^Fin k]→L[K] B) →L[K] ((ℕ →ᵇ K) [⋀^Fin k]→L[K] B))) a₀)
    (P : Type*) [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P]
    (hP : HasEquivalentUltrametricNorm K P) (hinf : ¬ FiniteDimensional K P) :
    ∃ (U : P →L[K] ((ℕ →ᵇ K) →L[K] (ℕ →ᵇ K))) (x₀ : P),
      ¬ AnalyticAt K (fun x ↦ (ContinuousAlternatingMap.compContinuousLinearMapCLM (U x) :
        ((ℕ →ᵇ K) [⋀^Fin k]→L[K] B) →L[K] ((ℕ →ᵇ K) [⋀^Fin k]→L[K] B))) x₀ := by
  obtain ⟨ι, π, hπι⟩ := exists_cZero_retraction_of_discrete he hval hK hP hinf
  refine ⟨(ContinuousLinearMap.mul K (ℕ →ᵇ K)).comp ((cZeroToBCF K).comp π), ι 0, fun hU => ?_⟩
  apply hC6 0 0
  refine (hU.comp (ι.analyticAt 0)).congr (Filter.Eventually.of_forall fun a => ?_)
  have hUa : ((ContinuousLinearMap.mul K (ℕ →ᵇ K)).comp ((cZeroToBCF K).comp π)) (ι a) =
      ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF := by
    change ContinuousLinearMap.mul K (ℕ →ᵇ K) ((cZeroToBCF K) (π (ι a))) = _
    rw [hπι]
    rfl
  simp only [Function.comp_apply]
  congr 1
  rw [zero_add]
  exact hUa

end AlternatingAnalytic.FiniteDimSharp
