import AlternatingAnalytic.Forms.Calculus.WedgeAnalytic
import AlternatingAnalytic.Forms.Calculus.UncurryShuffle

/-!
# Ambient differential calculus (Theorem 7.2, chart level)

Collects the laws of Theorem 7.2 for ambient analytic forms on an open subset of a normed
space: the wedge product is unital, associative and graded commutative (`wedge_assoc`,
`wedge_comm`), `d` preserves ambient analyticity, `d² = 0`, and the graded Leibniz rule holds.
As in the paper, there is no restriction on the characteristic or the degree. Pullbacks are in `AmbientBasic.lean`.
-/

set_option maxSynthPendingDepth 3

open Filter Set
open scoped ContDiff

namespace AlternatingAnalytic.Forms

variable {K : Type*} [NontriviallyNormedField K]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace K P] {k l m : ℕ}

/-- The constant `0`-form `1` is a left unit for the wedge product. -/
theorem one_wedge (μ : P [⋀^Fin k]→L[K] K) (v : Fin (0 + k) → P) :
    wedge (ContinuousAlternatingMap.constOfIsEmpty K P (Fin 0) (1 : K)) μ v =
      μ (v ∘ finCongr (Nat.zero_add k).symm) :=
  shuffle_constOfIsEmpty_left μ.toAlternatingMap v

/-- The constant `0`-form `1` is a right unit for the wedge product. -/
theorem wedge_one (μ : P [⋀^Fin k]→L[K] K) (v : Fin (k + 0) → P) :
    wedge μ (ContinuousAlternatingMap.constOfIsEmpty K P (Fin 0) (1 : K)) v =
      μ (v ∘ finCongr (Nat.add_zero k).symm) :=
  shuffle_constOfIsEmpty_right μ.toAlternatingMap v

/-- The wedge product is associative. -/
theorem wedge_assoc (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K)
    (θ : P [⋀^Fin m]→L[K] K) (v : Fin (k + l + m) → P) :
    wedge (wedge μ ν) θ v = wedge μ (wedge ν θ) (v ∘ finCongr (Nat.add_assoc k l m).symm) :=
  shuffle_assoc μ.toAlternatingMap ν.toAlternatingMap θ.toAlternatingMap v

/-- The wedge product is graded commutative. -/
theorem wedge_comm (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K)
    (v : Fin (k + l) → P) :
    wedge μ ν v = (-1 : K) ^ (k * l) * wedge ν μ (v ∘ finCongr (Nat.add_comm l k)) :=
  shuffle_comm μ.toAlternatingMap ν.toAlternatingMap v

/-- The exterior derivative as an algebraic `alternatizeUncurryFin`. -/
theorem toAlternatingMap_extDeriv (η : P → P [⋀^Fin k]→L[K] K) (y : P) :
    (extDeriv η y).toAlternatingMap = AlternatingMap.alternatizeUncurryFin
      (ContinuousAlternatingMap.toAlternatingMapLinear ∘ₗ (fderiv K η y : P →ₗ[K] _)) :=
  ContinuousAlternatingMap.toAlternatingMap_alternatizeUncurryFin _

/-- The graded Leibniz rule `d(η ∧ ζ) = dη ∧ ζ + (-1)^k η ∧ dζ`. -/
theorem leibniz {U : Set P} {η : P → P [⋀^Fin k]→L[K] K} {ζ : P → P [⋀^Fin l]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) (hζ : IsAmbientAnalyticOn ζ U) :
    ∀ y ∈ U, ∀ v : Fin (k + l + 1) → P, extDeriv (fun x => wedge (η x) (ζ x)) y v =
      wedge (extDeriv η y) (ζ y) (v ∘ finCongr (by omega : k + 1 + l = k + l + 1)) +
        (-1 : K) ^ k *
          wedge (η y) (extDeriv ζ y) (v ∘ finCongr (by omega : k + (l + 1) = k + l + 1)) := by
  intro y hy v
  have h1 := sum_shuffle_left_removeNth
    (ContinuousAlternatingMap.toAlternatingMapLinear ∘ₗ (fderiv K η y : P →ₗ[K] _))
    (ζ y).toAlternatingMap v
  have h2 := sum_shuffle_right_removeNth (η y).toAlternatingMap
    (ContinuousAlternatingMap.toAlternatingMapLinear ∘ₗ (fderiv K ζ y : P →ₗ[K] _)) v
  rw [wedge_apply, wedge_apply, toAlternatingMap_extDeriv, toAlternatingMap_extDeriv, ← h1,
    ← smul_eq_mul, ← h2, ← Finset.sum_add_distrib]
  change ContinuousAlternatingMap.alternatizeUncurryFin _ v = _
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_wedge_apply (hη y hy) (hζ y hy), ContinuousAlternatingMap.add_apply, smul_add]
  rfl

variable [CompleteSpace K]

/-- The exterior derivative maps ambient analytic `k`-forms to ambient analytic `(k+1)`-forms. -/
theorem IsAmbientAnalyticOn.extDeriv {U : Set P} (hU : IsOpen U) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) : IsAmbientAnalyticOn (Forms.extDeriv η) U :=
  isAmbientAnalyticOn_extDeriv hU hη

/-- `d² = 0` for ambient analytic forms. -/
theorem extDeriv_extDeriv {U : Set P} (hU : IsOpen U) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) : ∀ y ∈ U, Forms.extDeriv (Forms.extDeriv η) y = 0 :=
  fun _ hy => extDeriv_extDeriv_apply hU hη hy

end AlternatingAnalytic.Forms
