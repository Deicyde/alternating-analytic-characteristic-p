import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

import AlternatingAnalytic.Forms.Calculus.AmbientCalculus

/-!
# Proof of Theorem 7.2

Uses the library `AlternatingAnalytic/Forms/Calculus/` (namespace `AlternatingAnalytic.Forms`),
mainly `AmbientBasic.lean`, `AmbientDeriv.lean`, `WedgeAnalytic.lean` and `AmbientCalculus.lean`,
whose definitions of `IsAmbientAnalyticOn`, `wedge`, `extDeriv` and `pullback` have the same
bodies.
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge.Thm7_2

universe uK uP uP' uP''

section Defs

variable {K : Type uK} [NontriviallyNormedField K]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
  {P' : Type uP'} [NormedAddCommGroup P'] [NormedSpace K P']

/-- Ambient analyticity of a `k`-form `η` on `U`: `j ∘ η` is analytic on `U`, where
`j : Alt^k(P; K) → Mult^k(P; K)` is the inclusion. -/
def IsAmbientAnalyticOn {k : ℕ} (η : P → P [⋀^Fin k]→L[K] K) (U : Set P) : Prop :=
  AnalyticOnNhd K (fun y => (η y).toContinuousMultilinearMap) U

/-- The algebraic shuffle product of two scalar alternating maps. -/
noncomputable def wedgeAlg {k l : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K) :
    P [⋀^Fin (k + l)]→ₗ[K] K :=
  ((LinearMap.mul' K K).compAlternatingMap
    (μ.toAlternatingMap.domCoprod ν.toAlternatingMap)).domDomCongr finSumFinEquiv

/-- The shuffle product of continuous alternating maps is continuous. -/
theorem continuous_wedgeAlg {k l : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K) :
    Continuous (wedgeAlg μ ν) := by
  have h : ⇑(wedgeAlg μ ν) = fun v => ∑ σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l),
      LinearMap.mul' K K (AlternatingMap.domCoprod.summand μ.toAlternatingMap ν.toAlternatingMap σ
        (v ∘ finSumFinEquiv)) := by
    funext v
    simp [wedgeAlg, AlternatingMap.domCoprod_apply, map_sum, Function.comp_def]
  rw [h]
  refine continuous_finsetSum _ fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, map_zsmul_unit,
      LinearMap.mul'_apply, Function.comp_apply]
    simp only [Units.smul_def, zsmul_eq_mul]
    exact continuous_const.mul
      ((μ.cont.comp (continuous_pi fun i => continuous_apply _)).mul
        (ν.cont.comp (continuous_pi fun i => continuous_apply _)))

/-- The wedge (shuffle) product `μ ∧ ν ∈ Alt^{k+l}(P; K)`. -/
noncomputable def wedge {k l : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K) :
    P [⋀^Fin (k + l)]→L[K] K :=
  { wedgeAlg μ ν with cont := continuous_wedgeAlg μ ν }

/-- The exterior derivative, formula (7.1). -/
noncomputable def extDeriv {k : ℕ} (η : P → P [⋀^Fin k]→L[K] K) (y : P) :
    P [⋀^Fin (k + 1)]→L[K] K :=
  ContinuousAlternatingMap.alternatizeUncurryFin (fderiv K η y)

/-- Pullback `h^*η = (η ∘ h) ∘ (Dh, …, Dh)`. -/
noncomputable def pullback {k : ℕ} (h : P' → P) (η : P → P [⋀^Fin k]→L[K] K) (y : P') :
    P' [⋀^Fin k]→L[K] K :=
  (η (h y)).compContinuousLinearMap (fderiv K h y)

end Defs

variable (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
  {P' : Type uP'} [NormedAddCommGroup P'] [NormedSpace K P']
  {P'' : Type uP''} [NormedAddCommGroup P''] [NormedSpace K P'']

/-- Sheaf, locality: ambient analyticity on an open set is checked locally. -/
theorem sheaf_local {k : ℕ} (η : P → P [⋀^Fin k]→L[K] K) (U : Set P) :
    IsAmbientAnalyticOn η U ↔
      ∀ y ∈ U, ∃ V : Set P, IsOpen V ∧ y ∈ V ∧ IsAmbientAnalyticOn η V :=
  AlternatingAnalytic.Forms.isAmbientAnalyticOn_iff_local η U

/-- Sheaf, gluing: ambient analytic forms on the members of an open family that agree on
overlaps glue to an ambient analytic form on the union. -/
theorem sheaf_glue {k : ℕ} {ι : Type*} (V : ι → Set P) (hV : ∀ i, IsOpen (V i))
    (η : ι → P → P [⋀^Fin k]→L[K] K) (hη : ∀ i, IsAmbientAnalyticOn (η i) (V i))
    (hagree : ∀ i j, Set.EqOn (η i) (η j) (V i ∩ V j)) :
    ∃ θ : P → P [⋀^Fin k]→L[K] K,
      IsAmbientAnalyticOn θ (⋃ i, V i) ∧ ∀ i, Set.EqOn θ (η i) (V i) :=
  AlternatingAnalytic.Forms.exists_glue V hV η hη hagree

/-- Graded algebra: the zero form is ambient analytic. -/
theorem zero_mem {k : ℕ} (U : Set P) :
    IsAmbientAnalyticOn (fun _ : P => (0 : P [⋀^Fin k]→L[K] K)) U :=
  AlternatingAnalytic.Forms.isAmbientAnalyticOn_zero U

/-- Graded algebra: ambient analytic forms are closed under addition. -/
theorem add_mem {k : ℕ} {U : Set P} {η ζ : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) (hζ : IsAmbientAnalyticOn ζ U) :
    IsAmbientAnalyticOn (fun y => η y + ζ y) U :=
  AlternatingAnalytic.Forms.IsAmbientAnalyticOn.add hη hζ

/-- Graded algebra: ambient analytic forms are closed under scalar multiplication. -/
theorem smul_mem {k : ℕ} {U : Set P} (c : K) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) :
    IsAmbientAnalyticOn (fun y => c • η y) U :=
  AlternatingAnalytic.Forms.IsAmbientAnalyticOn.const_smul c hη

/-- Graded algebra: the wedge product of ambient analytic forms is ambient analytic. -/
theorem wedge_mem {k l : ℕ} {U : Set P} {η : P → P [⋀^Fin k]→L[K] K}
    {ζ : P → P [⋀^Fin l]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) (hζ : IsAmbientAnalyticOn ζ U) :
    IsAmbientAnalyticOn (fun y => wedge (η y) (ζ y)) U :=
  AlternatingAnalytic.Forms.IsAmbientAnalyticOn.wedge hη hζ

/-- Graded algebra: the constant `0`-form `1` is a left unit. -/
theorem one_wedge {k : ℕ} (μ : P [⋀^Fin k]→L[K] K) (v : Fin (0 + k) → P) :
    wedge (ContinuousAlternatingMap.constOfIsEmpty K P (Fin 0) (1 : K)) μ v =
      μ (v ∘ finCongr (Nat.zero_add k).symm) :=
  AlternatingAnalytic.Forms.one_wedge μ v

/-- Graded algebra: the constant `0`-form `1` is a right unit. -/
theorem wedge_one {k : ℕ} (μ : P [⋀^Fin k]→L[K] K) (v : Fin (k + 0) → P) :
    wedge μ (ContinuousAlternatingMap.constOfIsEmpty K P (Fin 0) (1 : K)) v =
      μ (v ∘ finCongr (Nat.add_zero k).symm) :=
  AlternatingAnalytic.Forms.wedge_one μ v

/-- The product is associative. -/
theorem wedge_assoc {k l m : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K)
    (θ : P [⋀^Fin m]→L[K] K) (v : Fin (k + l + m) → P) :
    wedge (wedge μ ν) θ v = wedge μ (wedge ν θ) (v ∘ finCongr (Nat.add_assoc k l m).symm) :=
  AlternatingAnalytic.Forms.wedge_assoc μ ν θ v

/-- The product is graded commutative. -/
theorem wedge_comm {k l : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K)
    (v : Fin (k + l) → P) :
    wedge μ ν v = (-1 : K) ^ (k * l) * wedge ν μ (v ∘ finCongr (Nat.add_comm l k)) :=
  AlternatingAnalytic.Forms.wedge_comm μ ν v

/-- Analytic maps induce pullbacks of ambient analytic forms. -/
theorem pullback_mem {k : ℕ} {U : Set P} {V : Set P'} (hV : IsOpen V) {h : P' → P}
    (hh : ContDiffOn K ω h V) (hmaps : Set.MapsTo h V U) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) :
    IsAmbientAnalyticOn (pullback h η) V :=
  AlternatingAnalytic.Forms.IsAmbientAnalyticOn.pullback hV hh hmaps hη

/-- Pullback along the identity is the identity. -/
theorem pullback_id {k : ℕ} (η : P → P [⋀^Fin k]→L[K] K) :
    pullback (fun y : P => y) η = η :=
  AlternatingAnalytic.Forms.pullback_id η

/-- Pullback is contravariantly functorial: `(h₂ ∘ h₁)^* = h₁^* ∘ h₂^*` on `V`. -/
theorem pullback_comp {k : ℕ} {V : Set P''} {W : Set P'} (hV : IsOpen V) (hW : IsOpen W)
    {h₁ : P'' → P'} {h₂ : P' → P} (hh₁ : ContDiffOn K ω h₁ V) (hh₂ : ContDiffOn K ω h₂ W)
    (hmaps : Set.MapsTo h₁ V W) (η : P → P [⋀^Fin k]→L[K] K) :
    Set.EqOn (pullback (h₂ ∘ h₁) η) (pullback h₁ (pullback h₂ η)) V :=
  AlternatingAnalytic.Forms.pullback_comp hV hW hh₁ hh₂ hmaps η

/-- Pullback commutes with the product. -/
theorem pullback_wedge {k l : ℕ} (h : P' → P) (η : P → P [⋀^Fin k]→L[K] K)
    (ζ : P → P [⋀^Fin l]→L[K] K) :
    pullback h (fun y => wedge (η y) (ζ y)) = fun y => wedge (pullback h η y) (pullback h ζ y) :=
  AlternatingAnalytic.Forms.pullback_wedge h η ζ

/-- The exterior derivative maps `Ω^k_amb(U)` to `Ω^{k+1}_amb(U)`. -/
theorem extDeriv_mem {k : ℕ} {U : Set P} (hU : IsOpen U) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) :
    IsAmbientAnalyticOn (extDeriv η) U :=
  AlternatingAnalytic.Forms.IsAmbientAnalyticOn.extDeriv hU hη

/-- `d² = 0`. -/
theorem extDeriv_extDeriv {k : ℕ} {U : Set P} (hU : IsOpen U) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) :
    ∀ y ∈ U, extDeriv (extDeriv η) y = 0 :=
  AlternatingAnalytic.Forms.extDeriv_extDeriv hU hη

/-- Pullback commutes with the exterior derivative. -/
theorem pullback_extDeriv {k : ℕ} {U : Set P} {V : Set P'} (hU : IsOpen U) (hV : IsOpen V)
    {h : P' → P} (hh : ContDiffOn K ω h V) (hmaps : Set.MapsTo h V U)
    {η : P → P [⋀^Fin k]→L[K] K} (hη : IsAmbientAnalyticOn η U) :
    Set.EqOn (extDeriv (pullback h η)) (pullback h (extDeriv η)) V :=
  AlternatingAnalytic.Forms.pullback_extDeriv hV hh hmaps hη

/-- The graded Leibniz rule `d(η ∧ ζ) = dη ∧ ζ + (-1)^k η ∧ dζ`. -/
theorem leibniz {k l : ℕ} {U : Set P} (hU : IsOpen U) {η : P → P [⋀^Fin k]→L[K] K}
    {ζ : P → P [⋀^Fin l]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) (hζ : IsAmbientAnalyticOn ζ U) :
    ∀ y ∈ U, ∀ v : Fin (k + l + 1) → P, extDeriv (fun x => wedge (η x) (ζ x)) y v =
      wedge (extDeriv η y) (ζ y) (v ∘ finCongr (by omega : k + 1 + l = k + l + 1)) +
        (-1 : K) ^ k * wedge (η y) (extDeriv ζ y) (v ∘ finCongr (by omega : k + (l + 1) = k + l + 1)) :=
  AlternatingAnalytic.Forms.leibniz hη hζ

end AlternatingAnalyticChallenge.Thm7_2
