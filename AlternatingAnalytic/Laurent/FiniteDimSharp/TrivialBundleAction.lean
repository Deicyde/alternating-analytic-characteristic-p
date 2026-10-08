import AlternatingAnalytic.Laurent.FiniteDimSharp.Defs
import AlternatingAnalytic.Geometry.AnalyticAlternatingBundleMorphism
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Morphism preservation on trivial bundles

Over the model space `P` itself, with trivial bundles, an analytic family `U : P → L(A, A)` is an
analytic operator-valued section, and the section induced by the pair `(U, id)` has the
coordinates `x ↦ A(U x)`, `A(f) = (m ↦ m ∘ (f, …, f))`. Hence preservation of analytic morphisms
makes `x ↦ A(U x)` analytic for every continuous linear `U : P →L L(A, A)`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff
open Bundle

namespace AlternatingAnalytic.FiniteDimSharp

universe u

variable {K : Type u} [NontriviallyNormedField K] {P : Type u} [NormedAddCommGroup P]
  [NormedSpace K P] (A B : Type u) [NormedAddCommGroup A] [NormedSpace K A]
  [NormedAddCommGroup B] [NormedSpace K B]

/-- A continuous linear family `U : P →L L(A, A)` as an analytic section of the operator bundle of
the trivial bundle with fiber `A` over `P`. -/
noncomputable def trivialHomSection (U : P →L[K] (A →L[K] A)) :
    ContMDiffSection 𝓘(K, P) (A →L[K] A) ω (fun b ↦ Trivial P A b →L[K] Trivial P A b) where
  toFun x := U x
  contMDiff_toFun := by
    intro x₀
    rw [Bundle.contMDiffAt_section]
    have h : (fun x ↦ ((trivializationAt (A →L[K] A)
        (fun b ↦ Trivial P A b →L[K] Trivial P A b) x₀) ⟨x, U x⟩).2) = fun x ↦ U x := by
      funext x
      rw [hom_trivializationAt, Trivialization.continuousLinearMap_apply]
      ext v
      simp
    rw [h]
    exact U.contDiff.contMDiff.contMDiffAt

/-- Preservation of analytic morphisms makes `x ↦ A(U x)` analytic for every continuous linear
family `U : P →L L(A, A)`. -/
theorem analyticAt_compContinuousLinearMapCLM_of_preserves {k : ℕ}
    (h : PreservesAnalyticMorphisms K P k) (U : P →L[K] (A →L[K] A)) (x₀ : P) :
    AnalyticAt K (fun x ↦ (ContinuousAlternatingMap.compContinuousLinearMapCLM (U x) :
      (A [⋀^Fin k]→L[K] B) →L[K] (A [⋀^Fin k]→L[K] B))) x₀ := by
  obtain ⟨s, hs⟩ := h P A A B B (Trivial P A) (Trivial P A) (Trivial P B) (Trivial P B)
    (trivialHomSection A U) (contMDiffHomId (I := 𝓘(K, P)) (n := ω) B (Trivial P B))
  have hs' : ∀ x, s x = alternatingBundleMap k (U x) (ContinuousLinearMap.id K B) :=
    fun x ↦ ContinuousLinearMap.ext (hs x)
  have h1 := (Bundle.contMDiffAt_section x₀).mp (s.contMDiff x₀)
  have h2 : (fun x ↦ ((trivializationAt ((A [⋀^Fin k]→L[K] B) →L[K] (A [⋀^Fin k]→L[K] B))
      (fun b ↦ (Trivial P A b [⋀^Fin k]→L[K] Trivial P B b) →L[K]
        (Trivial P A b [⋀^Fin k]→L[K] Trivial P B b)) x₀) ⟨x, s x⟩).2) =
      fun x ↦ (ContinuousAlternatingMap.compContinuousLinearMapCLM (U x) :
        (A [⋀^Fin k]→L[K] B) →L[K] (A [⋀^Fin k]→L[K] B)) := by
    funext x
    rw [hs' x]
    refine (alternatingBundleMap_coordinates k (trivializationAt A (Trivial P A) x₀)
      (trivializationAt A (Trivial P A) x₀) (trivializationAt B (Trivial P B) x₀)
      (trivializationAt B (Trivial P B) x₀) x (by simp) (U x)
      (ContinuousLinearMap.id K B)).trans ?_
    ext m y
    simp [alternatingMapAction_apply, Trivialization.continuousLinearMap_apply]
    rfl
  rw [h2] at h1
  exact (contMDiffAt_iff_contDiffAt.mp h1).analyticAt

end AlternatingAnalytic.FiniteDimSharp
