import AlternatingAnalytic.Geometry.FiniteCoordinateManifoldFamilies

/-!
The definition displayed in Section 8.1 of the paper, verbatim.
Check it with `lake env lean paper/Section8.lean`.
-/

open scoped Manifold ContDiff
open AlternatingAnalytic

def PreservesAlternatingFamilies
    {K P H : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P]
    [TopologicalSpace H] (I : ModelWithCorners K P H)
    (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    (k : ℕ) (E E' F F' : Type*)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F'] : Prop :=
  let Op := (E' →L[K] E) × (F →L[K] F')
  let Out := (E [⋀^Fin k]→L[K] F) →L[K]
    (E' [⋀^Fin k]→L[K] F')
  ∀ {U : Set M} {γ : M → Op}, IsOpen U →
    ContMDiffOn I 𝓘(K, Op) n γ U →
    ContMDiffOn I 𝓘(K, Out) n
      (fun x ↦ alternatingMapAction k (γ x)) U
