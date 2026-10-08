import AlternatingAnalytic.Analysis.AnalyticFamilies
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Theorem 2.1 (lifting linear constructions to bundles), pp. 4–5

Setting (Section 2.1). `K` is a nontrivially normed field, `Vec_K` the category of normed
`K`-spaces and bounded linear maps (no completeness), `n ∈ ℕ ∪ {∞, ω}`. `M` is a fixed `Cⁿ`
manifold modelled on a normed space `P`. `VBⁿ_K(M)` is the category of `Cⁿ` normed vector
bundles over `M`, with morphisms over `id_M` whose local operator-valued expressions
`x ↦ T(x) ∈ L(E, F)` are `Cⁿ`. For a variance `ε = (ε₁, …, ε_r)`, `C^ε = C₁ × ⋯ × C_r` with each
`C_a = Vec_K` or `Vec_K^op`; a functor `C^ε → Vec_K` is `Cⁿ` if all its maps on products of hom
spaces (maximum norm) are jointly `Cⁿ`; `B^ε_M` is the corresponding product of bundle
categories.

Paper statement: "For a fixed `Cⁿ` manifold `M`, fiberwise application defines, up to canonical
natural isomorphism, a functor `Bⁿ_M : Fun^{Cⁿ}(C^ε, Vec_K) → Fun(B^ε_M, VBⁿ_K(M))`,
`F ↦ F_M`, `η ↦ η_M`. Here the category on the left is the full subcategory of the ordinary
functor category on the functors regular on hom spaces. The resulting bundles, bundle
morphisms, and natural transformations are given fiberwise by `F`, its action on maps, and the
components of `η`, respectively. The same conclusion holds if regularity on whole hom spaces is
replaced by preservation of `Cⁿ` families parametrized by open subsets of the model space `P`."

Formalization notes:
* **The general theorem has no formal statement here** (formal statement pending). Stating it
  needs definitions that exist neither in Mathlib nor in the library: `Cⁿ` functors of mixed
  variance on `Vec_K` (regular on products of hom spaces), the category `VBⁿ_K(M)` with
  operator-regular morphisms over `id_M` for arbitrary fibers, the induced functor `F_M` on
  products of bundle categories, the functor `Bⁿ_M` on natural transformations, and
  "up to canonical natural isomorphism". The library's `AnalyticBundleCat` is only the
  `n = ω`, model `𝓘(K, P)` version of `VBⁿ_K(M)` and is not used here.
* What is stated, as theorem `alternating_object_familywise`, is the special case the library
  covers: the familywise form of the theorem for the single functor
  `F = Alt^k : Vec_K^op × Vec_K → Vec_K` (variance `ε = (op, +)`), at the level of objects. Given
  two `Cⁿ` vector bundles `E₁`, `E₂` with model fibers `F₁`, `F₂`, if the joint action
  `alternatingMapAction k (u, v) : m ↦ v ∘ m ∘ (u, …, u)` (library definition, imported from
  `AlternatingAnalytic.Analysis.AnalyticFamilies`) maps `Cⁿ` families
  `γ : U → L(F₁, F₁) × L(F₂, F₂)` on open `U ⊆ M` to `Cⁿ` families, then the bundle
  `x ↦ Alt^k(E₁ x; E₂ x)` (Mathlib's `Bundle.ContinuousAlternatingMap` topology) is a `Cⁿ`
  vector bundle.
* Deviations of the special case from the paper's familywise hypothesis: families are
  parametrized by open subsets of `M` (`ContMDiffOn I …`), not of the model space `P`; only the
  automorphism-type hom spaces `L(F₁, F₁) × L(F₂, F₂)` of the model fibers are tested (these are
  where transition maps live). The base is an arbitrary `ChartedSpace H M` with model with
  corners `I : ModelWithCorners K P H`; the `IsManifold` structure is not assumed (not needed
  for the object statement). For boundaryless models such as `I = 𝓘(K, P)`, the paper's
  `P`-familywise hypothesis implies `hfamily` via charts, so the theorem is a true special case
  of the paper's statement. With boundary or corners, open subsets of `M` correspond in charts
  to subsets of `H` that need not be open in `P`, so `hfamily` is then a different condition,
  not simply a more general one. Index type `Fin k`. `n : ℕ∞ω` covers `ℕ ∪ {∞, ω}`.
* **Status.** The paper's claim has no formal statement yet (statement pending). The auxiliary
  special case `alternating_object_familywise` is exactly the library theorem
  `AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family`
  (`Geometry/AnalyticAlternatingBundle.lean`); `exact
  AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family k hfamily` closes it. It is
  kept here as a `sorry`'d auxiliary statement only; it is not the paper's claim.
* The morphism part, the natural-transformation part, functoriality of `Bⁿ_M`, and the version
  with regularity on whole hom spaces are not stated.
-/

open Bundle
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalyticChallenge.Thm2_1

-- formal statement pending: the general functor `Bⁿ_M` on `Cⁿ` mixed-variance functors needs
-- definitions absent from Mathlib and the library (see the module docstring). The theorem below
-- is an auxiliary special case only, proved verbatim by
-- `AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family`.

/-- **Theorem 2.1, alternating special case (objects, familywise form).** If the joint
alternating action preserves `Cⁿ` families on open subsets of the base, the bundle of continuous
alternating maps between two `Cⁿ` vector bundles is a `Cⁿ` vector bundle. -/
theorem alternating_object_familywise
    {K M F₁ F₂ : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
    [NormedAddCommGroup F₁] [NormedSpace K F₁]
    [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ E₂ : M → Type*}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    {P H : Type*} [NormedAddCommGroup P] [NormedSpace K P]
    [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners K P H} {n : ℕ∞ω}
    [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]
    (k : ℕ)
    (hfamily : ∀ {U : Set M}, IsOpen U →
      ∀ {γ : M → (F₁ →L[K] F₁) × (F₂ →L[K] F₂)},
        ContMDiffOn I 𝓘(K, (F₁ →L[K] F₁) × (F₂ →L[K] F₂)) n γ U →
        ContMDiffOn I 𝓘(K, (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂))
          n (AlternatingAnalytic.alternatingMapAction k ∘ γ) U) :
    ContMDiffVectorBundle n (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) I := by
  sorry

end AlternatingAnalyticChallenge.Thm2_1
