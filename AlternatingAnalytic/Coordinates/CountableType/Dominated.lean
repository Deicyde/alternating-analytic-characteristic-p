import AlternatingAnalytic.Coordinates.CountableType.Hull
import AlternatingAnalytic.Coordinates.CountableType.GramSchmidt
import AlternatingAnalytic.Coordinates.CountableType.SortedLift

/-!
# The sorted lift on a countably spanned, dominated space

Let `K` be complete and nonarchimedean, and let `V₀` be a normed space spanned by a countable set,
whose scalar `k`-linear forms are dominated by a continuous linear map `j` into an ultrametric
normed space: `‖g v‖ ≤ ‖g‖ ∏ₐ ‖j (v a)‖`. Descending to the image of `j`, applying the sorted lift
for a van der Put basis there, and pulling back gives a bounded linear operator `S` on scalar
forms with `alternatization (S g) = g` for alternating `g` (`exists_sortedLift_of_dominated`).
This is the core of Proposition I.1 (`prop:scalar-countable`); the bidual supplies `j`.
-/

noncomputable section

open scoped BigOperators

namespace AlternatingAnalytic.CountableType

variable {K : Type*} [NontriviallyNormedField K]

/-- **Sorted lift on a countably spanned space.** If `V₀` is spanned by a countable set and
scalar forms on `V₀` are dominated by a continuous linear map into an ultrametric space, there is
a bounded linear operator on scalar `k`-linear forms whose alternatization is the identity on
alternating forms. -/
theorem exists_sortedLift_of_dominated [CompleteSpace K] {V₀ Z : Type*}
    [NormedAddCommGroup V₀] [NormedSpace K V₀] [NormedAddCommGroup Z] [NormedSpace K Z]
    [IsUltrametricDist K] [IsUltrametricDist Z] (j : V₀ →L[K] Z) (S₀ : Set V₀)
    (hS₀ : S₀.Countable) (hspan₀ : Submodule.span K S₀ = ⊤) (k : ℕ)
    (hbound : ∀ (g : ContinuousMultilinearMap K (fun _ : Fin k => V₀) K) (v : Fin k → V₀),
      ‖g v‖ ≤ ‖g‖ * ∏ a, ‖j (v a)‖) :
    ∃ L : ContinuousMultilinearMap K (fun _ : Fin k => V₀) K →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => V₀) K,
      ∀ g : V₀ [⋀^Fin k]→L[K] K,
        ContinuousMultilinearMap.alternatization (L g.toContinuousMultilinearMap) = g := by
  set W := LinearMap.range (j : V₀ →ₗ[K] Z)
  let p : V₀ →L[K] W := j.codRestrict W fun x => LinearMap.mem_range_self _ x
  have hp : Function.Surjective p := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hpb : ∀ (g : ContinuousMultilinearMap K (fun _ : Fin k => V₀) K) (v : Fin k → V₀),
      ‖g v‖ ≤ ‖g‖ * ∏ a, ‖p (v a)‖ := hbound
  set T : Set W := (p : V₀ →ₗ[K] W) '' S₀
  have hT : T.Countable := hS₀.image _
  have hspan : Submodule.span K T = ⊤ := by
    rw [Submodule.span_image, hspan₀, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hp
  obtain ⟨ι, _, b, hb⟩ := exists_basis_coord_bound T hT hspan
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  refine ⟨(ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => p)).comp
    ((sortedLift b h2 hb k).comp (descend p hp hpb)), fun g => ?_⟩
  ext v
  rw [ContinuousMultilinearMap.alternatization_apply_apply]
  calc ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => p)).comp
          ((sortedLift b h2 hb k).comp (descend p hp hpb))) g.toContinuousMultilinearMap (v ∘ σ)
      = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        sortedLift b h2 hb k (descendAlt p hp hpb g).toContinuousMultilinearMap
          ((fun i => p (v i)) ∘ σ) := rfl
    _ = ContinuousMultilinearMap.alternatization
          (sortedLift b h2 hb k (descendAlt p hp hpb g).toContinuousMultilinearMap)
          (fun i => p (v i)) :=
        (ContinuousMultilinearMap.alternatization_apply_apply _ _).symm
    _ = g v := by rw [alternatization_sortedLift, descendAlt_apply_comp]

end AlternatingAnalytic.CountableType
