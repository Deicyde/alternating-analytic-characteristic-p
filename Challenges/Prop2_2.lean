import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.Basic

/-!
# Proposition 2.2 (ambient polynomial action), p. 6

Paper statement (Section 2.2). For `f ∈ L(E, E')` and `g ∈ L(F, F')` the joint action is
`B(f, g)(m)(x₁, …, x_k) = g(m(f x₁, …, f x_k))`. "The joint action on multilinear maps
`B : L(E, E') × L(F, F') → L(Mult^k(E'; F), Mult^k(E; F'))` is the diagonal of a bounded
`(k + 1)`-linear map, and hence is `C^ω`. Its restriction to alternating inputs is analytic as
a map into `L(Alt^k(E'; F), Mult^k(E; F'))`, and all its values belong to the closed subspace
of operators taking values in `Alt^k(E; F')`."
In Section 2, `K` is a nontrivially normed field, the spaces are normed `K`-spaces, not assumed
complete, and products carry the maximum norm.

## Formalization notes
* `Mult^k(E; F)` is `ContinuousMultilinearMap K (fun _ : Fin k => E) F` and `Alt^k(E; F)` is
  `E [⋀^Fin k]→L[K] F`. `k = 0` is allowed.
* `multilinearAction k (f, g)` is the operator `m ↦ g ∘ m ∘ (f, …, f)`.
* `C^ω` is Mathlib's `ContDiff K ω`; "analytic" is `AnalyticOnNhd K _ Set.univ`.
* Restriction to alternating inputs is precomposition with
  `ContinuousAlternatingMap.toContinuousMultilinearMapCLM`.
* `part4` states that every value takes alternating values and that the set of operators taking
  values in `Alt^k(E; F')` (the range of `toContinuousMultilinearMap`) is closed.
* The bound `‖H‖ ≤ 1` from the proof is not stated.
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge.Prop2_2

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F']

/-- The joint action `B(f, g)(m) = g ∘ m ∘ (f, …, f)` on continuous multilinear maps. -/
noncomputable def multilinearAction (k : ℕ) (v : (E →L[K] E') × (F →L[K] F')) :
    ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F' :=
  (ContinuousLinearMap.compContinuousMultilinearMapL K (fun _ : Fin k => E) F F' v.2).comp
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => v.1))

/-- The joint action on multilinear maps is the diagonal of a
bounded `(k + 1)`-linear map. -/
theorem part1 (k : ℕ) :
    ∃ H : ContinuousMultilinearMap K (fun _ : Fin (k + 1) => (E →L[K] E') × (F →L[K] F'))
        (ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
          ContinuousMultilinearMap K (fun _ : Fin k => E) F'),
      ∀ v, H (fun _ => v) = multilinearAction k v := by
  sorry

/-- The joint action on multilinear maps is `C^ω`. -/
theorem part2 (k : ℕ) :
    ContDiff K ω (multilinearAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k) := by
  sorry

/-- The restriction of the joint action to alternating inputs is
analytic as a map into `L(Alt^k(E'; F), Mult^k(E; F'))`. -/
theorem part3 (k : ℕ) :
    AnalyticOnNhd K
      (fun v : (E →L[K] E') × (F →L[K] F') =>
        (multilinearAction k v).comp
          (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K :
            (E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E') F))
      Set.univ := by
  sorry

/-- Every value of the restricted action takes values in
`Alt^k(E; F')`, and the operators taking values in `Alt^k(E; F')` form a closed subset of
`L(Alt^k(E'; F), Mult^k(E; F'))`. -/
theorem part4 (k : ℕ) :
    (∀ (v : (E →L[K] E') × (F →L[K] F')) (m : E' [⋀^Fin k]→L[K] F),
      ∃ m' : E [⋀^Fin k]→L[K] F',
        m'.toContinuousMultilinearMap = multilinearAction k v m.toContinuousMultilinearMap) ∧
    IsClosed {T : (E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E) F' |
      ∀ m, T m ∈ Set.range
        (ContinuousAlternatingMap.toContinuousMultilinearMap :
          (E [⋀^Fin k]→L[K] F') → ContinuousMultilinearMap K (fun _ : Fin k => E) F')} := by
  sorry

end AlternatingAnalyticChallenge.Prop2_2
