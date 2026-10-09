import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances

/-!
# Lemma D.11 (incomplete base fields), p. 47

Paper statement (Appendix D, "Incomplete base fields"). "Let `K` be a nontrivially normed field
with completion `K̂`, and let `E, E', F` be `K̂`-Banach spaces, regarded as `K`-Banach spaces by
restriction of scalars (with the same norms). Then `L_K(E,E') = L_{K̂}(E,E')`,
`Alt^k_K(E;F) = Alt^k_{K̂}(E;F)` and `Alt^k_K(E';F) = Alt^k_{K̂}(E';F)` with the same norms,
`A^{k,K}_{E,E';F} = A^{k,K̂}_{E,E';F}`, and every bounded `k`-linear lift of `A^{k,K}_{E,E';F}`
over `K` is a bounded `k`-linear lift of `A^{k,K̂}_{E,E';F}` over `K̂`."

## Formalization notes

* The completion `K̂` is modelled abstractly as a complete nontrivially normed field `Kh` with an
  isometric scalar inclusion `[NormedAlgebra K Kh]` of dense range (`hd`). This characterizes the
  completion up to isometric isomorphism; `UniformSpace.Completion K` is not used because Mathlib
  has no `NontriviallyNormedField` instance on it (the library's instance lives in the proving
  module).
* "Regarded as `K`-Banach spaces by restriction of scalars (with the same norms)" is
  `[NormedSpace K E] [IsScalarTower K Kh E]` on the same normed group (likewise `E'`, `F`).
* Equality of the map spaces "as sets with the same norms" is expressed by `Kh`-linear isometric
  equivalences that do not change the underlying functions; "`A^{k,K} = A^{k,K̂}`" is the
  statement that these identifications intertwine the two precomposition maps
  `ContinuousAlternatingMap.compContinuousLinearMapCLM`.
* "`P` is a lift over `K̂`" is expressed as: there is a continuous `Kh`-multilinear `P'` with the
  same values as `P` (after restricting scalars of the inputs), the same norm, and diagonal
  `A^{k,K̂}`. `‖·‖` on lift spaces is the usual multilinear operator norm, supplied by the local
  instance `liftOpNorm` (needed only because instance search does not find it unaided).
* Degree index is `Fin k`. Completeness of `E, E', F` is included as in the paper (it is not
  needed for the conclusion). No Lean modules of this library are imported.
-/

namespace AlternatingAnalyticChallenge.LemD_11

/-- The standard operator norm on the space of candidate lifts
`L(A, B)^n → L(Alt^k(B; C), Alt^k(A; C))`, exposed as a local instance because typeclass search
does not find `ContinuousMultilinearMap.hasOpNorm` through the nested alternating-map codomain
on its own. (This mirrors the library's local instance in `DenseScalarLiftTransport.lean`.) -/
noncomputable local instance liftOpNorm {R A B C : Type*} [NontriviallyNormedField R]
    [NormedAddCommGroup A] [NormedSpace R A] [NormedAddCommGroup B] [NormedSpace R B]
    [NormedAddCommGroup C] [NormedSpace R C] {k n : ℕ} :
    Norm (ContinuousMultilinearMap R (fun _ : Fin n => A →L[R] B)
      ((B [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := R) (E := fun _ : Fin n => A →L[R] B)
    (G := (B [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))

/-- Lemma D.11, map spaces: `L_K(E, E') = L_{K̂}(E, E')`, `Alt^k_K(E; F) = Alt^k_{K̂}(E; F)` and
`Alt^k_K(E'; F) = Alt^k_{K̂}(E'; F)` (same underlying maps, same norms), and
`A^{k,K}_{E,E';F} = A^{k,K̂}_{E,E';F}` under these identifications. -/
theorem map_spaces_eq
    (K Kh : Type*) [NontriviallyNormedField K] [NontriviallyNormedField Kh]
    [NormedAlgebra K Kh] [CompleteSpace Kh] (hd : DenseRange (algebraMap K Kh))
    (E E' F : Type*)
    [NormedAddCommGroup E] [NormedSpace Kh E] [CompleteSpace E]
    [NormedSpace K E] [IsScalarTower K Kh E]
    [NormedAddCommGroup E'] [NormedSpace Kh E'] [CompleteSpace E']
    [NormedSpace K E'] [IsScalarTower K Kh E']
    [NormedAddCommGroup F] [NormedSpace Kh F] [CompleteSpace F]
    [NormedSpace K F] [IsScalarTower K Kh F] (k : ℕ) :
    ∃ (eL : (E →L[K] E') ≃ₗᵢ[Kh] (E →L[Kh] E'))
      (eA : (E [⋀^Fin k]→L[K] F) ≃ₗᵢ[Kh] (E [⋀^Fin k]→L[Kh] F))
      (eA' : (E' [⋀^Fin k]→L[K] F) ≃ₗᵢ[Kh] (E' [⋀^Fin k]→L[Kh] F)),
      (∀ (f : E →L[K] E') (x : E), eL f x = f x) ∧
      (∀ (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E), eA m x = m x) ∧
      (∀ (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E'), eA' m x = m x) ∧
      ∀ (f : E →L[K] E') (m : E' [⋀^Fin k]→L[K] F),
        eA (ContinuousAlternatingMap.compContinuousLinearMapCLM f m) =
          ContinuousAlternatingMap.compContinuousLinearMapCLM (eL f) (eA' m) := by
  sorry

/-- Lemma D.11, lifts: every bounded `k`-linear lift `P` of `A^{k,K}_{E,E';F}` over `K` is (as the
same map, after the identifications above) a bounded `k`-linear lift of `A^{k,K̂}_{E,E';F}` over
`K̂`, with the same norm. -/
theorem lift_is_lift_over_completion
    (K Kh : Type*) [NontriviallyNormedField K] [NontriviallyNormedField Kh]
    [NormedAlgebra K Kh] [CompleteSpace Kh] (hd : DenseRange (algebraMap K Kh))
    (E E' F : Type*)
    [NormedAddCommGroup E] [NormedSpace Kh E] [CompleteSpace E]
    [NormedSpace K E] [IsScalarTower K Kh E]
    [NormedAddCommGroup E'] [NormedSpace Kh E'] [CompleteSpace E']
    [NormedSpace K E'] [IsScalarTower K Kh E']
    [NormedAddCommGroup F] [NormedSpace Kh F] [CompleteSpace F]
    [NormedSpace K F] [IsScalarTower K Kh F] (k : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin k => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)))
    (hP : ∀ f : E →L[K] E',
      P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f) :
    ∃ P' : ContinuousMultilinearMap Kh (fun _ : Fin k => E →L[Kh] E')
        ((E' [⋀^Fin k]→L[Kh] F) →L[Kh] (E [⋀^Fin k]→L[Kh] F)),
      (∀ (g : Fin k → E →L[Kh] E') (m : E' [⋀^Fin k]→L[Kh] F) (x : Fin k → E),
        P' g m x = P (fun i => (g i).restrictScalars K) (m.restrictScalars K) x) ∧
      ‖P'‖ = ‖P‖ ∧
      ∀ g : E →L[Kh] E',
        P' (fun _ => g) = ContinuousAlternatingMap.compContinuousLinearMapCLM g := by
  sorry

end AlternatingAnalyticChallenge.LemD_11
