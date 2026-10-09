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

* The completion `K̂` is a complete nontrivially normed field `Kh` with an isometric inclusion
  `[NormedAlgebra K Kh]` of dense range (`hd`). This determines `K̂` up to isometric isomorphism;
  `UniformSpace.Completion K` has no `NontriviallyNormedField` instance in Mathlib.
* Restriction of scalars is `[NormedSpace K E] [IsScalarTower K Kh E]` on the same normed group
  (likewise `E'`, `F`).
* "Equal with the same norms" means `Kh`-linear isometric equivalences that do not change the
  underlying functions; `A^{k,K} = A^{k,K̂}` means these intertwine the two maps
  `ContinuousAlternatingMap.compContinuousLinearMapCLM`.
* "`P` is a lift over `K̂`" means: some continuous `Kh`-multilinear `P'` has the same values as
  `P` (after restricting scalars of the inputs), the same norm, and diagonal `A^{k,K̂}`. The norm
  on lift spaces is the multilinear operator norm, given by the local instance `liftOpNorm`.
* The degree index is `Fin k`. Completeness of `E, E', F` is assumed as in the paper but not
  needed.
-/

namespace AlternatingAnalyticChallenge.LemD_11

/-- The operator norm on candidate lifts `L(A, B)^n → L(Alt^k(B; C), Alt^k(A; C))`.
Instance search does not find `ContinuousMultilinearMap.hasOpNorm` here unaided. -/
noncomputable local instance liftOpNorm {R A B C : Type*} [NontriviallyNormedField R]
    [NormedAddCommGroup A] [NormedSpace R A] [NormedAddCommGroup B] [NormedSpace R B]
    [NormedAddCommGroup C] [NormedSpace R C] {k n : ℕ} :
    Norm (ContinuousMultilinearMap R (fun _ : Fin n => A →L[R] B)
      ((B [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := R) (E := fun _ : Fin n => A →L[R] B)
    (G := (B [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))

/-- Lemma D.11, map spaces: `L_K(E, E')`, `Alt^k_K(E; F)` and `Alt^k_K(E'; F)` equal their
`K̂` versions (same maps, same norms), and under these identifications `A^{k,K} = A^{k,K̂}`. -/
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

/-- Lemma D.11, lifts: every bounded `k`-linear lift of `A^{k,K}` over `K` is, as the same map, a
bounded `k`-linear lift of `A^{k,K̂}` over `K̂` with the same norm. -/
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
