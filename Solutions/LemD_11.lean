import AlternatingAnalytic.Analysis.DenseScalarLiftTransport
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances

/-!
# Lemma D.11 (incomplete base fields), p. 47

Solution: the statements of `Challenges/LemD_11.lean`, proved from
`AlternatingAnalytic/Analysis/DenseScalarRestriction.lean` (`denseScalarLinearEquiv`,
`denseScalarAlternatingEquiv`) and `AlternatingAnalytic/Analysis/DenseScalarLiftTransport.lean`
(`denseScalarLiftTransport`, `norm_denseScalarLiftTransport`,
`denseScalarLiftTransport_diagonal`).
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
          ContinuousAlternatingMap.compContinuousLinearMapCLM (eL f) (eA' m) :=
  ⟨AlternatingAnalytic.denseScalarLinearEquiv hd, AlternatingAnalytic.denseScalarAlternatingEquiv hd,
    AlternatingAnalytic.denseScalarAlternatingEquiv hd, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

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
        P' (fun _ => g) = ContinuousAlternatingMap.compContinuousLinearMapCLM g :=
  ⟨AlternatingAnalytic.denseScalarLiftTransport hd P, fun _ _ _ => rfl,
    AlternatingAnalytic.norm_denseScalarLiftTransport hd P,
    AlternatingAnalytic.denseScalarLiftTransport_diagonal hd P hP⟩

end AlternatingAnalyticChallenge.LemD_11
