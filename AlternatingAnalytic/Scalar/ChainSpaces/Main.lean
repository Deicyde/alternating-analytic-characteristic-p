import AlternatingAnalytic.Scalar.ChainSpaces.NoLift
import AlternatingAnalytic.Scalar.ChainSpaces.Family
import AlternatingAnalytic.Analysis.PositiveCharacteristic
import AlternatingAnalytic.Analysis.SphericalCompleteness
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Data.Fintype.EquivFin

/-!
# Theorem F.1: the scalar counterexample, conditional on Lemmas F.2 and F.5

Let `K` be complete, not spherically complete, with `k! = 0` (so `K` is nonarchimedean and
`k ≥ 2`). Take the labels `L = Fin N` enumerating the finite family `F` of pairs `(Σ, Σ')`
(F.2), idempotents `ρ j`, `ρ' j` with kernels `Σ^j`, `Σ'^j`, and the chain-limit spaces
`E = chainSpace ρ ⊆ ℓ^∞(List L; K^{k+1})`, `E' = chainSpace ρ' ⊆ ℓ^∞(List L; K^k)` (F.6). They are
closed, contain `c₀`, are complete, ultrametric and not separable, and scalar precomposition
`A^k_{E,E';K}` is analytic at no point. Lemma F.3 (chain gap) is used from the library;
Lemma F.2 (multilinear tails, part 3) and Lemma F.5 (finite test certificate) enter as the
hypotheses `MultilinearDiagonalTail K` and `FiniteTestCertificate K k`.
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.ChainSpaces

universe u

/-- A normed field in which `k!` vanishes is nonarchimedean. -/
theorem isUltrametricDist_of_factorial_eq_zero {K : Type*} [NormedField K] {k : ℕ}
    (hk : (k.factorial : K) = 0) : IsUltrametricDist K := by
  have hdiv : ringChar K ∣ k.factorial := (CharP.cast_eq_zero_iff K (ringChar K) _).mp hk
  have hp : (ringChar K).Prime := by
    apply (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
    intro hz
    rw [hz, zero_dvd_iff] at hdiv
    exact Nat.factorial_ne_zero k hdiv
  have : Fact (ringChar K).Prime := ⟨hp⟩
  exact charP_isUltrametricDist (ringChar K)

theorem continuous_detV' (K : Type u) [NormedField K] (k : ℕ) : Continuous (detV' K k) := by
  have h : (detV' K k : (Fin k → Fin k → K) → K) =
      fun z => Matrix.det (Matrix.of fun a r => z r a) :=
    funext (detV'_apply K k)
  rw [h]
  exact Continuous.matrix_det (continuous_matrix fun a r =>
    (continuous_apply a).comp (continuous_apply r))

/-- The determinant `δ'` on `K^k` as a continuous alternating form. -/
noncomputable def detCont (K : Type u) [NormedField K] (k : ℕ) : (Fin k → K) [⋀^Fin k]→L[K] K where
  toMultilinearMap := (detV' K k).toMultilinearMap
  cont := continuous_detV' K k
  map_eq_zero_of_eq' := (detV' K k).map_eq_zero_of_eq'

theorem detCont_toAlternatingMap (K : Type u) [NormedField K] (k : ℕ) :
    (detCont K k).toAlternatingMap = detV' K k :=
  rfl

/-- The statement of Lemma F.2, part 3, for the field `K` and countably infinite index types in
`Type`: over a complete nonarchimedean, not spherically complete `K`, diagonal values of bounded
multilinear forms on `ℓ^∞(I, K)` tend to zero. -/
def MultilinearDiagonalTail (K : Type u) [NontriviallyNormedField K] : Prop :=
  ∀ [IsUltrametricDist K], ¬ SphericallyCompleteSpace K →
    ∀ (I : Type) [Countable I] [Infinite I] [DecidableEq I] {d : ℕ}, 1 ≤ d →
      ∀ μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K,
        Tendsto (fun i : I => μ (fun _ => lp.single ∞ i (1 : K))) cofinite (𝓝 0)

/-- The conclusion of Theorem F.1, part 2 (sequence-space form), in degree `k`. -/
def SequenceConclusion (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ)
    (E : Submodule K (lp (fun _ : Λ => Fin (k + 1) → K) ∞))
    (E' : Submodule K (lp (fun _ : Λ => Fin k → K) ∞)),
    IsClosed (E : Set (lp (fun _ : Λ => Fin (k + 1) → K) ∞)) ∧
    IsClosed (E' : Set (lp (fun _ : Λ => Fin k → K) ∞)) ∧
    (∀ x : lp (fun _ : Λ => Fin (k + 1) → K) ∞,
      Tendsto (fun i => (x : ∀ _ : Λ, Fin (k + 1) → K) i) cofinite (𝓝 0) → x ∈ E) ∧
    (∀ y : lp (fun _ : Λ => Fin k → K) ∞,
      Tendsto (fun i => (y : ∀ _ : Λ, Fin k → K) i) cofinite (𝓝 0) → y ∈ E') ∧
    CompleteSpace E ∧ CompleteSpace E' ∧ IsUltrametricDist E ∧ IsUltrametricDist E' ∧
    ¬ TopologicalSpace.SeparableSpace E ∧ ¬ TopologicalSpace.SeparableSpace E' ∧
    ∀ u₀ : E →L[K] E',
      ¬ AnalyticAt K
        (fun u : E →L[K] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (E' [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀

/-- The conclusion of Theorem F.1, part 1 (abstract form), in degree `k`. -/
def AbstractConclusion (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∃ (E E' : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
    (_ : IsUltrametricDist E)
    (_ : NormedAddCommGroup E') (_ : NormedSpace K E') (_ : CompleteSpace E')
    (_ : IsUltrametricDist E'),
    ∀ u₀ : E →L[K] E',
      ¬ AnalyticAt K
        (fun u : E →L[K] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (E' [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀

/-- **Theorem F.1, part 2, conditional on Lemmas F.2 and F.5.** -/
theorem sequenceConclusion_of_lemmas (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) (k : ℕ) (hk : (k.factorial : K) = 0)
    (hF2 : MultilinearDiagonalTail K) (hF5 : FiniteTestCertificate K k) :
    SequenceConclusion K k := by
  have : IsUltrametricDist K := isUltrametricDist_of_factorial_eq_zero hk
  have hk2 : 2 ≤ k := two_le_of_factorial_eq_zero K hk
  obtain ⟨T, hT, hcert⟩ := hF5 hk
  have := (pairFamily_finite K k).fintype
  let e : Fin (Fintype.card (pairFamily K k)) ≃ pairFamily K k := (Fintype.equivFin _).symm
  choose ρl hρidem hρker using fun j => exists_idempotent_ker K (e j).1.1
  choose ρl' hρ'idem hρ'ker using fun j => exists_idempotent_ker K (e j).1.2
  let ρ : Fin (Fintype.card (pairFamily K k)) → (Fin (k + 1) → K) →L[K] (Fin (k + 1) → K) :=
    fun j => LinearMap.toContinuousLinearMap (ρl j)
  let ρ' : Fin (Fintype.card (pairFamily K k)) → (Fin k → K) →L[K] (Fin k → K) :=
    fun j => LinearMap.toContinuousLinearMap (ρl' j)
  have hρ : ∀ j v, ρ j v = ρl j v := fun _ _ => rfl
  have hρ' : ∀ j v, ρ' j v = ρl' j v := fun _ _ => rfl
  let c₀ : Fin k := ⟨0, by omega⟩
  let c₁ : Fin k := ⟨1, by omega⟩
  have hc : c₀ < c₁ := by simp [c₀, c₁, Fin.lt_def]
  let j₀ := e.symm ⟨_, pairFamily_top_colEq K k hc⟩
  have hj₀ : (e j₀).1 = ((⊤ : Submodule K (Fin (k + 1) → K)), colEq K k c₀ c₁) := by
    simp [j₀]
  have : Nonempty (Fin (Fintype.card (pairFamily K k))) := ⟨j₀⟩
  refine ⟨List (Fin (Fintype.card (pairFamily K k))), inferInstance, chainSpace ρ, chainSpace ρ',
    isClosed_chainSpace ρ, isClosed_chainSpace ρ', fun x hx => mem_chainSpace_of_tendsto ρ hx,
    fun y hy => mem_chainSpace_of_tendsto ρ' hy, completeSpace_chainSpace ρ,
    completeSpace_chainSpace ρ', isUltrametricDist_chainSpace ρ, isUltrametricDist_chainSpace ρ',
    ?_, ?_, ?_⟩
  · refine not_separableSpace_chainSpace ρ (j := j₀) (v := Pi.single 0 1) ?_ ?_
    · exact fun h => by simpa using congrFun h 0
    · rw [hρ, hρker, hj₀]
      exact Submodule.mem_top
  · refine not_separableSpace_chainSpace ρ' (j := j₀) (v := fun _ => 1) ?_ ?_
    · exact fun h => one_ne_zero (congrFun h c₀)
    · rw [hρ', hρ'ker, hj₀]
      simp [colEq]
  · intro u₀
    refine not_analyticAt_compContinuousLinearMapCLM ρ ρ' (fun j v => hρidem j v)
      (fun j v => hρ'idem j v) (detCont K k)
      (fun j z hz => detV'_eq_zero_of_mem K k (e j).2 z fun r => (hρ'ker j (z r)).1 (hz r))
      (firstCoords K k) ?_ (fun μ => hF2 hK _ (by omega) μ) u₀
    refine ⟨fun j => T (e j).1, fun j t ht => ⟨fun r v hv => ?_, fun r => ?_⟩, fun τ hτ => ?_⟩
    · have hv' : v ∈ (e j).1.1 := (hρker j v).1 hv
      exact (hρ'ker j _).2 ((hT (e j).1 (e j).2 t ht).1 r (Submodule.mem_map_of_mem hv'))
    · exact (hρker j _).2 ((hT (e j).1 (e j).2 t ht).2 r)
    · obtain ⟨P, hP, t, ht, hge⟩ := hcert τ hτ
      exact ⟨e.symm ⟨P, hP⟩, t, by simpa using ht, hge⟩

/-- Part 2 of Theorem F.1 implies part 1. -/
theorem abstractConclusion_of_sequenceConclusion (K : Type u) [NontriviallyNormedField K]
    (k : ℕ) (h : SequenceConclusion K k) : AbstractConclusion K k := by
  obtain ⟨Λ, _, E, E', -, -, -, -, hE, hE', hu, hu', -, -, hna⟩ := h
  exact ⟨E, E', inferInstance, inferInstance, hE, hu, inferInstance, inferInstance, hE', hu', hna⟩

/-- **Theorem F.1, part 1, conditional on Lemmas F.2 and F.5.** -/
theorem abstractConclusion_of_lemmas (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) (k : ℕ) (hk : (k.factorial : K) = 0)
    (hF2 : MultilinearDiagonalTail K) (hF5 : FiniteTestCertificate K k) :
    AbstractConclusion K k :=
  abstractConclusion_of_sequenceConclusion K k (sequenceConclusion_of_lemmas K hK k hk hF2 hF5)

end AlternatingAnalytic.ChainSpaces
