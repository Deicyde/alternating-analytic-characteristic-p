import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.LaurentCoefficients
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import AlternatingAnalytic.Analysis.LaurentResidueTheorem

/-!
# Lemma C.4 (the coefficient lift `Ψ`), pp. 38-39

Solution: `Ψ := AlternatingAnalytic.laurentResidueLift κ r k ⟨0, _⟩ P`
(`Analysis/LaurentResidueLift.lean`) with `laurentResidueLift_apply`,
`laurentResidueLift_alternating`, `laurentResidueLift_support_le`, `laurentResidueLift_pol1`
(same file) and `laurentResidueLift_pol` (`Analysis/LaurentResiduePolarization.lean`); bundled
as `laurentResidueLift_full_properties` in `Analysis/LaurentResidueTheorem.lean`. The given `η`
equals `completedLaurentCoefficient` by `completedLaurentCoefficient_unique`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.LemC_4

open AlternatingAnalytic

universe u

/-- The constant-coefficient map `coeff₀ : ℓ^∞(S, κ((X))) → κ^S`, taken coordinatewise. -/
noncomputable def coeff0 (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    {S : Type*} [TopologicalSpace S] (y : S →ᵇ LaurentField κ r) : S → κ :=
  fun s => LaurentField.coeff κ r 0 (y s)

/-- `M_r := max_{l ∈ ℕ} (l + 1) r^l`. -/
noncomputable def Mr (r : ℝ≥0) : ℝ := ⨆ l : ℕ, ((l : ℝ) + 1) * (r : ℝ) ^ l

/-- The type of a map `f : [k] → J`: the multiplicity `|f⁻¹(j)|` of each label `j`. -/
noncomputable def selectionType {J : Type*} [Fintype J] {k : ℕ} (f : Fin k → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => f i = j)).card

/-- Candidates for a bounded `k`-linear lift of `A^k_{E,E;F}`: continuous `k`-linear maps
`L(E,E)^k → L(Alt^k(E;F), Alt^k(E;F))`. -/
abbrev LiftCandidate (K : Type*) [NontriviallyNormedField K]
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) : Type _ :=
  ContinuousMultilinearMap K (fun _ : Fin k => E →L[K] E)
    ((E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))

/-- The multilinear operator norm `‖P‖` of a lift candidate. -/
noncomputable def liftNorm {K : Type*} [NontriviallyNormedField K]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] {k : ℕ} (P : LiftCandidate K E F k) : ℝ :=
  @Norm.norm _ (ContinuousMultilinearMap.hasOpNorm (𝕜 := K) (E := fun _ : Fin k => E →L[K] E)
    (G := (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) P

/-- The hypotheses of Lemma C.4, and its four conclusions. -/
theorem coefficient_lift
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k)
    (P : LiftCandidate (LaurentField κ r) (ℕ →ᵇ LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) k)
    (hP : ∀ f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r),
      P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f)
    (Ωκ : (⋀[κ]^k (ℕ → κ)) →ₗ[κ] ((Fin k → ℕ) → κ))
    (hΩκ : ∀ (y : Fin k → ℕ → κ) (c : Fin k → ℕ),
      Ωκ (exteriorPower.ιMulti κ k y) c = Matrix.det (fun a b => y b (c a)))
    (η : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k → ⋀[κ]^k (ℕ → κ))
    (hη : ∀ b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
      Ωκ (η b) = coeff0 κ r (completedExteriorArray (LaurentField κ r) ℕ k b)) :
    ∃ Ψ : MultilinearMap κ (fun _ : Fin k => ℕ → κ)
        (MultilinearMap κ (fun _ : Fin k => ℕ → κ) (⋀[κ]^k (ℕ → κ))),
      -- (Ψ1): `Ψ = η ∘ Φ` on `E₀^{2k}`, and `Ψ` is `2k`-linear over `κ` (by its type)
      (∀ u x : Fin k → ℕ → κ,
        Ψ u x = η (P (fun i => ContinuousLinearMap.mul (LaurentField κ r)
            (ℕ →ᵇ LaurentField κ r) (constantLaurentArray κ r (u i)))
          (completedExteriorWedge (LaurentField κ r) ℕ k)
          (fun i => constantLaurentArray κ r (x i)))) ∧
      -- (Ψ2): alternating in the last `k` slots
      (∀ (u x : Fin k → ℕ → κ) (i j : Fin k), i ≠ j → x i = x j → Ψ u x = 0) ∧
      -- (Ψ3): uniform support bound
      (∀ u x : Fin k → ℕ → κ,
        exteriorSupportDim (Ψ u x) ≤ ⌊(k : ℝ) * Mr r * liftNorm P⌋₊) ∧
      -- (Ψ4): the polarized identity (Pol)
      (∀ (m : ℕ), 1 ≤ m → ∀ (b : Fin m → ℕ → κ) (α : Fin m → ℕ), ∑ j, α j = k →
        ∀ x : Fin k → ℕ → κ,
          (∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => selectionType f = α),
              Ψ (fun i => b (f i)) x) =
            ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => selectionType f = α),
              exteriorPower.ιMulti κ k (fun i => b (f i) * x i)) ∧
      -- (Pol1)
      (∀ u x : Fin k → ℕ → κ,
        (∑ σ : Equiv.Perm (Fin k), Ψ (u ∘ σ) x) =
          ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti κ k (fun i => u (σ i) * x i)) := by
  have hΩ : Ωκ = determinantArray := by
    apply exteriorPower.linearMap_ext
    ext y c
    simp [hΩκ, determinantArray_ιMulti]
  subst hΩ
  have hb : BddAbove (Set.range fun l : ℕ => ((l : ℝ) + 1) * (r : ℝ) ^ l) :=
    ⟨geometricWeightMaximum r, Set.forall_mem_range.2 (geometricWeight_le_maximum r)⟩
  have hMr : Mr r = geometricWeightMaximum r := by
    apply le_antisymm (ciSup_le (geometricWeight_le_maximum r))
    unfold geometricWeightMaximum
    exact le_ciSup hb _
  let α : Fin k := ⟨0, by omega⟩
  have hηeq : ∀ b, η b = completedLaurentCoefficient κ r ℕ k α b := fun b =>
    completedLaurentCoefficient_unique κ r ℕ k α b (η b) (hη b)
  refine ⟨laurentResidueLift κ r k α P, fun u x => ?_,
    fun u x i j hij hx => laurentResidueLift_alternating κ r k α P u x hij hx,
    fun u x => ?_, fun m _ b ν _ x => ?_, laurentResidueLift_pol1 κ r k α P hP⟩
  · rw [laurentResidueLift_apply, hηeq]
    rfl
  · rw [hMr]
    exact laurentResidueLift_support_le κ r k α P u x
  · exact laurentResidueLift_pol κ r k α P hP b ν x

end AlternatingAnalyticChallenge.LemC_4
