import AlternatingAnalytic.MainTheorem

set_option backward.isDefEq.respectTransparency false

/-! The two challenge statements are proved from the actual Banach counterexample.
The prescribed-field result is proved first, then specialized to a characteristic-two
Laurent field for the global statement. Import this module separately from `challenge`. -/

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u

/-- Precomposition on degree-`k` continuous alternating maps is `C^ω` for every
pair of Banach spaces over `K`, with `E' = E` and index `Fin k`.
The field `K` itself need not be complete. -/
def BanachPrecompositionAnalytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F],
      ContDiff K ω
        (fun f : E →L[K] E =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)))

/-- For any prescribed nontrivially normed field of characteristic `p` and any
`k ≥ p`, assume `C^ω` precomposition for all Banach spaces with `E' = E` and index
`Fin k`. Then `False`. The field need not be complete. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) (hp : p.Prime)
    [CharP K p] (hpk : p ≤ k)
    (h : BanachPrecompositionAnalytic K k) : False := by
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, _, hno⟩ :=
    AlternatingAnalytic.exists_banach_counterexample_full.{u, 0} K p k hp hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  exact ((hno (Fin k) (by simp)).2 0).2 (h E F).contDiffAt

/-- Assume that precomposition on continuous alternating maps is `C^ω` for all
nontrivially normed fields, all normed spaces, and all finite index types. Then `False`. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] (E E' F : Type)
      [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] (ι : Type) [Fintype ι],
      ContDiff 𝕜 ω
        (fun f : E →L[𝕜] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))) : False := by
  let r : NNReal := 1 / 2
  let : Fact (0 < r) := ⟨by norm_num [r]⟩
  let : Fact (r < 1) := ⟨by norm_num [r]⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach
    (AlternatingAnalytic.LaurentField (ZMod 2) r) 2 2 Nat.prime_two le_rfl
  intro E F _ _ _ _ _ _
  exact h (AlternatingAnalytic.LaurentField (ZMod 2) r) E E F (Fin 2)

end AlternatingAnalyticChallenge
