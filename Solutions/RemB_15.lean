import AlternatingAnalytic.Algebra.DeterminantArray
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Sign
import AlternatingAnalytic.Algebra.NormalizedMultiplierLift

/-!
# Proof of Remark B.15

Uses `AlternatingAnalytic.normalizedMultiplierLift`, `normalizedClusterLift` and their lemmas
(`Algebra/NormalizedMultiplierLift.lean`).
-/

namespace AlternatingAnalyticChallenge.RemB_15

universe u

open Finset

/-- The normalized alternatization `Ψ_alt(u; x) = (1/k!) ∑_σ (u_{σ(1)} x₁) ∧ ⋯ ∧ (u_{σ(k)} x_k)`. -/
noncomputable def psiAlt (L : Type u) [Field L] (k : ℕ) (u x : Fin k → ℕ → L) :
    ⋀[L]^k (ℕ → L) :=
  (k.factorial : L)⁻¹ • ∑ σ : Equiv.Perm (Fin k),
    exteriorPower.ιMulti L k (fun i => fun n => u (σ i) n * x i n)

section ClusterDefinitions

variable {L : Type u} [Field L] {k : ℕ}

/-- The operator-slot weights `s = (1, 0, -1, 0)`. -/
def opWeight : Fin 4 → L := ![1, 0, -1, 0]

/-- The vector-slot weights `w = (1, -1, 1, -1)`. -/
def vecWeight : Fin 4 → L := ![1, -1, 1, -1]

/-- `s_C := ∑ᵢ sᵢ e_{C(i)}`. -/
noncomputable def sC (C : Fin 4 → ℕ) : ℕ →₀ L :=
  ∑ i, opWeight (L := L) i • Finsupp.single (C i) 1

/-- `w_C := ∑ᵢ wᵢ e_{C(i)}`. -/
noncomputable def wC (C : Fin 4 → ℕ) : ℕ →₀ L :=
  ∑ i, vecWeight (L := L) i • Finsupp.single (C i) 1

/-- The cluster value of `Ψ_alt`:
`χ(C₁, …, C_k) = Ω_{Ψ_alt(s_{C₁}, …, s_{C_k}; w_{C₁}, …, w_{C_k})}(C₁(1), …, C_k(1))`. -/
noncomputable def clusterValueAlt (L : Type u) [Field L] (k : ℕ) (C : Fin k → Fin 4 → ℕ) : L :=
  AlternatingAnalytic.determinantArray
    (psiAlt L k (fun j => ⇑(sC (L := L) (C j))) (fun j => ⇑(wC (L := L) (C j))))
    (fun j => C j 0)

end ClusterDefinitions

/-- `Ψ_alt` is a `2k`-linear map `V^k × V^k → Λ^k V`. -/
theorem psiAlt_multilinear {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) :
    ∃ Ψ : MultilinearMap L (fun _ : Fin k => ℕ → L)
        (MultilinearMap L (fun _ : Fin k => ℕ → L) (⋀[L]^k (ℕ → L))),
      ∀ u x : Fin k → ℕ → L, Ψ u x = psiAlt L k u x := by
  exact ⟨AlternatingAnalytic.normalizedMultiplierLift L k,
    fun u x => AlternatingAnalytic.normalizedMultiplierLift_apply L k u x⟩

/-- `Ψ_alt(u; x)` is alternating in `x`. -/
theorem psiAlt_alternating {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (u x : Fin k → ℕ → L) {i j : Fin k}
    (hx : x i = x j) (hij : i ≠ j) :
    psiAlt L k u x = 0 := by
  have h := AlternatingAnalytic.normalizedMultiplierLift_alternating L k u x hx hij
  rwa [AlternatingAnalytic.normalizedMultiplierLift_apply] at h

/-- `Ψ_alt` satisfies (Pol1) for the multipliers `D_u x = ux`. -/
theorem psiAlt_pol1 {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (u x : Fin k → ℕ → L) :
    ∑ σ : Equiv.Perm (Fin k), psiAlt L k (fun j => u (σ j)) x =
      ∑ σ : Equiv.Perm (Fin k),
        exteriorPower.ιMulti L k (fun j => fun n => u (σ j) n * x j n) := by
  have h := AlternatingAnalytic.normalizedMultiplierLift_pol1 L k hfact u x
  simp only [AlternatingAnalytic.normalizedMultiplierLift_apply] at h
  exact h

/-- `sdim(Ψ_alt(u; x)) ≤ k²`. -/
theorem exteriorSupportDim_psiAlt_le {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (u x : Fin k → ℕ → L) :
    AlternatingAnalytic.exteriorSupportDim (psiAlt L k u x) ≤ k ^ 2 := by
  have h := AlternatingAnalytic.exteriorSupportDim_normalizedMultiplierLift_le L k u x
  rwa [AlternatingAnalytic.normalizedMultiplierLift_apply] at h

/-- For pairwise disjoint clusters the cluster value of `Ψ_alt` is `1/k!`. -/
theorem clusterValueAlt_eq_inv_factorial {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (C : Fin k → Fin 4 → ℕ) (hC : ∀ j, StrictMono (C j))
    (hdisj : ∀ j l, j ≠ l → ∀ p q, C j p ≠ C l q) :
    clusterValueAlt L k C = (k.factorial : L)⁻¹ := by
  have hinj : Function.Injective (fun t : Fin k × Fin 4 => C t.1 t.2) := by
    rintro ⟨j, p⟩ ⟨l, q⟩ h
    by_cases hjl : j = l
    · subst hjl
      exact Prod.ext rfl ((hC j).injective h)
    · exact absurd h (hdisj j l hjl p q)
  have h := AlternatingAnalytic.clusterValue_normalizedClusterLift L k C hinj
  rw [AlternatingAnalytic.clusterValue, AlternatingAnalytic.normalizedClusterLift_apply,
    AlternatingAnalytic.normalizedMultiplierLift_apply] at h
  exact h

end AlternatingAnalyticChallenge.RemB_15
