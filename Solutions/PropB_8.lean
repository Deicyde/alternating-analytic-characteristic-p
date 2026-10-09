import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.GroupTheory.Perm.Sign
import AlternatingAnalytic.Algebra.Polarization
import AlternatingAnalytic.Algebra.FullPolarization
import AlternatingAnalytic.Algebra.FiniteHomogeneousIdentity
import AlternatingAnalytic.Algebra.PolarizationCounterexamples

/-!
# Proof of Proposition B.8

Uses `MultilinearMap.sum_perm_eq_of_multiplier_diagonal` (`Algebra/Polarization.lean`),
`MultilinearMap.sumOfType_eq_of_diagonal_eq` (`Algebra/FullPolarization.lean`), its finite-field
version `sumOfType_eq_of_diagonal_eq_of_card` (`Algebra/FiniteHomogeneousIdentity.lean`), and the
counterexamples in `Algebra/PolarizationCounterexamples.lean`.
-/

namespace AlternatingAnalyticChallenge.PropB_8

universe u v w

/-- A lift of `D` in degree `k`: a `2k`-linear map `Ψ : A^k × V^k → Λ^k V`, multilinear in the
`A`-slots and alternating in the `V`-slots. -/
abbrev Lift (L : Type u) [Field L] (A : Type v) [AddCommGroup A] [Module L A]
    (V : Type w) [AddCommGroup V] [Module L V] (k : ℕ) :=
  MultilinearMap L (fun _ : Fin k => A) (V [⋀^Fin k]→ₗ[L] ⋀[L]^k V)

/-- `type f = (|f⁻¹(1)|, …, |f⁻¹(m)|)` for a map `f : [k] → [m]`. -/
def typeOf {k m : ℕ} (f : Fin k → Fin m) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun i => f i = j).card

section

variable {L : Type u} [Field L] {A : Type v} [AddCommGroup A] [Module L A]
  {V : Type w} [AddCommGroup V] [Module L V] {k : ℕ}

/-- The pointwise identity (Pw). -/
def Pw (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) : Prop :=
  ∀ (a : A) (x : Fin k → V),
    Ψ (fun _ => a) x = exteriorPower.ιMulti L k (fun i => D a (x i))

/-- The polarized identity (Pol): for all `m ≥ 1`, `b ∈ A^m`, `α ∈ ℕ^m` with `|α| = k` and
`x ∈ V^k`, the sums over the maps `f : [k] → [m]` of type `α` agree. -/
def Pol (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (b : Fin m → A) (α : Fin m → ℕ), ∑ j, α j = k →
    ∀ x : Fin k → V,
      ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => typeOf f = α),
          Ψ (fun i => b (f i)) x =
        ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => typeOf f = α),
          exteriorPower.ιMulti L k (fun i => D (b (f i)) (x i))

/-- The multilinear instance (Pol1) of the polarized identity. -/
def Pol1 (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) : Prop :=
  ∀ (b : Fin k → A) (x : Fin k → V),
    ∑ σ : Equiv.Perm (Fin k), Ψ (fun i => b (σ i)) x =
      ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti L k (fun i => D (b (σ i)) (x i))

end

/-- Part (1): over every field, (Pol) ⇒ (Pw) ⇒ (Pol1). -/
theorem pol_imp_pw_and_pw_imp_pol1
    {L : Type u} [Field L] {A : Type v} [AddCommGroup A] [Module L A]
    {V : Type w} [AddCommGroup V] [Module L V] {k : ℕ} (hk : 1 ≤ k)
    (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) :
    (Pol D Ψ → Pw D Ψ) ∧ (Pw D Ψ → Pol1 D Ψ) := by
  refine ⟨fun hPol a x => ?_, fun hPw b x => ?_⟩
  · have h := hPol 1 le_rfl (fun _ => a) (fun _ => k) (by simp) x
    have hfilt : (Finset.univ.filter
        (fun f : Fin k → Fin 1 => typeOf f = fun _ => k)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro f _
      funext j
      have hj : ∀ i, f i = j := fun i => Subsingleton.elim _ _
      simp [typeOf, hj]
    rw [hfilt, Fintype.sum_unique, Fintype.sum_unique] at h
    simpa using h
  · let ev : (V [⋀^Fin k]→ₗ[L] ⋀[L]^k V) →ₗ[L] ⋀[L]^k V :=
      { toFun := fun g => g x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h := MultilinearMap.sum_perm_eq_of_multiplier_diagonal (ev.compMultilinearMap Ψ)
      (exteriorPower.ιMulti L k).toMultilinearMap D x (fun a => hPw a x) b
    simpa [ev] using h

/-- Part (2): if `L` is infinite, or `L = F_q` with `k ≤ q`, then (Pw) ⇒ (Pol). -/
theorem pw_imp_pol
    {L : Type u} [Field L] {A : Type v} [AddCommGroup A] [Module L A]
    {V : Type w} [AddCommGroup V] [Module L V] {k : ℕ} (hk : 1 ≤ k)
    (hL : Infinite L ∨ (Finite L ∧ k ≤ Nat.card L))
    (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) :
    Pw D Ψ → Pol D Ψ := by
  intro hPw m _ b α _ x
  let ev : (V [⋀^Fin k]→ₗ[L] ⋀[L]^k V) →ₗ[L] ⋀[L]^k V :=
    { toFun := fun g => g x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let M := ev.compMultilinearMap Ψ
  let N := (exteriorPower.ιMulti L k).toMultilinearMap.compLinearMap
    fun i => (LinearMap.applyₗ (R := L) (x i)).comp D
  have hdiag : ∀ a : A, M (fun _ => a) = N (fun _ => a) := fun a => by
    simpa [M, N, ev] using hPw a x
  have hsel : ∀ f : Fin k → Fin m, Polarization.selectionType f = typeOf f := by
    intro f; funext j
    simp only [Polarization.selectionType, typeOf]
    congr
  have key : M.sumOfType b α = N.sumOfType b α := by
    rcases hL with hinf | ⟨hfin, hcard⟩
    · exact MultilinearMap.sumOfType_eq_of_diagonal_eq M N hdiag b α
    · have : Fintype L := Fintype.ofFinite L
      exact MultilinearMap.sumOfType_eq_of_diagonal_eq_of_card M N
        (by rwa [Nat.card_eq_fintype_card] at hcard) hdiag b α
  simp only [MultilinearMap.sumOfType, hsel] at key
  convert key using 2 <;> simp [M, N, ev]

/-- Part (3): if `L = F_q` and `k ≥ q + 1`, some lift satisfies (Pw) but not (Pol). -/
theorem exists_pw_not_pol
    {L : Type u} [Field L] [Finite L] {k : ℕ} (hk : 1 ≤ k) (hkq : Nat.card L + 1 ≤ k) :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module L A)
      (V : Type u) (_ : AddCommGroup V) (_ : Module L V)
      (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k), Pw D Ψ ∧ ¬ Pol D Ψ := by
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨Ψ, hpw, hnpol⟩ := PolarizationCounterexamples.exists_pw_not_pol (K := L)
    (k := k) (by rwa [Nat.card_eq_fintype_card] at hkq)
  refine ⟨Fin 3 → L, inferInstance, inferInstance, Fin k → L, inferInstance, inferInstance,
    0, Ψ, hpw, fun hpol => hnpol ?_⟩
  intro b α hα x
  have hsel : ∀ f : Fin k → Fin 3, Polarization.selectionType f = typeOf f := by
    intro f; funext j
    simp only [Polarization.selectionType, typeOf]
    congr
  have h := hpol 3 (by norm_num) b α hα x
  simp only [MultilinearMap.sumOfType, hsel]
  convert h using 1
  let ev : ((Fin k → L) [⋀^Fin k]→ₗ[L] ⋀[L]^k (Fin k → L)) →ₗ[L] ⋀[L]^k (Fin k → L) :=
    { toFun := fun g => g x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact map_sum ev _ _

/-- Part (4): if `k! = 0` in `L`, some lift satisfies (Pol1) but not (Pw). -/
theorem exists_pol1_not_pw
    {L : Type u} [Field L] {k : ℕ} (hk : 1 ≤ k) (hfact : (k.factorial : L) = 0) :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module L A)
      (V : Type u) (_ : AddCommGroup V) (_ : Module L V)
      (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k), Pol1 D Ψ ∧ ¬ Pw D Ψ := by
  obtain ⟨Ψ, hpol1, hnpw⟩ := PolarizationCounterexamples.exists_pol1_not_pw (K := L) hfact
  exact ⟨L, inferInstance, inferInstance, Fin k → L, inferInstance, inferInstance,
    0, Ψ, hpol1, hnpw⟩

end AlternatingAnalyticChallenge.PropB_8
