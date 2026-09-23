import AlternatingAnalytic.Algebra.ClusterStaircase
import AlternatingAnalytic.Algebra.ClusterDiagonal
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Data.Finsupp.Pointwise

/-!
# The finite-field multiplier obstruction

Finite coloring of genuine coefficients, the support-rank argument, and the
polarized diagonal identity rule out bounded-support multiplier lifts when the
factorial of their degree vanishes in the field.
-/

open Finset Module

namespace AlternatingAnalytic

variable {L : Type*} [Field L] {k : ℕ}

/-- A function on a symmetric group invariant under all adjacent left
transpositions is constant. -/
theorem permutation_value_eq_of_adjacent {A : Type*} (n : ℕ)
    (f : Equiv.Perm (Fin (n + 1)) → A)
    (hadj : ∀ (i : Fin n) (τ : Equiv.Perm (Fin (n + 1))),
      f (Equiv.swap i.castSucc i.succ * τ) = f τ)
    (σ : Equiv.Perm (Fin (n + 1))) : f σ = f 1 := by
  classical
  have hmem : σ ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top σ
  have h : ∀ τ, f (σ * τ) = f τ := by
    induction hmem using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, rfl⟩ := hs
      exact hadj i
    | one => simp
    | mul s t _ _ hs ht =>
      intro τ
      rw [mul_assoc, hs, ht]
  simpa using h 1

/-- The finite-field obstruction on finitely supported inputs. The support
bound is required only on actual inputs taking their values in `{0,1,-1}`;
vector antisymmetry and the multiplier-wedge identity are genuine identities
of the given doubly multilinear map. -/
theorem finiteField_multiplier_obstruction [Finite L]
    (hfactorial : (k.factorial : L) = 0) (Ψ : ClusterMap L k)
    (hanti : ClusterVectorAntisymmetric Ψ) (hpol : ClusterPol1 Ψ)
    (d : ℕ) (hbound : ∀ (u v : Fin k → ℕ →₀ L),
      (∀ j x, u j x = 0 ∨ u j x = 1 ∨ u j x = -1) →
      (∀ j x, v j x = 0 ∨ v j x = 1 ∨ v j x = -1) →
      exteriorSupportDim (Ψ u v) ≤ d) : False := by
  classical
  cases k with
  | zero => simp at hfactorial
  | succ n =>
    obtain ⟨H, hH, hpattern⟩ := exists_infinite_clusterCoefficient_homogeneous Ψ
    obtain ⟨e, he, heH⟩ := exists_strictMono_in_infinite_set H hH
    let C : Fin (n + 1) → Fin 4 → ℕ := fun j p => e (4 * j.val + p.val)
    have hC : ∀ j, StrictMono (C j) := by
      intro j p q hpq
      apply he
      change 4 * j.val + p.val < 4 * j.val + q.val
      exact Nat.add_lt_add_left hpq _
    have hCH : ∀ j p, C j p ∈ H := fun j p => heH _
    have horder : ∀ j l, j < l → ∀ p q, C j p < C l q := by
      intro j l hjl p q
      apply he
      change 4 * j.val + p.val < 4 * l.val + q.val
      have := p.isLt
      change j.val < l.val at hjl
      omega
    let f : Equiv.Perm (Fin (n + 1)) → L :=
      fun τ => clusterValue Ψ (fun j => C (τ j))
    have hadj : ∀ (i : Fin n) (τ : Equiv.Perm (Fin (n + 1))),
        f (Equiv.swap i.castSucc i.succ * τ) = f τ := by
      intro i τ
      let α := τ.symm i.castSucc
      let β := τ.symm i.succ
      have hαβ : α ≠ β := by
        intro hab
        have h := congrArg (fun x => (τ x).val) hab
        simp only [α, β, Equiv.apply_symm_apply, Fin.val_castSucc, Fin.val_succ] at h
        omega
      have hsucc : (τ β).val = (τ α).val + 1 := by simp [α, β]
      have hswap : (Equiv.swap α β).trans τ = Equiv.swap i.castSucc i.succ * τ := by
        apply Equiv.ext
        intro j
        change τ (Equiv.swap α β j) = Equiv.swap i.castSucc i.succ (τ j)
        simpa [α, β] using τ.injective.map_swap α β j
      have h := clusterValue_adjacent_eq Ψ H hH hpattern d hbound τ α β hαβ hsucc
        (fun j => C (τ j)) (fun j => C ((Equiv.swap i.castSucc i.succ * τ) j))
        (fun j => hC _) (fun j => hC _) (fun j p => hCH _ p)
        (fun j p => hCH _ p) (fun j l hjl p q => horder _ _ hjl p q)
        (by
          intro j l hjl p q
          rw [hswap] at hjl
          exact horder _ _ hjl p q)
      exact h.symm
    have hconst : ∀ σ, f σ = f 1 := permutation_value_eq_of_adjacent n f hadj
    have hsum : (∑ σ, f σ) = 1 := by
      apply sum_clusterValue_perm_eq_one_of_separated Ψ hanti hpol C hC
      intro j l hjl
      rcases lt_or_gt_of_ne hjl with h | h
      · exact Or.inl (horder _ _ h)
      · exact Or.inr (horder _ _ h)
    have hone : (1 : L) = 0 := calc
      1 = ∑ σ, f σ := hsum.symm
      _ = ∑ _ : Equiv.Perm (Fin (n + 1)), f 1 := by
        exact Finset.sum_congr rfl (fun σ _ => hconst σ)
      _ = ((n + 1).factorial : L) * f 1 := by
        simp [Fintype.card_perm, nsmul_eq_mul]
      _ = 0 := by rw [hfactorial, zero_mul]
    exact one_ne_zero hone

section Restriction

variable {E : Type*} [AddCommGroup E] [Module L E]

/-- A doubly multilinear map with values in the exterior power of its input
space. The first group of inputs is the multiplier group. -/
abbrev MultiplierMap (L : Type*) [Field L] (k : ℕ) (E : Type*)
    [AddCommGroup E] [Module L E] :=
  MultilinearMap L (fun _ : Fin k => E)
    (MultilinearMap L (fun _ : Fin k => E) (⋀[L]^k E))

/-- Restrict both groups of inputs through `inc` and push the exterior output
forward through `out`. Its definition uses only multilinear-map composition. -/
noncomputable def restrictClusterMap (inc : (ℕ →₀ L) →ₗ[L] E)
    (out : E →ₗ[L] (ℕ → L)) (Ψ : MultiplierMap L k E) : ClusterMap L k :=
  ((exteriorPower.map k out).compMultilinearMapₗ L).compMultilinearMap
    ((MultilinearMap.compLinearMapₗ (fun _ : Fin k => inc)).compMultilinearMap
      (Ψ.compLinearMap fun _ => inc))

@[simp]
theorem restrictClusterMap_apply (inc : (ℕ →₀ L) →ₗ[L] E)
    (out : E →ₗ[L] (ℕ → L)) (Ψ : MultiplierMap L k E)
    (u v : Fin k → ℕ →₀ L) :
    restrictClusterMap inc out Ψ u v =
      exteriorPower.map k out (Ψ (fun j => inc (u j)) (fun j => inc (v j))) := rfl

/-- The obstruction is preserved by a genuine inclusion of finite sequences
into an input space and a compatible map from that space to all sequences.
The polarized identity is required only at the finite-sequence inputs. -/
theorem finiteField_multiplier_obstruction_of_restriction [Finite L]
    (hfactorial : (k.factorial : L) = 0)
    (inc : (ℕ →₀ L) →ₗ[L] E) (out : E →ₗ[L] (ℕ → L))
    (hcomp : ∀ x : ℕ →₀ L, out (inc x) = fun n => x n)
    (Ψ : MultiplierMap L k E)
    (hanti : ∀ (u v : Fin k → E) (σ : Equiv.Perm (Fin k)),
      Ψ u (v ∘ σ) = Equiv.Perm.sign σ • Ψ u v)
    (hpol : ∀ (u v : Fin k → ℕ →₀ L),
      (∑ σ : Equiv.Perm (Fin k), Ψ (fun j => inc (u (σ j))) (fun j => inc (v j))) =
        ∑ σ : Equiv.Perm (Fin k),
          exteriorPower.ιMulti L k (fun j => inc (u (σ j) * v j)))
    (d : ℕ) (hbound : ∀ (u v : Fin k → E), exteriorSupportDim (Ψ u v) ≤ d) :
    False := by
  classical
  refine finiteField_multiplier_obstruction hfactorial (restrictClusterMap inc out Ψ) ?_ ?_ d ?_
  · intro u v σ
    change exteriorPower.map k out
      (Ψ (fun j => inc (u j)) ((fun j => inc (v j)) ∘ σ)) = _
    rw [hanti]
    simp only [restrictClusterMap_apply, Units.smul_def, map_zsmul]
  · intro u v
    have h := congrArg (exteriorPower.map k out) (hpol u v)
    simpa only [map_sum, exteriorPower.map_apply_ιMulti, Function.comp_def,
      hcomp, Finsupp.mul_apply, restrictClusterMap_apply] using h
  · intro u v _ _
    exact (exteriorSupportDim_map_le out _).trans (hbound _ _)

/-- The full-sequence version of the paper's finite-field theorem. Its
polarized identity is needed only on finitely supported tuples. -/
theorem finiteField_multiplier_obstruction_full [Finite L]
    (hfactorial : (k.factorial : L) = 0) (Ψ : MultiplierMap L k (ℕ → L))
    (hanti : ∀ (u v : Fin k → ℕ → L) (σ : Equiv.Perm (Fin k)),
      Ψ u (v ∘ σ) = Equiv.Perm.sign σ • Ψ u v)
    (hpol : ∀ (u v : Fin k → ℕ →₀ L),
      (∑ σ : Equiv.Perm (Fin k), Ψ (fun j n => u (σ j) n) (fun j n => v j n)) =
        ∑ σ : Equiv.Perm (Fin k),
          exteriorPower.ιMulti L k (fun j n => u (σ j) n * v j n))
    (d : ℕ) (hbound : ∀ (u v : Fin k → ℕ → L), exteriorSupportDim (Ψ u v) ≤ d) :
    False := by
  exact finiteField_multiplier_obstruction_of_restriction hfactorial
    Finsupp.lcoeFun LinearMap.id (fun _ => rfl) Ψ hanti hpol d hbound

/-- The finite-sequence input and output version of the paper's finite-field
theorem. The exterior output is mapped to the exterior power of all sequences;
this cannot increase its support dimension. -/
theorem finiteField_multiplier_obstruction_finsupp [Finite L]
    (hfactorial : (k.factorial : L) = 0) (Ψ : MultiplierMap L k (ℕ →₀ L))
    (hanti : ∀ (u v : Fin k → ℕ →₀ L) (σ : Equiv.Perm (Fin k)),
      Ψ u (v ∘ σ) = Equiv.Perm.sign σ • Ψ u v)
    (hpol : ∀ (u v : Fin k → ℕ →₀ L),
      (∑ σ : Equiv.Perm (Fin k), Ψ (u ∘ σ) v) =
        ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti L k (fun j => u (σ j) * v j))
    (d : ℕ) (hbound : ∀ (u v : Fin k → ℕ →₀ L), exteriorSupportDim (Ψ u v) ≤ d) :
    False := by
  exact finiteField_multiplier_obstruction_of_restriction hfactorial
    LinearMap.id Finsupp.lcoeFun (fun _ => rfl) Ψ hanti hpol d hbound

end Restriction

end AlternatingAnalytic
