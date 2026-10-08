import AlternatingAnalytic.Analysis.LaurentResidueLift
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Multipliers on a `c₀` base have no bounded lift

Proposition C.6, main part. Over `K₁ = κ((X))`, the homogeneous map
`σ(a) = W_B ∘ (D_a, …, D_a)` on `c₀(ℕ, K₁)` has no bounded `k`-linear lift into
`Alt^k(ℓ^∞(ℕ, K₁); B)` when `κ` is finite and `k! = 0` in `κ`. The residue of a hypothetical lift
is taken on finitely supported coefficient-field multipliers, which lie in `c₀`, and the
finite-field multiplier obstruction is applied to it.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Module
open scoped NNReal BoundedContinuousFunction ZeroAtInfty

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)

/-- A finitely supported coefficient-field sequence, as a null Laurent sequence. -/
def finsuppLaurentCZero (u : ℕ →₀ κ) : C₀(ℕ, LaurentField κ r) where
  toFun n := algebraMap κ (LaurentField κ r) (u n)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [u.support.eventually_cofinite_notMem] with n hn
    rw [Finsupp.notMem_support_iff.1 hn, map_zero]

@[simp]
theorem finsuppLaurentCZero_toBCF (u : ℕ →₀ κ) :
    (finsuppLaurentCZero κ r u).toBCF = constantLaurentArray κ r u := by
  ext n
  rfl

/-- Coefficient-field sequences have supremum norm at most one. -/
theorem norm_finsuppLaurentCZero_le_one (u : ℕ →₀ κ) : ‖finsuppLaurentCZero κ r u‖ ≤ 1 := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, finsuppLaurentCZero_toBCF]
  exact norm_constantLaurentArray_le_one κ r _

theorem finsuppLaurentCZero_add (u v : ℕ →₀ κ) :
    finsuppLaurentCZero κ r (u + v) = finsuppLaurentCZero κ r u + finsuppLaurentCZero κ r v := by
  ext n
  exact map_add (algebraMap κ (LaurentField κ r)) (u n) (v n)

theorem finsuppLaurentCZero_smul (c : κ) (u : ℕ →₀ κ) :
    finsuppLaurentCZero κ r (c • u) =
      algebraMap κ (LaurentField κ r) c • finsuppLaurentCZero κ r u := by
  ext n
  exact map_mul (algebraMap κ (LaurentField κ r)) c (u n)

theorem finsuppLaurentCZero_update {ι : Type*} [DecidableEq ι] (u : ι → ℕ →₀ κ) (i : ι)
    (a : ℕ →₀ κ) :
    (fun j => finsuppLaurentCZero κ r (Function.update u i a j)) =
      Function.update (fun j => finsuppLaurentCZero κ r (u j)) i (finsuppLaurentCZero κ r a) := by
  funext j
  exact Function.apply_update (fun _ => finsuppLaurentCZero κ r) u i a j

local notation "K" => LaurentField κ r
local notation "A" => ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
  ProjectiveExteriorCompletion (LaurentField κ r) ℕ k)

/-- The type of continuous `k`-linear maps on `c₀(ℕ, K₁)` with values in `Alt^k(E₁; B)`. -/
abbrev CZeroLiftCandidate : Type _ :=
  ContinuousMultilinearMap K (fun _ : Fin k => C₀(ℕ, LaurentField κ r)) A

/-- The coefficient-field action on `Alt^k(E₁; B)` is the action through `algebraMap`. -/
theorem czeroLaurentAlternating_algebraMap_smul (c : κ) (f : A) :
    algebraMap κ K c • f = c • f := by
  ext x
  exact algebraMap_smul K c (f x)

variable {κ r k}

/-- The coefficient-field residue of a lift over `c₀`, on finitely supported inputs. -/
def czeroResidue (α : Fin k) (P : CZeroLiftCandidate κ r k) : ClusterMap κ k where
  toFun u := MultilinearMap.compLinearMapₗ (fun _ => Finsupp.lcoeFun)
    (laurentResiduePost κ r k α (P (fun i => finsuppLaurentCZero κ r (u i))))
  map_update_add' u i a b := by
    rw [finsuppLaurentCZero_update, finsuppLaurentCZero_update, finsuppLaurentCZero_update,
      finsuppLaurentCZero_add, P.map_update_add, map_add, map_add]
  map_update_smul' u i c a := by
    rw [finsuppLaurentCZero_update, finsuppLaurentCZero_update, finsuppLaurentCZero_smul,
      P.map_update_smul, czeroLaurentAlternating_algebraMap_smul, map_smul, map_smul]

theorem czeroResidue_apply (α : Fin k) (P : CZeroLiftCandidate κ r k) (u v : Fin k → ℕ →₀ κ) :
    czeroResidue α P u v = completedLaurentCoefficient κ r ℕ k α
      (P (fun i => finsuppLaurentCZero κ r (u i)) (fun i => constantLaurentArray κ r (v i))) :=
  rfl

/-- The residue is antisymmetric in its vector slots. -/
theorem czeroResidue_antisymmetric (α : Fin k) (P : CZeroLiftCandidate κ r k) :
    ClusterVectorAntisymmetric (czeroResidue α P) := by
  intro u v σ
  have h := (P (fun i => finsuppLaurentCZero κ r (u i))).toAlternatingMap.map_perm
    (fun i => constantLaurentArray κ r (v i)) σ
  have h' := congrArg (completedLaurentCoefficient κ r ℕ k α) h
  simpa only [czeroResidue_apply, Function.comp_def, ContinuousAlternatingMap.coe_toAlternatingMap,
    Units.smul_def, map_zsmul] using h'

/-- The diagonal identity of a lift of `σ` descends to the coefficient-field wedge identity. -/
theorem czeroResidue_diagonal (α : Fin k) (P : CZeroLiftCandidate κ r k)
    (hP : ∀ a : C₀(ℕ, LaurentField κ r), P (fun _ => a) =
      (completedExteriorWedge K ℕ k).compContinuousLinearMap
        (ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF))
    (a : ℕ →₀ κ) (v : Fin k → ℕ →₀ κ) :
    czeroResidue α P (fun _ => a) v = exteriorPower.ιMulti κ k (fun i => ⇑a * ⇑(v i)) := by
  rw [czeroResidue_apply, hP]
  change completedLaurentCoefficient κ r ℕ k α
    (completedExteriorWedge K ℕ k (fun i =>
      boundedSequenceMultiplier K ℕ (finsuppLaurentCZero κ r a).toBCF
        (constantLaurentArray κ r (v i)))) = _
  simp only [finsuppLaurentCZero_toBCF, boundedSequenceMultiplier_constant]
  exact completedLaurentCoefficient_constant_wedge κ r ℕ k α _

/-- Fixing the vector arguments of the residue gives a multilinear map of the multipliers. -/
def czeroResidueFixedVectors (α : Fin k) (P : CZeroLiftCandidate κ r k) (v : Fin k → ℕ →₀ κ) :
    MultilinearMap κ (fun _ : Fin k => ℕ →₀ κ) (⋀[κ]^k (ℕ → κ)) where
  toFun u := czeroResidue α P u v
  map_update_add' u i a b := congrArg (fun f => f v)
    ((czeroResidue α P).map_update_add u i a b)
  map_update_smul' u i c a := congrArg (fun f => f v)
    ((czeroResidue α P).map_update_smul u i c a)

/-- Squarefree polarization of the diagonal identity. -/
theorem czeroResidue_pol1 (α : Fin k) (P : CZeroLiftCandidate κ r k)
    (hP : ∀ a : C₀(ℕ, LaurentField κ r), P (fun _ => a) =
      (completedExteriorWedge K ℕ k).compContinuousLinearMap
        (ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF)) :
    ClusterPol1 (czeroResidue α P) := by
  intro u v
  exact MultilinearMap.sum_perm_eq_of_multiplier_diagonal
    (czeroResidueFixedVectors α P v) (exteriorPower.ιMulti κ k).toMultilinearMap
    ((LinearMap.mul κ (ℕ → κ)).comp Finsupp.lcoeFun) (fun i => ⇑(v i))
    (fun a => czeroResidue_diagonal α P hP a v) u

/-- A single support bound for the residue on all finitely supported inputs. -/
theorem czeroResidue_support_le (α : Fin k) (P : CZeroLiftCandidate κ r k) :
    ∃ d : ℕ, ∀ u v : Fin k → ℕ →₀ κ, exteriorSupportDim (czeroResidue α P u v) ≤ d := by
  obtain ⟨C, hC, hbound⟩ := P.bound
  refine ⟨⌊(k : ℝ) * geometricWeightMaximum r * C⌋₊, fun u v => Nat.le_floor ?_⟩
  have hprod : (∏ i, ‖finsuppLaurentCZero κ r (u i)‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun i _ => norm_finsuppLaurentCZero_le_one κ r (u i))
  have hu : ‖P (fun i => finsuppLaurentCZero κ r (u i))‖ ≤ C :=
    (hbound _).trans (by simpa using mul_le_mul_of_nonneg_left hprod hC.le)
  have hx : ‖P (fun i => finsuppLaurentCZero κ r (u i)) (fun i => constantLaurentArray κ r (v i))‖ ≤
      ‖P (fun i => finsuppLaurentCZero κ r (u i))‖ := by
    simpa using ContinuousAlternatingMap.le_opNorm_mul_prod_of_le
      (P (fun i => finsuppLaurentCZero κ r (u i)))
      (fun i => norm_constantLaurentArray_le_one κ r (v i))
  rw [czeroResidue_apply]
  exact (completedLaurentCoefficient_support_le κ r ℕ k α _).trans
    (mul_le_mul_of_nonneg_left (hx.trans hu)
      (mul_nonneg (Nat.cast_nonneg k) (zero_le_one.trans (one_le_geometricWeightMaximum r))))

variable (κ r k)

/-- **Proposition C.6, main part, factorial form.** Over a finite coefficient field with
`k! = 0`, the multiplier map `a ↦ W_B ∘ (D_a, …, D_a)` on `c₀(ℕ, K₁)` has no bounded `k`-linear
lift. -/
theorem czero_not_exists_multiplierLift_of_factorial [Finite κ] (hk : 0 < k)
    (hfactorial : (k.factorial : κ) = 0) :
    ¬ ∃ P : CZeroLiftCandidate κ r k, ∀ a : C₀(ℕ, LaurentField κ r), P (fun _ => a) =
      (completedExteriorWedge K ℕ k).compContinuousLinearMap
        (ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF) := by
  rintro ⟨P, hP⟩
  let α : Fin k := ⟨0, hk⟩
  obtain ⟨d, hd⟩ := czeroResidue_support_le α P
  exact finiteField_multiplier_obstruction hfactorial (czeroResidue α P)
    (czeroResidue_antisymmetric α P) (czeroResidue_pol1 α P hP) d (fun u v _ _ => hd u v)

/-- **Proposition C.6, main part.** For `κ` finite of characteristic `p ≤ k`, the multiplier
map on `c₀(ℕ, K₁)` has no bounded `k`-linear lift. -/
theorem czero_not_exists_multiplierLift [Finite κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (hpk : p ≤ k) :
    ¬ ∃ P : CZeroLiftCandidate κ r k, ∀ a : C₀(ℕ, LaurentField κ r), P (fun _ => a) =
      (completedExteriorWedge K ℕ k).compContinuousLinearMap
        (ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF) := by
  apply czero_not_exists_multiplierLift_of_factorial κ r k
    ((Fact.out : p.Prime).pos.trans_le hpk)
  exact (CharP.cast_eq_zero_iff κ p k.factorial).2
    (Nat.dvd_factorial (Fact.out : p.Prime).pos hpk)

end AlternatingAnalytic
