import AlternatingAnalytic.Analysis.PaddedSplitRetraction

/-!
# The split retraction with auxiliary arguments last

The retraction `R` of Appendix H: restrict the first `p` arguments to `D`, fix the last `n` at the
auxiliary standard basis, apply the degree-`p` retraction, and wedge back. Since `Smap` inserts
the auxiliary argument first, each wedge step carries the sign of a cyclic shift.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair.Padding
variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
local instance canonicalNormedFieldK : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance canonicalFieldK : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField
local instance canonicalFieldL : Field (L p r) :=
  (inferInstance : NontriviallyNormedField (L p r)).toField

/-- Fix the last argument at `(0, 1)` and restrict the others to `V`. -/
def freezeLast {V F : Type*} [NormedAddCommGroup V] [NormedSpace (K p r) V]
    [NormedAddCommGroup F] [NormedSpace (K p r) F] (k : ℕ) :
    ((V × K p r) [×(k+1)]→L[K p r] F) →L[K p r] (V [×k]→L[K p r] F) :=
  (freezeFirst p r k).comp
    (ContinuousMultilinearMap.domDomCongrₗᵢ (K p r) (V × K p r) F
      (finRotate (k+1))).toLinearIsometry.toContinuousLinearMap

@[simp] theorem freezeLast_apply {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace (K p r) V]
    [NormedAddCommGroup F] [NormedSpace (K p r) F]
    (k : ℕ) (m : (V × K p r) [×(k+1)]→L[K p r] F) (x : Fin k → V) :
    freezeLast p r k m x = m (Fin.snoc (fun i => (x i,0)) (0,1)) := by
  change m (fun i => @Fin.cons k (fun _ => V × K p r)
    (0,1) (fun j => (x j,0)) (finRotate (k+1) i)) = _
  rw [← Fin.snoc_eq_cons_rotate]

/-- `wedgeSucc` with the sign `(-1)^(p+n)`, for the auxiliary-last order. -/
def wedgeLastSucc (n : ℕ) :
    (D p r n [⋀^Fin (p+n)]→L[K p r] G p r) →L[K p r]
      (D p r (n+1) [⋀^Fin (p+(n+1))]→L[K p r] G p r) :=
  (-1 : ℤ) ^ (p+n) • wedgeSucc p r n

/-- On alternating maps, `freezeLast` is `restrictSucc` up to the sign `(-1)^(p+n)`. -/
theorem freezeLast_alternating (n : ℕ)
    (m : D p r (n+1) [⋀^Fin (p+(n+1))]→L[K p r] G p r) :
    freezeLast p r (p+n)
      (m.toContinuousMultilinearMap.compContinuousLinearMap
        fun _ => (appendEquiv p r n).toContinuousLinearMap) =
      (-1 : ℤ) ^ (p+n) • (restrictSucc p r n m).toContinuousMultilinearMap := by
  apply ContinuousMultilinearMap.ext
  intro x
  rw [freezeLast_apply]
  change m (fun i => appendEquiv p r n (@Fin.snoc (p+n) (fun _ => D p r n × K p r)
    (fun j => (x j,0)) (0,1) i)) = _
  rw [Fin.snoc_eq_cons_rotate]
  have hs := m.toAlternatingMap.map_perm
    (fun i => appendEquiv p r n (@Fin.cons (p+n) (fun _ => D p r n × K p r) (0,1) (fun j => (x j,0)) i))
    (finRotate (p+n+1))
  have hsign : Equiv.Perm.sign (finRotate (p+n+1)) = (-1 : ℤˣ) ^ (p+n) := by
    simp [sign_finRotate]
  have hs' := hs.trans (congrArg (fun a : ℤˣ => a • m
    (fun i => appendEquiv p r n (@Fin.cons (p+n) (fun _ => D p r n × K p r)
      (0,1) (fun j => (x j,0)) i))) hsign)
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Function.comp_def, ContinuousAlternatingMap.coe_toAlternatingMap, smul_apply,
    ContinuousAlternatingMap.coe_toContinuousMultilinearMap, restrictSucc_apply] at hs' ⊢
  convert hs' using 1
  apply congrArg m
  funext i
  apply congrArg (appendEquiv p r n)
  rfl

/-- Fix the last `n` arguments at the auxiliary standard basis, in order. -/
def freezeAuxiliaryLast : (n : ℕ) →
    (D p r n [×(p+n)]→L[K p r] G p r) →L[K p r]
      (DeterminantPair.D p r [×p]→L[K p r] G p r)
  | 0 => ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => ContinuousLinearMap.inl (K p r) (DeterminantPair.D p r) (Fin 0 → K p r))
  | n+1 => (freezeAuxiliaryLast n).comp ((freezeLast p r (p+n)).comp
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ => (appendEquiv p r n).toContinuousLinearMap)))

/-- Iterated `wedgeLastSucc`. -/
def iteratedWedgeLast : (n : ℕ) →
    (DeterminantPair.D p r [⋀^Fin p]→L[K p r] G p r) →L[K p r]
      (D p r n [⋀^Fin (p+n)]→L[K p r] G p r)
  | 0 => ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.fst (K p r) (DeterminantPair.D p r) (Fin 0 → K p r))
  | n+1 => (wedgeLastSucc p r n).comp (iteratedWedgeLast n)

/-- The retraction `Mult^{p+n}(D_k; G) → Alt^{p+n}(D_k; G)` of Appendix H. -/
def canonicalRetraction (n : ℕ) :
    (D p r n [×(p+n)]→L[K p r] G p r) →L[K p r]
      (D p r n [⋀^Fin (p+n)]→L[K p r] G p r) :=
  (iteratedWedgeLast p r n).comp
    ((DeterminantPair.retractionR p r).comp (freezeAuxiliaryLast p r n))

@[simp] theorem canonicalRetraction_succ (n : ℕ)
    (m : D p r (n+1) [×(p+(n+1))]→L[K p r] G p r) :
    canonicalRetraction p r (n+1) m = wedgeLastSucc p r n
      (canonicalRetraction p r n (freezeLast p r (p+n)
        (m.compContinuousLinearMap fun _ => (appendEquiv p r n).toContinuousLinearMap))) := rfl

@[simp] theorem canonicalRetraction_fix (n : ℕ)
    (m : D p r n [⋀^Fin (p+n)]→L[K p r] G p r) :
    canonicalRetraction p r n m.toContinuousMultilinearMap = m := by
  induction n with
  | zero => exact paddedRetraction_fix p r 0 m
  | succ n ih =>
      rw [canonicalRetraction_succ, freezeLast_alternating, map_zsmul, ih]
      simp only [wedgeLastSucc, smul_apply, map_zsmul,
        wedgeSucc_restrictSucc, smul_smul]
      rw [← pow_add, (Even.add_self (p+n)).neg_one_pow, one_smul]

/-- The retraction of `det_k` takes the value `1` on the standard basis. -/
@[simp] theorem canonicalRetraction_determinantD_standard (n : ℕ) :
    (canonicalRetraction p r n (determinantD p r n).toContinuousMultilinearMap
      (standardD p r n) : L p r) = 1 := by
  rw [canonicalRetraction_fix, determinantD_standard]

@[simp] theorem appendEquiv_padTuple (n : ℕ)
    (x : Fin p → DeterminantPair.D p r) (i : Fin (p+n)) :
    appendEquiv p r n (padTuple p r n (DeterminantPair.D p r) x i,0) =
      padTuple p r (n+1) (DeterminantPair.D p r) x i.castSucc := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
      simp only [finSumFinEquiv_apply_left, Fin.castSucc_castAdd, padTuple_castAdd]
      refine Prod.ext rfl ?_
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [appendEquiv]
  | inr i =>
      change appendEquiv p r n
        (padTuple p r n (DeterminantPair.D p r) x (Fin.natAdd p i),0) =
        padTuple p r (n+1) (DeterminantPair.D p r) x (Fin.natAdd p i.castSucc)
      simp only [padTuple_natAdd]
      refine Prod.ext rfl ?_
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;>
        simp [appendEquiv, Pi.single_apply]

/-- `freezeAuxiliaryLast m x = m (x₁, …, x_p, e'₁, …, e'_n)` for every multilinear `m`. -/
theorem freezeAuxiliaryLast_apply (n : ℕ)
    (m : D p r n [×(p+n)]→L[K p r] G p r) (x : Fin p → DeterminantPair.D p r) :
    freezeAuxiliaryLast p r n m x = m (padTuple p r n (DeterminantPair.D p r) x) := by
  induction n with
  | zero =>
      change m (fun i => (x i,0)) = _
      apply congrArg m
      funext i
      simpa using (padTuple_castAdd p r 0 (DeterminantPair.D p r) x i).symm
  | succ n ih =>
      change freezeAuxiliaryLast p r n
        (freezeLast p r (p+n)
          (m.compContinuousLinearMap fun _ => (appendEquiv p r n).toContinuousLinearMap)) x = _
      rw [ih, freezeLast_apply]
      change m (fun i => appendEquiv p r n
        (@Fin.snoc (p+n) (fun _ => D p r n × K p r)
          (fun j => (padTuple p r n (DeterminantPair.D p r) x j,0)) (0,1) i)) = _
      apply congrArg m
      funext i
      refine Fin.lastCases (n := p+n) ?_ (fun j => ?_) i
      · simp only [Fin.snoc, Fin.val_last, lt_self_iff_false, ↓reduceDIte, cast_eq]
        rw [appendEquiv_auxiliary]
        change standardD p r (n+1) (Fin.natAdd p (Fin.last n)) =
          padTuple p r (n+1) (DeterminantPair.D p r) x (Fin.natAdd p (Fin.last n))
        simp only [standardD, padTuple, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
      · simp only [Fin.snoc_castSucc, appendEquiv_padTuple]

/-- `(D_k, G)` is split in degree `p + n`. -/
theorem isSplitAlternatingPair_canonical (n : ℕ) :
    IsSplitAlternatingPair (K p r) (p+n) (D p r n) (G p r) :=
  ⟨canonicalRetraction p r n, canonicalRetraction_fix p r n⟩

/-- Summary: the retraction, its formula, splitness and analytic self-action. -/
theorem canonical_padded_split_pair (n : ℕ) :
    (∀ (m : D p r n [×(p+n)]→L[K p r] G p r) (x : Fin p → DeterminantPair.D p r),
      freezeAuxiliaryLast p r n m x = m (padTuple p r n (DeterminantPair.D p r) x)) ∧
    canonicalRetraction p r n = (iteratedWedgeLast p r n).comp
      ((DeterminantPair.retractionR p r).comp (freezeAuxiliaryLast p r n)) ∧
    (∀ m : D p r n [⋀^Fin (p+n)]→L[K p r] G p r,
      canonicalRetraction p r n m.toContinuousMultilinearMap = m) ∧
    IsSplitAlternatingPair (K p r) (p+n) (D p r n) (G p r) ∧
    (∀ a : (D p r n →L[K p r] D p r n) × (G p r →L[K p r] G p r),
      AnalyticAt (K p r) (alternatingMapAction (K := K p r)
        (E := D p r n) (E' := D p r n) (F := G p r) (F' := G p r) (p+n)) a) := by
  refine ⟨freezeAuxiliaryLast_apply p r n, rfl, canonicalRetraction_fix p r n,
    isSplitAlternatingPair_canonical p r n, ?_⟩
  intro a
  exact analyticAt_alternatingMapAction_of_split_destination (p+n)
    (isSplitAlternatingPair_canonical p r n) a

end AlternatingAnalytic.DeterminantPair.Padding
