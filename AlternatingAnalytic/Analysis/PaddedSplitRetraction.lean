import AlternatingAnalytic.Analysis.DeterminantCoefficientPadding
import AlternatingAnalytic.Analysis.DeterminantCoefficientEquiv
import AlternatingAnalytic.Analysis.DeterminantPairAllAlternating
import AlternatingAnalytic.Analysis.SplitAlternatingPairs
import Mathlib.GroupTheory.Perm.Fin

/-! Concrete division-free split retractions on the literal padded determinant sources. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AlternatingAnalytic.DeterminantPair.Padding
variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
local instance splitNormedFieldK : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance splitFieldK : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField
local instance splitFieldL : Field (L p r) :=
  (inferInstance : NontriviallyNormedField (L p r)).toField

/-- Append the new rational coordinate to the literal maximum-norm product. -/
def appendEquiv (n : ℕ) : (D p r n × K p r) ≃L[K p r] D p r (n+1) where
  toFun x := (x.1.1, Fin.snoc x.1.2 x.2)
  invFun x := ((x.1, Fin.init x.2), x.2 (Fin.last n))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    refine Prod.ext rfl ?_
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    refine Prod.ext rfl ?_
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  continuous_toFun := continuous_fst.fst.prodMk (Continuous.finSnoc (A := fun _ : Fin (n+1) => K p r) continuous_fst.snd continuous_snd)
  continuous_invFun := by fun_prop

@[simp] theorem appendEquiv_apply (n : ℕ) (x : D p r n × K p r) :
    appendEquiv p r n x = (x.1.1, Fin.snoc x.1.2 x.2) := rfl

@[simp] theorem appendEquiv_symm_apply (n : ℕ) (x : D p r (n+1)) :
    (appendEquiv p r n).symm x = ((x.1, Fin.init x.2), x.2 (Fin.last n)) := rfl

/-- Curry and boundedly evaluate the first auxiliary argument, then restrict the
remaining arguments to the first factor. This is defined on arbitrary multilinear maps. -/
def freezeFirst {V F : Type*} [NormedAddCommGroup V] [NormedSpace (K p r) V]
    [NormedAddCommGroup F] [NormedSpace (K p r) F] (k : ℕ) :
    ((V × K p r) [×(k+1)]→L[K p r] F) →L[K p r] (V [×k]→L[K p r] F) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inl (K p r) V (K p r))).comp
    ((ContinuousLinearMap.apply (K p r) ((V × K p r) [×k]→L[K p r] F) ((0 : V), (1 : K p r))).comp
      (continuousMultilinearCurryLeftEquiv (K p r)
        (fun _ : Fin (k+1) => V × K p r) F).toLinearIsometry.toContinuousLinearMap)

@[simp] theorem freezeFirst_apply {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace (K p r) V]
    [NormedAddCommGroup F] [NormedSpace (K p r) F]
    (k : ℕ) (m : (V × K p r) [×(k+1)]→L[K p r] F) (x : Fin k → V) :
    freezeFirst p r k m x = m (Fin.cons (0,1) (fun i => (x i,0))) := rfl

/-- The alternating restriction associated to the actual curry/evaluation map. -/
def restrictSucc (n : ℕ) :
    (D p r (n+1) [⋀^Fin (p+(n+1))]→L[K p r] G p r) →L[K p r]
      (D p r n [⋀^Fin (p+n)]→L[K p r] G p r) :=
  (Round24Transfer.Rmap (K p r) (D p r n) (G p r) (p+n)).comp
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (appendEquiv p r n).toContinuousLinearMap)

@[simp] theorem restrictSucc_apply (n : ℕ)
    (m : D p r (n+1) [⋀^Fin (p+(n+1))]→L[K p r] G p r) (x : Fin (p+n) → D p r n) :
    restrictSucc p r n m x =
      m (fun i => appendEquiv p r n (@Fin.cons (p+n) (fun _ => D p r n × K p r) (0,1) (fun j => (x j,0)) i)) := rfl

/-- Actual local division-free padding, transported to the literal product. -/
def wedgeSucc (n : ℕ) :
    (D p r n [⋀^Fin (p+n)]→L[K p r] G p r) →L[K p r]
      (D p r (n+1) [⋀^Fin (p+(n+1))]→L[K p r] G p r) :=
  (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (appendEquiv p r n).symm.toContinuousLinearMap).comp
    (Round24Transfer.Smap (K p r) (D p r n) (G p r) (p+n))

@[simp] theorem restrictSucc_wedgeSucc (n : ℕ)
    (m : D p r n [⋀^Fin (p+n)]→L[K p r] G p r) :
    restrictSucc p r n (wedgeSucc p r n m) = m := by
  apply ContinuousAlternatingMap.ext
  intro x
  change (Round24Transfer.Smap (K p r) (D p r n) (G p r) (p+n) m)
    (fun i => (appendEquiv p r n).symm (appendEquiv p r n
      (@Fin.cons (p+n) (fun _ => D p r n × K p r) (0,1) (fun j => (x j,0)) i))) = m x
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [Round24Transfer.Smap_apply, Fin.sum_univ_succ]
  simp


/-- Top-degree uniqueness is proved only after extension into the complete Laurent field. -/
theorem alternating_ext_standard (n : ℕ)
    {a b : D p r n [⋀^Fin (p+n)]→L[K p r] G p r}
    (h : a (standardD p r n) = b (standardD p r n)) : a = b := by
  ext x
  rw [alternating_eq_coefficient_mul_det
    (RationalField.denseRange_algebraMap (ZMod p) r)
    (inclusionD p r n) (denseRange_inclusionD p r n) (basis p r n)
    (G p r) (standardD p r n) (inclusionD_standardD p r n) a x,
    alternating_eq_coefficient_mul_det
    (RationalField.denseRange_algebraMap (ZMod p) r)
    (inclusionD p r n) (denseRange_inclusionD p r n) (basis p r n)
    (G p r) (standardD p r n) (inclusionD_standardD p r n) b x, h]

@[simp] theorem standardD_castAdd (n : ℕ) (i : Fin p) :
    standardD p r n (Fin.castAdd n i) = (⟨e p r i, e_mem_D p r i⟩,0) := by
  simp [standardD]

@[simp] theorem standardD_natAdd (n : ℕ) (i : Fin n) :
    standardD p r n (Fin.natAdd p i) = (0,Pi.single i 1) := by
  simp [standardD]

@[simp] theorem appendEquiv_standard (n : ℕ) (i : Fin (p+n)) :
    appendEquiv p r n (standardD p r n i,0) =
      standardD p r (n+1) i.castSucc := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
      simp only [finSumFinEquiv_apply_left, Fin.castSucc_castAdd,
        standardD_castAdd, appendEquiv_apply]
      refine Prod.ext rfl ?_
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
  | inr i =>
      change appendEquiv p r n (standardD p r n (Fin.natAdd p i),0) =
        standardD p r (n+1) (Fin.natAdd p i.castSucc)
      simp only [standardD_natAdd, appendEquiv_apply]
      refine Prod.ext rfl ?_
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Pi.single_apply]

@[simp] theorem appendEquiv_auxiliary (n : ℕ) :
    appendEquiv p r n (0,1) = standardD p r (n+1) (Fin.last (p+n)) := by
  change appendEquiv p r n (0,1) =
    standardD p r (n+1) (Fin.natAdd p (Fin.last n))
  rw [standardD_natAdd]
  refine Prod.ext rfl ?_
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [appendEquiv_apply]

/-- The auxiliary-first convention differs from the manuscript's auxiliary-last
standard basis by the displayed cyclic sign. -/
theorem standard_restrictSucc (n : ℕ)
    (m : D p r (n+1) [⋀^Fin (p+(n+1))]→L[K p r] G p r) :
    m (standardD p r (n+1)) =
      (-1 : ℤˣ) ^ (p+n) • restrictSucc p r n m (standardD p r n) := by
  have hs : standardD p r (n+1) =
      Fin.snoc (fun i => appendEquiv p r n (standardD p r n i,0))
        (appendEquiv p r n (0,1)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hadd : p.add n = p+n := rfl
      simp only [hadd, Fin.snoc, Fin.val_last, lt_self_iff_false, ↓reduceDIte, cast_eq]
      exact (appendEquiv_auxiliary p r n).symm
    · simpa only [Fin.snoc_castSucc] using (appendEquiv_standard p r n j).symm
  rw [hs, Fin.snoc_eq_cons_rotate]
  have hperm := m.toAlternatingMap.map_perm
    (Fin.cons (appendEquiv p r n (0,1))
      (fun i => appendEquiv p r n (standardD p r n i,0))) (finRotate (p+n+1))
  have hsign : Equiv.Perm.sign (finRotate (p+n+1)) = (-1 : ℤˣ) ^ (p+n) := by
    simp
  calc
    _ = Equiv.Perm.sign (finRotate (p+n+1)) •
        m (Fin.cons (appendEquiv p r n (0,1))
          (fun i => appendEquiv p r n (standardD p r n i,0))) := hperm
    _ = (-1 : ℤˣ) ^ (p+n) •
        m (Fin.cons (appendEquiv p r n (0,1))
          (fun i => appendEquiv p r n (standardD p r n i,0))) := by
      exact congrArg (fun a : ℤˣ => a • m (Fin.cons (appendEquiv p r n (0,1))
        (fun i => appendEquiv p r n (standardD p r n i,0)))) hsign
    _ = _ := by
      rw [restrictSucc_apply]
      apply congrArg (fun y : G p r => (-1 : ℤˣ) ^ (p+n) • y)
      apply congrArg m
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- This is the reconstruction direction, proved by dense top-form uniqueness;
`Rmap_Smap` by itself does not imply it. -/
theorem restrictSucc_injective (n : ℕ) : Function.Injective (restrictSucc p r n) := by
  intro a b hab
  apply alternating_ext_standard p r (n+1)
  rw [standard_restrictSucc, standard_restrictSucc, hab]

@[simp] theorem wedgeSucc_restrictSucc (n : ℕ)
    (m : D p r (n+1) [⋀^Fin (p+(n+1))]→L[K p r] G p r) :
    wedgeSucc p r n (restrictSucc p r n m) = m :=
  restrictSucc_injective p r n (restrictSucc_wedgeSucc p r n _)

/-- Freeze all the actual auxiliary standard arguments, in the auxiliary-first
order of the iterated local wedge construction. -/
def freezeAuxiliary : (n : ℕ) →
    (D p r n [×(p+n)]→L[K p r] G p r) →L[K p r]
      (DeterminantPair.D p r [×p]→L[K p r] G p r)
  | 0 => ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => ContinuousLinearMap.inl (K p r) (DeterminantPair.D p r) (Fin 0 → K p r))
  | n+1 => (freezeAuxiliary n).comp ((freezeFirst p r (p+n)).comp
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ => (appendEquiv p r n).toContinuousLinearMap)))

/-- Iterated local `Smap`, with the literal product equivalences at every step. -/
def iteratedWedge : (n : ℕ) →
    (DeterminantPair.D p r [⋀^Fin p]→L[K p r] G p r) →L[K p r]
      (D p r n [⋀^Fin (p+n)]→L[K p r] G p r)
  | 0 => ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.fst (K p r) (DeterminantPair.D p r) (Fin 0 → K p r))
  | n+1 => (wedgeSucc p r n).comp (iteratedWedge n)

/-- The actual bounded retraction: freeze, use the degree-p all-alternating
inverse, and perform the iterated division-free local padding. -/
def paddedRetraction (n : ℕ) :
    (D p r n [×(p+n)]→L[K p r] G p r) →L[K p r]
      (D p r n [⋀^Fin (p+n)]→L[K p r] G p r) :=
  (iteratedWedge p r n).comp
    ((DeterminantPair.retractionR p r).comp (freezeAuxiliary p r n))

@[simp] theorem paddedRetraction_succ (n : ℕ)
    (m : D p r (n+1) [×(p+(n+1))]→L[K p r] G p r) :
    paddedRetraction p r (n+1) m = wedgeSucc p r n
      (paddedRetraction p r n (freezeFirst p r (p+n)
        (m.compContinuousLinearMap fun _ => (appendEquiv p r n).toContinuousLinearMap))) := rfl

/-- It fixes every alternating top form. No surjectivity of the padded
alternating inclusion and no norm-one assertion is used. -/
@[simp] theorem paddedRetraction_fix (n : ℕ)
    (m : D p r n [⋀^Fin (p+n)]→L[K p r] G p r) :
    paddedRetraction p r n m.toContinuousMultilinearMap = m := by
  induction n with
  | zero =>
      apply ContinuousAlternatingMap.ext
      intro x
      change DeterminantPair.retractionR p r
        (m.toContinuousMultilinearMap.compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inl (K p r) (DeterminantPair.D p r) (Fin 0 → K p r)))
        (fun i => (x i).1) = m x
      rw [DeterminantPair.retractionR_apply]
      apply congrArg m
      funext i
      exact Prod.ext rfl (Subsingleton.elim _ _)
  | succ n ih =>
      rw [paddedRetraction_succ]
      have hfreeze : freezeFirst p r (p+n)
          (m.toContinuousMultilinearMap.compContinuousLinearMap
            fun _ => (appendEquiv p r n).toContinuousLinearMap) =
          (restrictSucc p r n m).toContinuousMultilinearMap := rfl
      rw [hfreeze, ih, wedgeSucc_restrictSucc]

/-- The source's actual split certificate for every amount of padding. -/
theorem isSplitAlternatingPair_D (n : ℕ) :
    IsSplitAlternatingPair (K p r) (p+n) (D p r n) (G p r) :=
  ⟨paddedRetraction p r n, paddedRetraction_fix p r n⟩

/-- Global joint self-action analyticity follows from this concrete split retraction. -/
theorem analyticAt_selfActionD (n : ℕ)
    (a : (D p r n →L[K p r] D p r n) × (G p r →L[K p r] G p r)) :
    AnalyticAt (K p r) (alternatingMapAction (K := K p r)
      (E := D p r n) (E' := D p r n) (F := G p r) (F' := G p r) (p+n)) a :=
  analyticAt_alternatingMapAction_of_split_destination (p+n)
    (isSplitAlternatingPair_D p r n) a

/-- The padded split statement, with the actual retraction, its construction and
reconstruction identities, and analytic joint self-action. -/
theorem padded_split_pair (n : ℕ) :
    paddedRetraction p r n = (iteratedWedge p r n).comp
      ((DeterminantPair.retractionR p r).comp (freezeAuxiliary p r n)) ∧
    (∀ m : D p r n [⋀^Fin (p+n)]→L[K p r] G p r,
      paddedRetraction p r n m.toContinuousMultilinearMap = m) ∧
    IsSplitAlternatingPair (K p r) (p+n) (D p r n) (G p r) ∧
    (∀ a : (D p r n →L[K p r] D p r n) × (G p r →L[K p r] G p r),
      AnalyticAt (K p r) (alternatingMapAction (K := K p r)
        (E := D p r n) (E' := D p r n) (F := G p r) (F' := G p r) (p+n)) a) :=
  ⟨rfl, paddedRetraction_fix p r n, isSplitAlternatingPair_D p r n,
    analyticAt_selfActionD p r n⟩

end AlternatingAnalytic.DeterminantPair.Padding
