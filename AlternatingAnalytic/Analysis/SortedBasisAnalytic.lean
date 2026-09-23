import AlternatingAnalytic.Analysis.SortedBasisRetraction
import AlternatingAnalytic.Analysis.SortedBasisLift
import AlternatingAnalytic.Analysis.DenseMultilinearExtension

/-! The sorted lift for an arbitrary orthogonal unconditional Schauder basis.
The ambient source need not be complete and the basis index may be uncountable. -/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

variable {K I E E' F : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [LinearOrder I] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [CompleteSpace F]

/-- Sort on the finite coordinate span, then extend along its dense isometric inclusion. -/
def sortedSchauderRetraction (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) :
    (E [×n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F) :=
  (denseAlternatingExtension (Submodule.span K (Set.range b)).subtypeₗᵢ
    (schauderSpan_denseRange b) n).comp
    ((sortedBasisRetraction (Basis.span b.linearIndependent) (schauderSpanBasis_bound b hb) n).comp
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin n => (Submodule.span K (Set.range b)).subtypeL)))

theorem norm_sortedSchauderRetraction_le (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) :
    ‖sortedSchauderRetraction (F := F) b hb n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  rw [one_mul]
  change ‖denseAlternatingExtension (Submodule.span K (Set.range b)).subtypeₗᵢ
    (schauderSpan_denseRange b) n
    (sortedBasisRetraction (Basis.span b.linearIndependent) (schauderSpanBasis_bound b hb) n
      (g.compContinuousLinearMap (fun _ => (Submodule.span K (Set.range b)).subtypeL)))‖ ≤ ‖g‖
  apply (norm_denseAlternatingExtension_le _ _ _ _).trans
  apply (ContinuousLinearMap.le_of_opNorm_le _
    (norm_sortedBasisRetraction_le (Basis.span b.linearIndependent)
      (schauderSpanBasis_bound b hb) n) _).trans
  simpa only [one_mul, Submodule.subtypeₗᵢ_toContinuousLinearMap] using
    g.norm_compContinuous_linearIsometry_le
    (fun _ : Fin n => (Submodule.span K (Set.range b)).subtypeₗᵢ)

theorem sortedSchauderRetraction_span_apply (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → Submodule.span K (Set.range b)) :
    sortedSchauderRetraction b hb n g (fun i => x i) =
      sortedAlternatingMap (Basis.span b.linearIndependent) n
        (g.compContinuousLinearMap (fun _ => (Submodule.span K (Set.range b)).subtypeL)) x := by
  exact denseAlternatingExtension_apply _ _ _ _ _

theorem sortedSchauderRetraction_basis (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (g : E [×n]→L[K] F) (s : Set.powersetCard I n) :
    sortedSchauderRetraction b hb n g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) =
      g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
  let x := (Basis.span b.linearIndependent) ∘ Set.powersetCard.ofFinEmbEquiv.symm s
  have hx : (fun i => (x i : E)) = b ∘ Set.powersetCard.ofFinEmbEquiv.symm s := by
    ext i
    exact Basis.coe_span_apply _ _
  rw [← hx, sortedSchauderRetraction_span_apply]
  exact sortedAlternatingMap_basis _ _ _ _

theorem sortedSchauderRetraction_retract (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (g : E [⋀^Fin n]→L[K] F) :
    sortedSchauderRetraction b hb n g.toContinuousMultilinearMap = g := by
  ext v
  have heq := (DenseRange.piMap (fun _ : Fin n => schauderSpan_denseRange b)).equalizer
    (sortedSchauderRetraction b hb n g.toContinuousMultilinearMap).cont g.cont
  refine congrFun (heq ?_) v
  funext x
  change sortedSchauderRetraction b hb n g.toContinuousMultilinearMap (fun i => (x i : E)) =
    g (fun i => (x i : E))
  rw [sortedSchauderRetraction_span_apply]
  exact DFunLike.congr_fun
    (sortedAlternatingMap_retract (Basis.span b.linearIndependent) n
      (g.compContinuousLinearMap (Submodule.span K (Set.range b)).subtypeL)) x

/-- The actual sorted multilinear lift on the original topological source. -/
def sortedSchauderLift (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) :
    (E →L[K] E') [×n]→L[K]
      ((E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) :=
  contractingRetractionLift n (sortedSchauderRetraction b hb n)

theorem sortedSchauderLift_apply (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (f : Fin n → E →L[K] E') (m : E' [⋀^Fin n]→L[K] F) :
    sortedSchauderLift b hb n f m =
      sortedSchauderRetraction b hb n
        (m.toContinuousMultilinearMap.compContinuousLinearMap f) := rfl

theorem sortedSchauderLift_basis (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (f : Fin n → E →L[K] E') (m : E' [⋀^Fin n]→L[K] F) (s : Set.powersetCard I n) :
    sortedSchauderLift b hb n f m (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) =
      m (fun i => f i (b (Set.powersetCard.ofFinEmbEquiv.symm s i))) := by
  rw [sortedSchauderLift_apply, sortedSchauderRetraction_basis]
  rfl

noncomputable local instance sortedSchauderLiftNorm (n : ℕ) :
    Norm ((E →L[K] E') [×n]→L[K]
      ((E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin n => E →L[K] E')
    (G := (E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))

theorem norm_sortedSchauderLift_le (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) :
    ‖sortedSchauderLift (E' := E') (F := F) b hb n‖ ≤ 1 :=
  norm_contractingRetractionLift_le n _ (norm_sortedSchauderRetraction_le b hb n)

theorem sortedSchauderLift_diag (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) (f : E →L[K] E') :
    sortedSchauderLift (F := F) b hb n (fun _ => f) =
      Round24Transfer.Q K (Fin n) E E' F f :=
  contractingRetractionLift_diag n _ (sortedSchauderRetraction_retract b hb n) f

theorem cpolynomialAt_of_orthogonalSchauderBasis (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) (f : E →L[K] E') :
    CPolynomialAt K (Round24Transfer.Q K (Fin n) E E' F) f := by
  exact Round24Transfer.cpolynomialAt_of_lift (sortedSchauderLift b hb n)
    (sortedSchauderLift_diag b hb n) f

theorem analyticAt_of_orthogonalSchauderBasis (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) (f : E →L[K] E') :
    AnalyticAt K (Round24Transfer.Q K (Fin n) E E' F) f :=
  (cpolynomialAt_of_orthogonalSchauderBasis b hb n f).analyticAt

/-- The bounded-lift conclusion for any finite indexing type. -/
theorem hasBoundedLift_of_orthogonalSchauderBasis {ι : Type*} [Fintype ι]
    (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) :
    Round24Transfer.HasBoundedLift K ι E E' F := by
  apply Round24Transfer.hasBoundedLift_reindex (Fintype.equivFin ι).symm
  exact Round24Transfer.hasBoundedLift_of_analyticAt
    (analyticAt_of_orthogonalSchauderBasis b hb (Fintype.card ι) (0 : E →L[K] E'))

theorem cpolynomialAt_of_orthogonalSchauderBasis_fintype {ι : Type*} [Fintype ι]
    (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (f : E →L[K] E') :
    CPolynomialAt K (Round24Transfer.Q K ι E E' F) f := by
  obtain ⟨P, hP⟩ := hasBoundedLift_of_orthogonalSchauderBasis
    (ι := ι) (E' := E') (F := F) b hb
  exact Round24Transfer.cpolynomialAt_of_lift P hP f

theorem analyticAt_of_orthogonalSchauderBasis_fintype {ι : Type*} [Fintype ι]
    (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (f : E →L[K] E') :
    AnalyticAt K (Round24Transfer.Q K ι E E' F) f :=
  (cpolynomialAt_of_orthogonalSchauderBasis_fintype b hb f).analyticAt

end AlternatingAnalytic
