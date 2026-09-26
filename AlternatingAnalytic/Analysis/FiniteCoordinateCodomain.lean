import AlternatingAnalytic.Analysis.FiniteCoordinateCodomainAlgebra
import AlternatingAnalytic.Analysis.FiniteCoordinateCodomainBounds
import AlternatingAnalytic.Analysis.FiniteCoordinateExpansion

/-!
# Finite coordinate bases in the codomain

The codomain-coordinate construction of `charp.tex`, Proposition
`prop:finite-coordinate`. Every row retains its own operator argument.
The ordinary real norm estimate and exterior-basis expansion require no
completeness, ultrametricity, or characteristic restriction.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  {d : ℕ}

private theorem codomain_algebra_bound (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    ‖finiteCoordinateCodomainAlgebra b k f m x‖ ≤
      (finiteCoordinateCodomainBound b hb k * ∏ a, ‖f a‖) * ‖m‖ * ∏ j, ‖x j‖ := by
  rw [finiteCoordinateCodomainAlgebra_apply]
  calc
    _ ≤ finiteCoordinateCodomainBound b hb k * ‖m‖ *
        (∏ a, ‖f a‖) * ∏ j, ‖x j‖ :=
      norm_finiteCoordinateCodomain_sum_le b hb k f m x
    _ = _ := by ring

/-- The bounded operator supplied by a fixed tuple of operator arguments. -/
def finiteCoordinateCodomainOperator (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f : Fin k → E →L[K] E') :
    (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F) :=
  AlternatingMap.mkContinuousLinear (finiteCoordinateCodomainAlgebra b k f)
    (finiteCoordinateCodomainBound b hb k * ∏ a, ‖f a‖)
    (codomain_algebra_bound b hb k f)

private def codomainMultilinear (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    MultilinearMap K (fun _ : Fin k => E →L[K] E')
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) where
  toFun := finiteCoordinateCodomainOperator b hb k
  map_update_add' f i u v := by
    ext m x
    change finiteCoordinateCodomainAlgebra b k (Function.update f i (u + v)) m x =
      finiteCoordinateCodomainAlgebra b k (Function.update f i u) m x +
      finiteCoordinateCodomainAlgebra b k (Function.update f i v) m x
    rw [MultilinearMap.map_update_add]
    rfl
  map_update_smul' f i c u := by
    ext m x
    change finiteCoordinateCodomainAlgebra b k (Function.update f i (c • u)) m x =
      c • finiteCoordinateCodomainAlgebra b k (Function.update f i u) m x
    rw [MultilinearMap.map_update_smul]
    rfl

private theorem codomainMultilinear_bound (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f : Fin k → E →L[K] E') :
    ‖codomainMultilinear (F := F) b hb k f‖ ≤
      finiteCoordinateCodomainBound b hb k * ∏ a, ‖f a‖ := by
  apply AlternatingMap.mkContinuousLinear_norm_le
  exact mul_nonneg (finiteCoordinateCodomainBound_nonneg b hb k)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- The bounded codomain-coordinate lift in every degree, including degree zero. -/
def finiteCoordinateCodomainLift (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    (E →L[K] E') [×k]→L[K]
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) :=
  MultilinearMap.mkContinuous
    (𝕜 := K) (E := fun _ : Fin k => E →L[K] E')
    (G := (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))
    (codomainMultilinear b hb k) (finiteCoordinateCodomainBound b hb k)
    (codomainMultilinear_bound b hb k)

theorem finiteCoordinateCodomainLift_apply (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    finiteCoordinateCodomainLift b hb k f m x =
      ∑ s : Set.powersetCard (Fin d) k,
        (Matrix.of fun a j => finiteCoordinateCodomainFunctional b hb
          (Set.powersetCard.ofFinEmbEquiv.symm s a) (f a (x j))).det •
          m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a)) :=
  finiteCoordinateCodomainAlgebra_apply b k f m x

/-- Separate additivity in each operator, before restriction to the diagonal. -/
theorem finiteCoordinateCodomainLift_update_add (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (i : Fin k) (u v : E →L[K] E') :
    finiteCoordinateCodomainLift (F := F) b hb k (Function.update f i (u + v)) =
      finiteCoordinateCodomainLift b hb k (Function.update f i u) +
      finiteCoordinateCodomainLift b hb k (Function.update f i v) :=
  (finiteCoordinateCodomainLift b hb k).map_update_add f i u v

/-- Separate homogeneity in each operator, over the original field. -/
theorem finiteCoordinateCodomainLift_update_smul (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (i : Fin k) (c : K) (u : E →L[K] E') :
    finiteCoordinateCodomainLift (F := F) b hb k (Function.update f i (c • u)) =
      c • finiteCoordinateCodomainLift b hb k (Function.update f i u) :=
  (finiteCoordinateCodomainLift b hb k).map_update_smul f i c u

/-- Equal columns give zero, also in characteristic two. -/
theorem finiteCoordinateCodomainLift_eq_zero_of_eq (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F)
    (x : Fin k → E) {i j : Fin k} (h : x i = x j) (hij : i ≠ j) :
    finiteCoordinateCodomainLift b hb k f m x = 0 :=
  (finiteCoordinateCodomainLift b hb k f m).map_eq_zero_of_eq x h hij

theorem norm_finiteCoordinateCodomainLift_apply_le (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    ‖finiteCoordinateCodomainLift b hb k f m x‖ ≤
      finiteCoordinateCodomainBound b hb k * ‖m‖ * (∏ a, ‖f a‖) * ∏ j, ‖x j‖ := by
  rw [finiteCoordinateCodomainLift_apply]
  exact norm_finiteCoordinateCodomain_sum_le b hb k f m x

noncomputable local instance finiteCoordinateCodomainLiftNorm (k : ℕ) :
    Norm ((E →L[K] E') [×k]→L[K]
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin k => E →L[K] E')
    (G := (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))

theorem norm_finiteCoordinateCodomainLift_le (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    ‖finiteCoordinateCodomainLift (E := E) (F := F) b hb k‖ ≤
      finiteCoordinateCodomainBound b hb k :=
  MultilinearMap.mkContinuous_norm_le _ (finiteCoordinateCodomainBound_nonneg b hb k) _

/-- Exterior-basis expansion proves the diagonal identity. -/
theorem finiteCoordinateCodomainLift_diag (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f : E →L[K] E') :
    finiteCoordinateCodomainLift (F := F) b hb k (fun _ => f) =
      Round24Transfer.Q K (Fin k) E E' F f := by
  ext m x
  rw [finiteCoordinateCodomainLift_apply]
  exact finiteCoordinate_expansion b k m (fun j => f (x j))

theorem hasBoundedLift_of_finiteCoordinateCodomain (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    Round24Transfer.HasBoundedLift K (Fin k) E E' F := by
  rw [Round24Transfer.HasBoundedLift, Fintype.card_fin]
  exact ⟨finiteCoordinateCodomainLift b hb k, finiteCoordinateCodomainLift_diag b hb k⟩

theorem cpolynomialAt_Q_of_finiteCoordinateCodomain (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f₀ : E →L[K] E') :
    CPolynomialAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ :=
  Round24Transfer.cpolynomialAt_of_lift (finiteCoordinateCodomainLift b hb k)
    (finiteCoordinateCodomainLift_diag b hb k) f₀

theorem analyticAt_Q_of_finiteCoordinateCodomain (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f₀ : E →L[K] E') :
    AnalyticAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ :=
  (cpolynomialAt_Q_of_finiteCoordinateCodomain b hb k f₀).analyticAt

/-- Above the basis dimension the increasing-tuple sum is empty. -/
theorem finiteCoordinateCodomainLift_eq_zero_of_lt (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) :
    finiteCoordinateCodomainLift (E := E) (F := F) b hb k = 0 := by
  let := finiteCoordinateCodomainIndices_isEmpty h
  ext f m x
  simp [finiteCoordinateCodomainLift_apply]

theorem Q_eq_zero_of_finiteCoordinateCodomain_lt (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) (f : E →L[K] E') :
    Round24Transfer.Q K (Fin k) E E' F f = 0 := by
  rw [← finiteCoordinateCodomainLift_diag b hb k f,
    finiteCoordinateCodomainLift_eq_zero_of_lt b hb h]
  rfl

/-- The degree-zero lift retains the value of the empty tuple. -/
theorem finiteCoordinateCodomainLift_zero_apply (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (f : Fin 0 → E →L[K] E')
    (m : E' [⋀^Fin 0]→L[K] F) (x : Fin 0 → E) :
    finiteCoordinateCodomainLift b hb 0 f m x = m (fun i => Fin.elim0 i) := by
  let : Unique (Set.powersetCard (Fin d) 0) :=
    ⟨⟨∅, rfl⟩, fun s => Subtype.ext (Finset.card_eq_zero.mp s.prop)⟩
  rw [finiteCoordinateCodomainLift_apply, Fintype.sum_unique, Matrix.det_isEmpty, one_smul]
  exact congrArg m (Subsingleton.elim _ _)

theorem Q_zero_constant_of_finiteCoordinateCodomain (f g : E →L[K] E') :
    Round24Transfer.Q K (Fin 0) E E' F f =
      Round24Transfer.Q K (Fin 0) E E' F g := by
  ext m x
  exact congrArg m (Subsingleton.elim _ _)

/-- Alternating forms on the codomain vanish above its coordinate dimension. -/
theorem alternatingMap_eq_zero_of_finiteCoordinateCodomain_lt
    (b : Basis (Fin d) K E') {k : ℕ} (h : d < k)
    (m : E' [⋀^Fin k]→L[K] F) : m = 0 := by
  let := finiteCoordinateCodomainIndices_isEmpty h
  ext y
  rw [← finiteCoordinate_expansion b k m y]
  simp

/-- The codomain-coordinate case of `prop:finite-coordinate`, collected with
the actual lift, its determinant formula, separate linearity, strong alternation,
both norm bounds, diagonal identity, analytic conclusions, and boundary cases. -/
theorem finiteCoordinateCodomain (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    let C := finiteCoordinateCodomainBound b hb k
    let P := finiteCoordinateCodomainLift (E := E) (F := F) b hb k
    0 ≤ C ∧
    (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E),
      P f m x = ∑ s : Set.powersetCard (Fin d) k,
        (Matrix.of fun a j => finiteCoordinateCodomainFunctional b hb
          (Set.powersetCard.ofFinEmbEquiv.symm s a) (f a (x j))).det •
          m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))) ∧
    (∀ (f : Fin k → E →L[K] E') (i : Fin k) (u v : E →L[K] E'),
      P (Function.update f i (u + v)) =
        P (Function.update f i u) + P (Function.update f i v)) ∧
    (∀ (f : Fin k → E →L[K] E') (i : Fin k) (c : K) (u : E →L[K] E'),
      P (Function.update f i (c • u)) = c • P (Function.update f i u)) ∧
    (∀ (f : Fin k → E →L[K] E') (m n : E' [⋀^Fin k]→L[K] F),
      P f (m + n) = P f m + P f n) ∧
    (∀ (f : Fin k → E →L[K] E') (c : K) (m : E' [⋀^Fin k]→L[K] F),
      P f (c • m) = c • P f m) ∧
    (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F)
      (x : Fin k → E) (i : Fin k) (u v : E),
      P f m (Function.update x i (u + v)) =
        P f m (Function.update x i u) + P f m (Function.update x i v)) ∧
    (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F)
      (x : Fin k → E) (i : Fin k) (c : K) (u : E),
      P f m (Function.update x i (c • u)) = c • P f m (Function.update x i u)) ∧
    (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F)
      (x : Fin k → E) (i j : Fin k), x i = x j → i ≠ j → P f m x = 0) ∧
    (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E),
      ‖P f m x‖ ≤ C * ‖m‖ * (∏ a, ‖f a‖) * ∏ j, ‖x j‖) ∧
    ‖P‖ ≤ C ∧
    (∀ f : E →L[K] E', P (fun _ => f) = Round24Transfer.Q K (Fin k) E E' F f) ∧
    Round24Transfer.HasBoundedLift K (Fin k) E E' F ∧
    (∀ f₀ : E →L[K] E', CPolynomialAt K (Round24Transfer.Q K (Fin k) E E' F) f₀) ∧
    (∀ f₀ : E →L[K] E', AnalyticAt K (Round24Transfer.Q K (Fin k) E E' F) f₀) ∧
    (d < k → C = 0 ∧ P = 0 ∧
      (∀ m : E' [⋀^Fin k]→L[K] F, m = 0) ∧
      ∀ f : E →L[K] E', Round24Transfer.Q K (Fin k) E E' F f = 0) ∧
    (k = 0 → C = 1 ∧
      (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F)
        (x : Fin k → E) (y : Fin k → E'), P f m x = m y) ∧
      ∀ f g : E →L[K] E', Round24Transfer.Q K (Fin k) E E' F f =
        Round24Transfer.Q K (Fin k) E E' F g) := by
  dsimp only
  refine ⟨finiteCoordinateCodomainBound_nonneg b hb k,
    finiteCoordinateCodomainLift_apply b hb k,
    finiteCoordinateCodomainLift_update_add b hb k,
    finiteCoordinateCodomainLift_update_smul b hb k,
    (fun f m n => (finiteCoordinateCodomainLift b hb k f).map_add m n),
    (fun f c m => (finiteCoordinateCodomainLift b hb k f).map_smul c m),
    (fun f m x i u v => (finiteCoordinateCodomainLift b hb k f m).map_update_add x i u v),
    (fun f m x i c u => (finiteCoordinateCodomainLift b hb k f m).map_update_smul x i c u),
    (fun f m x i j h hij => finiteCoordinateCodomainLift_eq_zero_of_eq b hb k f m x h hij),
    norm_finiteCoordinateCodomainLift_apply_le b hb k,
    norm_finiteCoordinateCodomainLift_le b hb k,
    finiteCoordinateCodomainLift_diag b hb k,
    hasBoundedLift_of_finiteCoordinateCodomain b hb k,
    cpolynomialAt_Q_of_finiteCoordinateCodomain b hb k,
    analyticAt_Q_of_finiteCoordinateCodomain b hb k, ?_, ?_⟩
  · intro h
    exact ⟨finiteCoordinateCodomainBound_eq_zero_of_lt b hb h,
      finiteCoordinateCodomainLift_eq_zero_of_lt b hb h,
      alternatingMap_eq_zero_of_finiteCoordinateCodomain_lt b h,
      Q_eq_zero_of_finiteCoordinateCodomain_lt b hb h⟩
  · rintro rfl
    refine ⟨finiteCoordinateCodomainBound_zero b hb, ?_,
      Q_zero_constant_of_finiteCoordinateCodomain⟩
    intro f m x y
    rw [finiteCoordinateCodomainLift_zero_apply]
    exact congrArg m (Subsingleton.elim _ _)

end AlternatingAnalytic
