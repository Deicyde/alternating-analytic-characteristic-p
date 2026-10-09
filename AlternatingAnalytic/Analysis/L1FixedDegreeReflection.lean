import AlternatingAnalytic.Analysis.DenseMultilinearExtension
import AlternatingAnalytic.Analysis.L1AnalyticFactorization
import AlternatingAnalytic.Analysis.L1PolynomialLift
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Within

/-!
# Fixed-degree reflection along ℓ¹ families

Theorem 4.5(2): if `a : H → W` has a bounded homogeneous polynomial representative of
fixed degree `d` with values in a Banach space `Z ⊇ W` (closed), then `a ∘ γ` is analytic
for every analytic `γ` on an open subset of ℓ¹(I, K). The proof extends the multilinear
map to the completion of `H`, lifts it after a bounded linear map from ℓ¹, and uses the
local factorization of `γ` through ℓ¹ words. Neither `K` nor `H` need be complete.
-/

open scoped lp
open Filter Topology
open L1Coordinates (L1)

noncomputable section

namespace AlternatingAnalytic

variable {K I J H Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup H] [NormedSpace K H]
  [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- The norm-nonincreasing extension of a multilinear map to the completion of `H`. -/
def completionMultilinear (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z) :
    ContinuousMultilinearMap K (fun _ : Fin d => UniformSpace.Completion H) Z :=
  denseMultilinearExtension
    (UniformSpace.Completion.toComplₗᵢ : H →ₗᵢ[K] UniformSpace.Completion H)
    UniformSpace.Completion.denseRange_coe d B

@[simp]
theorem completionMultilinear_apply (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z) (v : Fin d → H) :
    completionMultilinear d B (fun i => (v i : UniformSpace.Completion H)) = B v :=
  denseMultilinearExtension_apply
    (UniformSpace.Completion.toComplₗᵢ : H →ₗᵢ[K] UniformSpace.Completion H)
    UniformSpace.Completion.denseRange_coe d B v

theorem norm_completionMultilinear_le (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z) :
    ‖completionMultilinear d B‖ ≤ ‖B‖ :=
  norm_denseMultilinearExtension_le
    (UniformSpace.Completion.toComplₗᵢ : H →ₗᵢ[K] UniformSpace.Completion H)
    UniformSpace.Completion.denseRange_coe d B

/-- The completed diagonal stays in the closed submodule `W`. -/
theorem completionMultilinear_diagonal_mem
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    (z : UniformSpace.Completion H) : completionMultilinear d B (fun _ => z) ∈ W := by
  refine UniformSpace.Completion.induction_on z
    (hW.preimage ((completionMultilinear d B).cont.comp
      (continuous_pi fun _ => continuous_id))) ?_
  intro h
  rw [completionMultilinear_apply, ← hP]
  exact (P h).property

/-- The diagonal of the completed multilinear map, as a map into `W`. -/
def completionDiagonal
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h)) :
    UniformSpace.Completion H → W :=
  fun z => ⟨completionMultilinear d B (fun _ => z),
    completionMultilinear_diagonal_mem W hW d B P hP z⟩

@[simp]
theorem coe_completionDiagonal
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    (z : UniformSpace.Completion H) :
    (completionDiagonal W hW d B P hP z : Z) =
      completionMultilinear d B (fun _ => z) := rfl

@[simp]
theorem completionDiagonal_coe
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h)) (h : H) :
    completionDiagonal W hW d B P hP (h : UniformSpace.Completion H) = P h := by
  apply Subtype.ext
  exact (completionMultilinear_apply d B (fun _ => h)).trans (hP h).symm

/-- After a bounded linear map `T` from ℓ¹, the completed diagonal has a `W`-valued
multilinear representative of norm at most `d! * ‖B‖ * ‖T‖ ^ d`. -/
theorem exists_l1_completion_diagonal_lift
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    (T : L1 K J →L[K] UniformSpace.Completion H) :
    ∃ C : ContinuousMultilinearMap K (fun _ : Fin d => L1 K J) W,
      (∀ y, C (fun _ => y) = completionDiagonal W hW d B P hP (T y)) ∧
      ‖C‖ ≤ (d.factorial : ℝ) * ‖B‖ * ‖T‖ ^ d := by
  let D := (completionMultilinear d B).compContinuousLinearMap (fun _ => T)
  obtain ⟨C, hC, hnorm⟩ := L1PolynomialLift.exists_l1_diagonal_lift W hW d D
    (fun y => completionMultilinear_diagonal_mem W hW d B P hP (T y))
  refine ⟨C, fun y => Subtype.ext (hC y), hnorm.trans ?_⟩
  have hD : ‖D‖ ≤ ‖B‖ * ‖T‖ ^ d := by
    calc
      ‖D‖ ≤ ‖completionMultilinear d B‖ * ‖T‖ ^ d := by
        simpa using (completionMultilinear d B).norm_compContinuousLinearMap_le
          (fun _ : Fin d => T)
      _ ≤ ‖B‖ * ‖T‖ ^ d :=
        mul_le_mul_of_nonneg_right (norm_completionMultilinear_le d B) (by positivity)
  calc
    (d.factorial : ℝ) * ‖D‖ ≤ (d.factorial : ℝ) * (‖B‖ * ‖T‖ ^ d) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (d.factorial : ℝ) * ‖B‖ * ‖T‖ ^ d := (mul_assoc _ _ _).symm

/-- After a bounded linear map from ℓ¹, the completed diagonal is polynomial. -/
theorem cpolynomialAt_completionDiagonal_comp
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    (T : L1 K J →L[K] UniformSpace.Completion H) (x : L1 K J) :
    CPolynomialAt K (completionDiagonal W hW d B P hP ∘ T) x := by
  obtain ⟨C, hC, _⟩ := exists_l1_completion_diagonal_lift W hW d B P hP T
  let Δ : L1 K J →L[K] (Fin d → L1 K J) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id K _
  have hdiag : CPolynomialAt K (fun y => C (fun _ => y)) x :=
    C.cpolynomialAt.comp (f := Δ) (Δ.cpolynomialAt x)
  exact hdiag.congr (Filter.Eventually.of_forall hC)

/-- Fixed-degree reflection at a point of ℓ¹. -/
theorem analyticAt_comp_of_l1_fixed_degree
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    {γ : L1 K I → H} {x : L1 K I} (hγ : AnalyticAt K γ x) :
    AnalyticAt K (P ∘ γ) x := by
  obtain ⟨T, g, hg, hTg⟩ := L1Coordinates.exists_analyticAt_l1_factorization hγ
  apply ((cpolynomialAt_completionDiagonal_comp W hW d B P hP T (g x)).analyticAt.comp hg).congr
  filter_upwards [hTg] with y hy
  change completionDiagonal W hW d B P hP (T (g y)) = P (γ y)
  rw [hy, completionDiagonal_coe]

/-- Neighborhood version of `analyticAt_comp_of_l1_fixed_degree`. -/
theorem analyticOnNhd_comp_of_l1_fixed_degree
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    {γ : L1 K I → H} {U : Set (L1 K I)} (hγ : AnalyticOnNhd K γ U) :
    AnalyticOnNhd K (P ∘ γ) U :=
  fun x hx => analyticAt_comp_of_l1_fixed_degree W hW d B P hP (hγ x hx)

/-- Theorem 4.5(2) for a closed submodule, on an open subset of ℓ¹. -/
theorem analyticOn_comp_of_l1_fixed_degree
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    {γ : L1 K I → H} {U : Set (L1 K I)}
    (hU : IsOpen U) (hγ : AnalyticOn K γ U) : AnalyticOn K (P ∘ γ) U :=
  (analyticOnNhd_comp_of_l1_fixed_degree W hW d B P hP
    (hU.analyticOn_iff_analyticOnNhd.mp hγ)).analyticOn

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]

/-- Fixed-degree reflection through a linear isometry with closed range. -/
theorem analyticAt_comp_of_l1_fixed_degree_isometry
    (j : V →ₗᵢ[K] Z) (hj : IsClosed (Set.range j)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → V) (hP : ∀ h, j (P h) = B (fun _ => h))
    {γ : L1 K I → H} {x : L1 K I} (hγ : AnalyticAt K γ x) :
    AnalyticAt K (P ∘ γ) x := by
  have ha : AnalyticAt K ((fun h => j.equivRange (P h)) ∘ γ) x :=
    analyticAt_comp_of_l1_fixed_degree j.toLinearMap.range hj d B
      (fun h => j.equivRange (P h)) hP hγ
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using
    (j.equivRange.symm.analyticAt (j.equivRange (P (γ x)))).comp
      (f := (fun h => j.equivRange (P h)) ∘ γ) ha

/-- Neighborhood version of `analyticAt_comp_of_l1_fixed_degree_isometry`. -/
theorem analyticOnNhd_comp_of_l1_fixed_degree_isometry
    (j : V →ₗᵢ[K] Z) (hj : IsClosed (Set.range j)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → V) (hP : ∀ h, j (P h) = B (fun _ => h))
    {γ : L1 K I → H} {U : Set (L1 K I)} (hγ : AnalyticOnNhd K γ U) :
    AnalyticOnNhd K (P ∘ γ) U :=
  fun x hx => analyticAt_comp_of_l1_fixed_degree_isometry j hj d B P hP (hγ x hx)

/-- Theorem 4.5(2) for a linear isometry with closed range, on an open subset of ℓ¹. -/
theorem analyticOn_comp_of_l1_fixed_degree_isometry
    (j : V →ₗᵢ[K] Z) (hj : IsClosed (Set.range j)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → V) (hP : ∀ h, j (P h) = B (fun _ => h))
    {γ : L1 K I → H} {U : Set (L1 K I)}
    (hU : IsOpen U) (hγ : AnalyticOn K γ U) : AnalyticOn K (P ∘ γ) U :=
  (analyticOnNhd_comp_of_l1_fixed_degree_isometry j hj d B P hP
    (hU.analyticOn_iff_analyticOnNhd.mp hγ)).analyticOn

end AlternatingAnalytic
