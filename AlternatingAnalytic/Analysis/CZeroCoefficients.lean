import AlternatingAnalytic.Algebra.FiniteWordGrouping
import AlternatingAnalytic.Analysis.CZeroCoordinates

/-!
# Homogeneous diagonal lifting on discrete c₀

The distinct-word orbit coefficients from `FiniteWord` belong to the submodule
containing the full diagonal. Their nonarchimedean bound defines a continuous
multilinear map by the bounded-array construction. Finite diagonal regrouping
and convergence of finite truncations identify its diagonal with the original.

The index type and degree are arbitrary, including an empty index type and degree
zero. Only the submodule is complete; neither the scalar field nor the ambient
target needs to be complete.
-/

noncomputable section

open scoped Topology ZeroAtInfty BigOperators
open Filter

namespace CZero

variable {I K Z : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NontriviallyNormedField K] [NormedAddCommGroup Z] [NormedSpace K Z]
  [IsUltrametricDist Z] {n : ℕ}

/-- Grouping distinct coordinate words preserves the operator-norm bound. -/
theorem norm_groupedCoefficient_le
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (a : Fin n → I) :
    ‖FiniteWord.groupedCoefficient p.toMultilinearMap (coordinate (K := K)) a‖ ≤ ‖p‖ := by
  classical
  by_cases ha : FiniteWord.wordRepresentative a = a
  · rw [FiniteWord.groupedCoefficient_of_representative _ _ ha]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg p)
    intro u hu
    apply p.unit_le_opNorm
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun r => norm_coordinate_le (u r))
  · rw [FiniteWord.groupedCoefficient_of_not_representative _ _ ha, norm_zero]
    exact norm_nonneg p

/-- The actual grouped coefficient, valued in the submodule containing the diagonal. -/
def groupedCoefficientInSubmodule (W : Submodule K Z)
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (a : Fin n → I) : W :=
  ⟨FiniteWord.groupedCoefficient p.toMultilinearMap (coordinate (K := K)) a,
    FiniteWord.groupedCoefficient_mem W p.toMultilinearMap (coordinate (K := K)) hp a⟩

omit [IsUltrametricDist Z] in
@[simp]
theorem coe_groupedCoefficientInSubmodule (W : Submodule K Z)
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (a : Fin n → I) :
    (groupedCoefficientInSubmodule W p hp a : Z) =
      FiniteWord.groupedCoefficient p.toMultilinearMap (coordinate (K := K)) a := rfl

/-- The submodule norm is the ambient norm, so the same sharp bound applies. -/
theorem norm_groupedCoefficientInSubmodule_le (W : Submodule K Z)
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (a : Fin n → I) :
    ‖groupedCoefficientInSubmodule W p hp a‖ ≤ ‖p‖ :=
  norm_groupedCoefficient_le p a

variable (W : Submodule K Z) [CompleteSpace W]

/-- Lift a homogeneous diagonal using the bounded array of grouped coefficients. -/
def homogeneousLift
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) :
    ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) W :=
  boundedArrayMultilinearMap (groupedCoefficientInSubmodule W p hp) ‖p‖ (norm_nonneg p)
    (norm_groupedCoefficientInSubmodule_le W p hp)

@[simp]
theorem homogeneousLift_apply
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (x : Fin n → C₀(I, K)) :
    homogeneousLift W p hp x =
      ∑' a, (∏ r, x r (a r)) • groupedCoefficientInSubmodule W p hp a := rfl

/-- The lift has no larger operator norm than the original map. -/
theorem norm_homogeneousLift_le
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) : ‖homogeneousLift W p hp‖ ≤ ‖p‖ :=
  norm_boundedArrayMultilinearMap_le _ _ _ _

/-- Evaluation on coordinate tuples recovers the actual grouped coefficient array. -/
@[simp]
theorem homogeneousLift_coordinate
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (a : Fin n → I) :
    homogeneousLift W p hp (fun r => coordinate (K := K) (a r)) =
      groupedCoefficientInSubmodule W p hp a :=
  boundedArrayMultilinearMap_coordinate _ _ _ _ a

/-- The shared finite regrouping identity identifies the diagonals on truncations. -/
theorem homogeneousLift_diagonal_truncation
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (s : Finset I) (x : C₀(I, K)) :
    (homogeneousLift W p hp (fun _ => truncation s x) : Z) =
      p (fun _ => truncation s x) := by
  classical
  let q := homogeneousLift W p hp
  have hq (a : Fin n → I) :
      (q (fun r => coordinate (K := K) (a r)) : Z) =
        FiniteWord.groupedCoefficient p.toMultilinearMap (coordinate (K := K)) a := by
    simp only [q, homogeneousLift_coordinate, coe_groupedCoefficientInSubmodule]
  have ht : truncation s x = ∑ i : s, x i • coordinate (K := K) (i : I) := by
    rw [truncation_eq_sum]
    exact (Finset.sum_attach s (fun i => x i • coordinate (K := K) i)).symm
  have h := FiniteWord.finite_diagonal_grouping p.toMultilinearMap
    (coordinate (K := K)) s x
  change (q.toMultilinearMap (fun _ => truncation s x) : Z) = _
  rw [ht, q.toMultilinearMap.map_sum
    (fun (_ : Fin n) (j : s) => x j • coordinate (K := K) (j : I))]
  simp only [Submodule.coe_sum, q.toMultilinearMap.map_smul_univ, Submodule.coe_smul,
    ContinuousMultilinearMap.coe_coe, hq]
  rw [← truncation_eq_sum, ht] at h
  simpa only [ContinuousMultilinearMap.coe_coe] using h.symm

/-- Continuity extends finite diagonal regrouping to every vector of c₀. -/
theorem homogeneousLift_diagonal
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (x : C₀(I, K)) :
    (homogeneousLift W p hp (fun _ => x) : Z) = p (fun _ => x) := by
  have ht : Tendsto (fun s : Finset I => fun _ : Fin n => truncation s x)
      atTop (𝓝 (fun _ : Fin n => x)) :=
    tendsto_pi_nhds.mpr (fun _ => tendsto_truncation x)
  have hq := ((continuous_subtype_val.comp (homogeneousLift W p hp).cont).tendsto
    (fun _ => x)).comp ht
  have hpx := (p.cont.tendsto (fun _ => x)).comp ht
  exact tendsto_nhds_unique hq
    (hpx.congr (fun s => (homogeneousLift_diagonal_truncation W p hp s x).symm))

/-- Degree zero is included: the lift has the same constant value. -/
theorem homogeneousLift_zero
    (p : ContinuousMultilinearMap K (fun _ : Fin 0 => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (x : Fin 0 → C₀(I, K)) :
    (homogeneousLift W p hp x : Z) = p x := by
  have hx : x = fun _ => (0 : C₀(I, K)) := funext (fun r => Fin.elim0 r)
  rw [hx]
  exact homogeneousLift_diagonal W p hp 0

/-- With an empty index type every input tuple is diagonal, in every degree. -/
theorem homogeneousLift_apply_of_isEmpty [IsEmpty I]
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (x : Fin n → C₀(I, K)) :
    (homogeneousLift W p hp x : Z) = p x := by
  have hx : x = fun _ => (0 : C₀(I, K)) := by
    funext r
    ext i
    exact isEmptyElim i
  rw [hx]
  exact homogeneousLift_diagonal W p hp 0

/-- A homogeneous diagonal in a complete submodule has a continuous multilinear
lift with exactly the same diagonal and no larger operator norm. The witness is
the bounded-array map of the actual distinct-word grouped coefficients. This
holds for every degree and every discrete index type, without complete scalars. -/
theorem homogeneous_diagonal_lifting
    (p : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) :
    ∃ q : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) W,
      (∀ x, (q (fun _ => x) : Z) = p (fun _ => x)) ∧ ‖q‖ ≤ ‖p‖ :=
  ⟨homogeneousLift W p hp, homogeneousLift_diagonal W p hp,
    norm_homogeneousLift_le W p hp⟩

end CZero
