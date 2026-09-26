import AlternatingAnalytic.Analysis.L1Coordinates
import AlternatingAnalytic.Algebra.FiniteWordGrouping

/-!
# Homogeneous diagonal lifting on ordinary ℓ¹

The distinct-word coefficients from `FiniteWord` belong to the submodule containing
all diagonal values. Each coefficient has norm at most `d! * ‖B‖`, and the ordinary
ℓ¹ array constructor realizes them in the complete submodule. The shared finite
regrouping identity extends to every input by `lp.hasSum_single` and continuity.

Only the output submodule needs to be complete. The public closed-subspace theorem
obtains this from completeness of the ambient space, without completeness of the
scalar field. The real factorial counts distinct words and is never inverted.
The construction and all identities include degree zero and empty label types.
-/

open scoped lp BigOperators
open Filter Topology

namespace L1PolynomialLift

variable {K J Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z]

noncomputable local instance : DecidableEq J := Classical.decEq J

/-- The ordinary triangle inequality bounds each selected orbit coefficient by `d! * ‖B‖`. -/
theorem norm_groupedCoefficient_le {d : ℕ}
    (B : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) Z)
    (a : Fin d → J) :
    ‖FiniteWord.groupedCoefficient B.toMultilinearMap
      (fun j => lp.single 1 j (1 : K)) a‖ ≤ (d.factorial : ℝ) * ‖B‖ := by
  classical
  unfold FiniteWord.groupedCoefficient
  split_ifs
  · calc
      ‖∑ u ∈ FiniteWord.wordOrbit a, B (fun i => lp.single 1 (u i) (1 : K))‖
          ≤ ∑ u ∈ FiniteWord.wordOrbit a,
              ‖B (fun i => lp.single 1 (u i) (1 : K))‖ := norm_sum_le _ _
      _ ≤ ∑ _u ∈ FiniteWord.wordOrbit a, ‖B‖ := by
        apply Finset.sum_le_sum
        intro u hu
        simpa using B.le_opNorm (fun i => lp.single 1 (u i) (1 : K))
      _ = ((FiniteWord.wordOrbit a).card : ℝ) * ‖B‖ := by simp
      _ ≤ (d.factorial : ℝ) * ‖B‖ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast FiniteWord.card_wordOrbit_le a)
          (norm_nonneg B)
  · simp only [norm_zero]
    positivity

variable {d : ℕ}

private theorem sum_piFinset_eq_sum_subtype
    {A : Type*} [AddCommMonoid A] (s : Finset J) (f : (Fin d → J) → A) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin d => s), f a) =
      ∑ a : Fin d → s, f (fun i => (a i : J)) := by
  classical
  symm
  refine Finset.sum_bij (fun a _ i => (a i : J)) ?_ ?_ ?_ ?_
  · intro a ha
    exact Fintype.mem_piFinset.mpr (fun i => (a i).property)
  · intro a ha a' ha' haa'
    funext i
    exact Subtype.ext (congrFun haa' i)
  · intro a ha
    exact ⟨fun i => ⟨a i, Fintype.mem_piFinset.mp ha i⟩, Finset.mem_univ _, rfl⟩
  · intro a ha
    rfl

/-- The shared algebraic regrouping identity gives equality on finite coordinate diagonals. -/
theorem diagonal_eq_sum_single
    (B D : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) Z)
    (hD : ∀ a : Fin d → J,
      D (fun r => lp.single 1 (a r) (1 : K)) =
        FiniteWord.groupedCoefficient B.toMultilinearMap
          (fun j => lp.single 1 j (1 : K)) a)
    (s : Finset J) (x : J → K) :
    D (fun _ => ∑ j ∈ s, lp.single 1 j (x j)) =
      B (fun _ => ∑ j ∈ s, lp.single 1 j (x j)) := by
  classical
  rw [L1Coordinates.map_sum_single D (fun _ => x) (fun _ => s)]
  simp only [hD]
  rw [sum_piFinset_eq_sum_subtype]
  have hsingle (j : J) :
      x j • lp.single (E := fun _ : J => K) 1 j (1 : K) =
        lp.single 1 j (x j) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : J => K) 1 j (x j) (1 : K)).symm
  simpa only [hsingle, ContinuousMultilinearMap.coe_coe] using
    (FiniteWord.finite_diagonal_grouping B.toMultilinearMap
      (fun j => lp.single 1 j (1 : K)) s x).symm

/-- Continuity extends equality from the canonical finite coordinate truncations. -/
theorem diagonal_eq_of_sum_single_eq
    (D B : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) Z)
    (h : ∀ (s : Finset J) (x : J → K),
      D (fun _ => ∑ j ∈ s, lp.single 1 j (x j)) =
        B (fun _ => ∑ j ∈ s, lp.single 1 j (x j)))
    (x : lp (fun _ : J => K) 1) : D (fun _ => x) = B (fun _ => x) := by
  classical
  apply tendsto_nhds_unique (L1Coordinates.tendsto_map_sum_single D (fun _ => x))
  simpa only [h] using L1Coordinates.tendsto_map_sum_single B (fun _ => x)

/-- A complete submodule suffices for ordinary ℓ¹ diagonal lifting. The witness is
constructed from the actual selected coefficients of `FiniteWord.groupedCoefficient`. -/
theorem exists_l1_diagonal_lift_of_completeSpace
    (W : Submodule K Z) [CompleteSpace W] (d : ℕ)
    (B : ContinuousMultilinearMap K
      (fun _ : Fin d => lp (fun _ : J => K) 1) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) :
    ∃ C : ContinuousMultilinearMap K
        (fun _ : Fin d => lp (fun _ : J => K) 1) W,
      (∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ∧
      ‖C‖ ≤ (d.factorial : ℝ) * ‖B‖ := by
  classical
  let c : (Fin d → J) → W := fun a =>
    ⟨FiniteWord.groupedCoefficient B.toMultilinearMap
        (fun j => lp.single 1 j (1 : K)) a,
      FiniteWord.groupedCoefficient_mem W B.toMultilinearMap
        (fun j => lp.single 1 j (1 : K)) hB a⟩
  have hc (a : Fin d → J) : ‖c a‖ ≤ (d.factorial : ℝ) * ‖B‖ :=
    norm_groupedCoefficient_le B a
  let C := L1Coordinates.continuousMultilinearOfBounded (K := K) c
    ((d.factorial : ℝ) * ‖B‖) hc
  refine ⟨C, ?_, L1Coordinates.continuousMultilinearOfBounded_norm_le
    c _ (by positivity) hc⟩
  let D := W.subtypeL.compContinuousMultilinearMap C
  have hD (a : Fin d → J) :
      D (fun r => lp.single 1 (a r) (1 : K)) =
        FiniteWord.groupedCoefficient B.toMultilinearMap
          (fun j => lp.single 1 j (1 : K)) a := by
    change (C (fun r => lp.single 1 (a r) (1 : K)) : Z) = _
    rw [L1Coordinates.continuousMultilinearOfBounded_single]
  exact diagonal_eq_of_sum_single_eq D B (diagonal_eq_sum_single B D hD)

/-- A homogeneous diagonal in a closed subspace of a Banach space admits one
continuous multilinear representative with the same diagonal and norm at most
`d! * ‖B‖`, for the original induced norm on the subspace. -/
theorem exists_l1_diagonal_lift [CompleteSpace Z]
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K
      (fun _ : Fin d => lp (fun _ : J => K) 1) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) :
    ∃ C : ContinuousMultilinearMap K
        (fun _ : Fin d => lp (fun _ : J => K) 1) W,
      (∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ∧
      ‖C‖ ≤ (d.factorial : ℝ) * ‖B‖ := by
  let : CompleteSpace W := hW.completeSpace_coe
  exact exists_l1_diagonal_lift_of_completeSpace W d B hB

end L1PolynomialLift
