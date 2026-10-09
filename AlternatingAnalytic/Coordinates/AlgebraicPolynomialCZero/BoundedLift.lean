import AlternatingAnalytic.Analysis.CZeroCoordinates
import AlternatingAnalytic.Coordinates.AlgebraicPolynomialCZero.SortedWords
import AlternatingAnalytic.Coordinates.AlgebraicPolynomialCZero.DiagonalNorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Bounded lifts of continuous algebraic polynomials on `c₀` (Proposition I.2)

Over a nonarchimedean field `K` (not necessarily complete), a continuous diagonal
`p x = b (x, …, x)` of an `n`-linear map `b : c₀(I, K)ⁿ → Z` (not assumed continuous), with `Z`
complete and nonarchimedean, has a bounded `n`-linear lift `q` with `‖q‖ ≤ L ^ n ‖p‖_diag`.
Here `L` bounds the inverse Vandermonde matrix of the nodes `1, t, …, tⁿ` for a fixed
`0 < |t| < 1`, so it depends only on `K` and `n`. The lift is built from the symmetrized
coefficients on sorted words, bounded by interpolation on the unit grid.
-/

open Finset Filter
open scoped ZeroAtInfty Topology

namespace AlgebraicPolynomialCZero

universe uK uI uZ

section Constants

variable (K : Type uK) [NontriviallyNormedField K]

/-- A fixed scalar of norm strictly between `0` and `1`. -/
noncomputable def node : K := Classical.choose (NormedField.exists_norm_lt_one K)

theorem norm_node_pos : 0 < ‖node K‖ := (Classical.choose_spec (NormedField.exists_norm_lt_one K)).1

theorem norm_node_lt_one : ‖node K‖ < 1 :=
  (Classical.choose_spec (NormedField.exists_norm_lt_one K)).2

/-- The interpolation nodes `1, t, …, tⁿ`. -/
noncomputable def nodes (n : ℕ) : Fin (n + 1) → K := fun k => node K ^ (k : ℕ)

theorem nodes_injective (n : ℕ) : Function.Injective (nodes K n) := by
  intro k l h
  have h' : ‖node K‖ ^ (k : ℕ) = ‖node K‖ ^ (l : ℕ) := by
    simpa [nodes, norm_pow] using congrArg norm h
  exact Fin.ext (pow_right_injective₀ (norm_node_pos K) (norm_node_lt_one K).ne h')

theorem norm_nodes_le_one (n : ℕ) (k : Fin (n + 1)) : ‖nodes K n k‖ ≤ 1 := by
  rw [nodes, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_node_lt_one K).le

/-- A bound `L ≥ 1` for the entries of the inverse Vandermonde matrix of the nodes. -/
noncomputable def lagrangeConst (n : ℕ) : ℝ :=
  1 + ∑ i, ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖

theorem one_le_lagrangeConst (n : ℕ) : 1 ≤ lagrangeConst K n :=
  le_add_of_nonneg_right (sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)

theorem norm_inv_vandermonde_le (n : ℕ) (i k : Fin (n + 1)) :
    ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ ≤ lagrangeConst K n := by
  have hk : ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ ≤
      ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ :=
    single_le_sum (f := fun k => ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖)
      (fun _ _ => norm_nonneg _) (mem_univ k)
  have hi : ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ ≤
      ∑ i, ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖ :=
    single_le_sum (f := fun i => ∑ k, ‖(Matrix.vandermonde (nodes K n))⁻¹ i k‖)
      (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ i)
  rw [lagrangeConst]
  linarith

/-- The lifting constant `L ^ n` of Proposition I.2. -/
noncomputable def liftConst (n : ℕ) : ℝ := lagrangeConst K n ^ n

theorem one_le_liftConst (n : ℕ) : 1 ≤ liftConst K n :=
  one_le_pow₀ (one_le_lagrangeConst K n)

end Constants

section Coefficients

variable {K : Type uK} [NontriviallyNormedField K] [IsUltrametricDist K]
  {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
  {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z] {n : ℕ}

/-- A grid vector `∑ j, ν (g j) • e_j` with nodes in the unit ball has norm at most one. -/
theorem norm_gridVector_le {S : Finset I} (w : S → K) (hw : ∀ j, ‖w j‖ ≤ 1) :
    ‖∑ j, w j • CZero.coordinate (K := K) (j : I)‖ ≤ 1 := by
  refine (CZero.norm_le zero_le_one).mpr fun i => ?_
  have hi : (∑ j, w j • CZero.coordinate (K := K) (j : I)) i =
      ∑ j, w j * CZero.coordinate (K := K) (j : I) i := by
    rw [← CZero.evalCLM_apply, map_sum]
    simp
  rw [hi]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hw j)).trans
    ((CZero.norm_apply_le _ i).trans (CZero.norm_coordinate_le _))

variable [LinearOrder I]

/-- The symmetrized coefficients of an algebraic polynomial whose diagonal satisfies
`‖p x‖ ≤ D ‖x‖ ^ n` are bounded by `L ^ n D`. -/
theorem norm_coeff_le (b : MultilinearMap K (fun _ : Fin n => C₀(I, K)) Z) {D : ℝ} (hD : 0 ≤ D)
    (hbD : ∀ x, ‖b (fun _ => x)‖ ≤ D * ‖x‖ ^ n) (a : Fin n → I) :
    ‖coeff (fun a' => b (fun r => CZero.coordinate (K := K) (a' r))) a‖ ≤ liftConst K n * D := by
  have hC : 0 ≤ liftConst K n * D := mul_nonneg (zero_le_one.trans (one_le_liftConst K n)) hD
  by_cases ha : Monotone a
  swap
  · have hempty : (Fintype.piFinset fun _ => univ.image a).filter
        (fun a' : Fin n → I => sortWord a' = a) = ∅ := by
      ext a'
      simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ h
      exact ha (h ▸ monotone_sortWord a')
    rw [coeff, hempty, sum_empty, norm_zero]
    exact hC
  set S : Finset I := univ.image a
  rw [← sum_filter_wordCount_eq_coeff _ ha,
    ← sum_interpolation (nodes K n) (nodes_injective K n) b
      (fun j : S => CZero.coordinate (K := K) (j : I)) (fun j => wordCount a (j : I))]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun g _ => ?_
  rw [norm_smul, norm_prod]
  have hcard : Fintype.card S ≤ n := by
    rw [Fintype.card_coe]
    exact card_image_le.trans (by simp)
  have hW : ∏ j : S, ‖(Matrix.vandermonde (nodes K n))⁻¹ (wordCount a (j : I)) (g j)‖ ≤
      liftConst K n := by
    calc ∏ j : S, ‖(Matrix.vandermonde (nodes K n))⁻¹ (wordCount a (j : I)) (g j)‖
        ≤ ∏ _j : S, lagrangeConst K n :=
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => norm_inv_vandermonde_le K n _ _
      _ = lagrangeConst K n ^ Fintype.card S := by rw [prod_const, card_univ]
      _ ≤ liftConst K n := pow_le_pow_right₀ (one_le_lagrangeConst K n) hcard
  have hx : ‖b (fun _ => ∑ j : S, nodes K n (g j) • CZero.coordinate (K := K) (j : I))‖ ≤ D := by
    refine (hbD _).trans ?_
    calc D * ‖∑ j : S, nodes K n (g j) • CZero.coordinate (K := K) (j : I)‖ ^ n ≤ D * 1 :=
          mul_le_mul_of_nonneg_left
            (pow_le_one₀ (norm_nonneg _)
              (norm_gridVector_le _ fun j => norm_nodes_le_one K n (g j))) hD
      _ = D := mul_one D
  exact mul_le_mul hW hx (norm_nonneg _) (zero_le_one.trans (one_le_liftConst K n))

omit [IsUltrametricDist K] in
/-- The bounded-array map of the symmetrized coefficients agrees with the algebraic diagonal on
finite truncations. -/
theorem diag_truncation [CompleteSpace Z] (b : MultilinearMap K (fun _ : Fin n => C₀(I, K)) Z)
    {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ a, ‖coeff (fun a' => b (fun r => CZero.coordinate (K := K) (a' r))) a‖ ≤ C)
    (s : Finset I) (x : C₀(I, K)) :
    CZero.boundedArrayMultilinearMap _ C hC hc (fun _ => CZero.truncation s x) =
      b (fun _ => CZero.truncation s x) := by
  refine (CZero.boundedArrayMultilinearMap_truncation _ C hC hc (fun _ => x) (fun _ => s)).trans ?_
  refine (sum_smul_coeff (⇑x) _ s).trans ?_
  rw [CZero.truncation_eq_sum, MultilinearMap.map_sum_finset]
  refine sum_congr rfl fun a' _ => ?_
  exact (b.map_smul_univ (fun r => x (a' r)) (fun r => CZero.coordinate (a' r))).symm

end Coefficients

/-- Proposition I.2: for `n ≥ 1`, a continuous algebraic homogeneous polynomial
`p : c₀(I, K) → Z` of degree `n` has finite diagonal norm and a bounded `n`-linear lift `q` with
`‖q‖ ≤ C ‖p‖_diag`, where `C` depends only on `K` and `n`. -/
theorem exists_boundedLift_of_continuous_algebraicPolynomial
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Type uI) [TopologicalSpace I] [DiscreteTopology I]
        (Z : Type uZ) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
        [IsUltrametricDist Z] (p : C₀(I, K) → Z),
        Continuous p →
        (∃ b : MultilinearMap K (fun _ : Fin n => C₀(I, K)) Z, ∀ x, p x = b (fun _ => x)) →
        (∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n) ∧
        ∃ q : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z,
          (∀ x, q (fun _ => x) = p x) ∧
            ‖q‖ ≤ C * sInf {D : ℝ | 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n} := by
  refine ⟨liftConst K n, zero_le_one.trans (one_le_liftConst K n), ?_⟩
  intro I _ _ Z _ _ _ _ p hp hb'
  obtain ⟨b, hb⟩ := hb'
  have h0 : p 0 = 0 := by rw [hb]; exact diag_zero b hn
  have hhom : ∀ (c : K) x, p (c • x) = c ^ n • p x := fun c x => by rw [hb, hb, diag_smul]
  have hfin := exists_diag_bound hp.continuousAt h0 hhom
  refine ⟨hfin, ?_⟩
  have hD0 := diagNorm_nonneg (n := n) p
  have hpD : ∀ x, ‖b (fun _ => x)‖ ≤
      sInf {D : ℝ | 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n} * ‖x‖ ^ n := fun x => by
    rw [← hb]
    exact norm_le_diagNorm_mul h0 hfin x
  let : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  have hc := norm_coeff_le b hD0 hpD
  have hC := mul_nonneg (zero_le_one.trans (one_le_liftConst K n)) hD0
  refine ⟨CZero.boundedArrayMultilinearMap _ _ hC hc, fun x => ?_,
    CZero.norm_boundedArrayMultilinearMap_le _ _ hC hc⟩
  set q := CZero.boundedArrayMultilinearMap (K := K) _ _ hC hc
  have h1 : Tendsto (fun s : Finset I => q (fun _ => CZero.truncation s x)) atTop
      (𝓝 (q fun _ => x)) :=
    ((q.cont.comp (continuous_pi fun _ => continuous_id)).tendsto x).comp
      (CZero.tendsto_truncation x)
  have h2 : Tendsto (fun s : Finset I => p (CZero.truncation s x)) atTop (𝓝 (p x)) :=
    (hp.tendsto x).comp (CZero.tendsto_truncation x)
  refine tendsto_nhds_unique h1 (h2.congr fun s => ?_)
  rw [hb]
  exact (diag_truncation b hC hc s x).symm

end AlgebraicPolynomialCZero
