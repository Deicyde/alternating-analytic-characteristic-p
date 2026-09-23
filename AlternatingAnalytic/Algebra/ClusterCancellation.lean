import AlternatingAnalytic.Algebra.ClusterValues
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases

/-!
# Cancellation of clusters containing no output index

Finite families are indexed separately for each input slot. Distinct labeled blocks
are separated: every point of one is below every point of the other. Consecutive,
disjoint clusters in the homogeneous set have exactly this property.
-/

open Finset

namespace AlternatingAnalytic

variable {L : Type*} [Field L] {k : ℕ}

/-- Split a weighted sum over coordinate selections at one specified coordinate. -/
theorem sum_weighted_split_at {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]
    (j : I) (w : I → P → L) (f : (I → P) → L) :
    (∑ a : I → P, (∏ l, w l (a l)) * f a) =
      ∑ b : {l : I // l ≠ j} → P,
        (∏ l : {l : I // l ≠ j}, w l (b l)) *
          ∑ p : P, w j p * f ((Equiv.funSplitAt j P).symm (p, b)) := by
  classical
  let e := Equiv.funSplitAt j P
  rw [← e.symm.sum_comp (fun a => (∏ l, w l (a l)) * f a)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hprod : (∏ l, w l (e.symm (p, b) l)) =
      w j p * ∏ l : {l : I // l ≠ j}, w l (b l) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun l : I => l = j)]
    congr 1
    · trans w j (e.symm (p, b) j)
      · apply Finset.prod_eq_single (f := fun l : {l : I // l = j} =>
          w l (e.symm (p, b) l)) (⟨j, rfl⟩ : {l : I // l = j})
        · intro l _ hl
          exact (hl (Subtype.ext l.property)).elim
        · intro h
          exact (h (@Finset.mem_univ _ (Subtype.fintype (fun l : I => l = j))
            ⟨j, rfl⟩)).elim
      · simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro l _
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, l.property]
  rw [hprod]
  ac_rfl

/-- A local weighted double sum vanishing at a coordinate makes the full weighted
sum vanish. This is a finite-sum statement, independent of the coefficient geometry. -/
theorem sum_weighted_double_eq_zero {I P Q : Type*} [Fintype I] [DecidableEq I]
    [Fintype P] [Fintype Q] (j : I) (s : I → P → L) (w : I → Q → L)
    (f : (I → P) → (I → Q) → L)
    (hlocal : ∀ a y,
      ∑ p, ∑ q, s j p * w j q * f (Function.update a j p) (Function.update y j q) = 0) :
    (∑ a : I → P, ∑ y : I → Q,
      ((∏ l, s l (a l)) * (∏ l, w l (y l))) * f a y) = 0 := by
  classical
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_weighted_split_at j]
  apply Finset.sum_eq_zero
  intro a _
  suffices h : (∑ p, s j p * ∑ y : I → Q,
      (∏ l, w l (y l)) * f ((Equiv.funSplitAt j P).symm (p, a)) y) = 0 by
    rw [h, mul_zero]
  simp_rw [sum_weighted_split_at j w, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hP : Nonempty P
  · by_cases hQ : Nonempty Q
    · let p₀ : P := Classical.choice hP
      let q₀ : Q := Classical.choice hQ
      let a₀ := (Equiv.funSplitAt j P).symm (p₀, a)
      let y₀ := (Equiv.funSplitAt j Q).symm (q₀, y)
      have ha (p : P) : (Equiv.funSplitAt j P).symm (p, a) =
          Function.update a₀ j p := by
        funext l
        by_cases hl : l = j <;>
          simp [Equiv.funSplitAt, Equiv.piSplitAt, a₀, hl]
      have hy (q : Q) : (Equiv.funSplitAt j Q).symm (q, y) =
          Function.update y₀ j q := by
        funext l
        by_cases hl : l = j <;>
          simp [Equiv.funSplitAt, Equiv.piSplitAt, y₀, hl]
      simp_rw [ha, hy]
      calc
        _ = (∏ l : {l : I // l ≠ j}, w l (y l)) *
            ∑ p, ∑ q, s j p * w j q * f (Function.update a₀ j p)
              (Function.update y₀ j q) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro q _
          ac_rfl
        _ = 0 := by rw [hlocal, mul_zero]
    · have : IsEmpty Q := not_nonempty_iff.mp hQ
      simp
  · have : IsEmpty P := not_nonempty_iff.mp hP
    simp

/-- Across separated blocks only the labels matter; within one block the internal
position comparisons determine the order pattern. -/
theorem separated_blocks_order_pattern {G I : Type*} (C : G → Fin 4 → ℕ)
    (hmono : ∀ g, StrictMono (C g))
    (hsep : ∀ g h, g ≠ h →
      (∀ p q, C g p < C h q) ∨ (∀ p q, C h p < C g q))
    (tag : I → G) (u v : I → Fin 4)
    (hpos : ∀ i j, tag i = tag j →
      (u i < u j ↔ v i < v j) ∧ (u i = u j ↔ v i = v j))
    (i j : I) :
    (C (tag i) (u i) < C (tag j) (u j) ↔ C (tag i) (v i) < C (tag j) (v j)) ∧
    (C (tag i) (u i) = C (tag j) (u j) ↔ C (tag i) (v i) = C (tag j) (v j)) := by
  by_cases h : tag i = tag j
  · have hp := hpos i j h
    rw [h]
    exact ⟨(hmono _).lt_iff_lt.trans (hp.1.trans (hmono _).lt_iff_lt.symm),
      (hmono _).injective.eq_iff.trans (hp.2.trans (hmono _).injective.eq_iff.symm)⟩
  · rcases hsep _ _ h with hlt | hgt
    · exact ⟨iff_of_true (hlt _ _) (hlt _ _),
        iff_of_false (ne_of_lt (hlt _ _)) (ne_of_lt (hlt _ _))⟩
    · exact ⟨iff_of_false (not_lt_of_gt (hgt _ _)) (not_lt_of_gt (hgt _ _)),
        iff_of_false (ne_of_gt (hgt _ _)) (ne_of_gt (hgt _ _))⟩

/-- Two disjoint increasing four-point intervals in `H` are separated. The interval
hypotheses express that the four points are consecutive elements of `H`. -/
theorem cluster_separated_of_intervals (H : Set ℕ) (C D : Fin 4 → ℕ)
    (hC : StrictMono C) (hD : StrictMono D)
    (hCH : ∀ p, C p ∈ H) (hDH : ∀ p, D p ∈ H)
    (hCI : ∀ x ∈ H, C 0 ≤ x → x ≤ C 3 → ∃ p, C p = x)
    (hDI : ∀ x ∈ H, D 0 ≤ x → x ≤ D 3 → ∃ p, D p = x)
    (hdisj : ∀ p q, C p ≠ D q) :
    (∀ p q, C p < D q) ∨ (∀ p q, D p < C q) := by
  rcases lt_or_gt_of_ne (hdisj 0 0) with h | h
  · have hgap : C 3 < D 0 := by
      by_contra! hle
      obtain ⟨p, hp⟩ := hCI (D 0) (hDH 0) h.le hle
      exact hdisj p 0 hp
    exact Or.inl fun p q => lt_of_le_of_lt (hC.monotone (by omega))
      (lt_of_lt_of_le hgap (hD.monotone (by omega)))
  · have hgap : D 3 < C 0 := by
      by_contra! hle
      obtain ⟨p, hp⟩ := hDI (C 0) (hCH 0) h.le hle
      exact hdisj 0 p hp.symm
    exact Or.inr fun p q => lt_of_le_of_lt (hD.monotone (by omega))
      (lt_of_lt_of_le hgap (hC.monotone (by omega)))

variable {J : Fin k → Type*}

/-- The labeled blocks of the operator, vector, and output coordinates. -/
def assignmentTag (A B O : ∀ j, J j) (i : Fin 3 × Fin k) : Sigma J :=
  ⟨i.2, ![A i.2, B i.2, O i.2] i.1⟩

/-- The internal positions of the operator, vector, and output coordinates. -/
def assignmentPosition (a y : Fin k → Fin 4) (i : Fin 3 × Fin k) : Fin 4 :=
  ![a i.2, y i.2, 0] i.1

/-- Changing two positions in a single slot preserves comparisons within each
occupied block under exactly the three possible coincidence conditions. -/
theorem assignmentPosition_update_pattern (A B O : ∀ j, J j)
    (a y : Fin k → Fin 4) (j : Fin k) (p q p' q' : Fin 4)
    (hab : A j = B j → (p < q ↔ p' < q') ∧ (p = q ↔ p' = q'))
    (hao : A j = O j → p = p') (hbo : B j = O j → q = q')
    (i l : Fin 3 × Fin k) (htag : assignmentTag A B O i = assignmentTag A B O l) :
    (assignmentPosition (Function.update a j p) (Function.update y j q) i <
        assignmentPosition (Function.update a j p) (Function.update y j q) l ↔
      assignmentPosition (Function.update a j p') (Function.update y j q') i <
        assignmentPosition (Function.update a j p') (Function.update y j q') l) ∧
    (assignmentPosition (Function.update a j p) (Function.update y j q) i =
        assignmentPosition (Function.update a j p) (Function.update y j q) l ↔
      assignmentPosition (Function.update a j p') (Function.update y j q') i =
        assignmentPosition (Function.update a j p') (Function.update y j q') l) := by
  rcases i with ⟨r, n⟩
  rcases l with ⟨s, m⟩
  have hnm : n = m := congrArg Sigma.fst htag
  subst m
  by_cases hn : n = j
  · subst n
    fin_cases r <;> fin_cases s <;>
      simp_all [assignmentTag, assignmentPosition]
    omega
  · simp [assignmentPosition, hn]

/-- The actual coefficient associated to a fixed assignment of input/output blocks. -/
noncomputable def assignedClusterCoefficient (Ψ : ClusterMap L k)
    (C : Sigma J → Fin 4 → ℕ) (A B O : ∀ j, J j) (a y : Fin k → Fin 4) : L :=
  clusterCoefficient Ψ (fun j => C ⟨j, A j⟩ (a j))
    (fun j => C ⟨j, B j⟩ (y j)) (fun j => C ⟨j, O j⟩ 0)

/-- The actual determinant evaluation with possibly different operator and vector
block assignments, keeping the selected output blocks fixed. -/
noncomputable def assignedClusterValue (Ψ : ClusterMap L k)
    (C : Sigma J → Fin 4 → ℕ) (A B O : ∀ j, J j) : L :=
  determinantArray
    (Ψ (fun j => clusterInput clusterOperatorWeight (C ⟨j, A j⟩))
      (fun j => clusterInput clusterVectorWeight (C ⟨j, B j⟩)))
    (fun j => C ⟨j, O j⟩ 0)

theorem assignedClusterValue_expansion (Ψ : ClusterMap L k)
    (C : Sigma J → Fin 4 → ℕ) (A B O : ∀ j, J j) :
    assignedClusterValue Ψ C A B O =
      ∑ a : Fin k → Fin 4, ∑ y : Fin k → Fin 4,
        ((∏ j, clusterOperatorWeight (R := L) (a j)) *
          (∏ j, clusterVectorWeight (y j))) * assignedClusterCoefficient Ψ C A B O a y :=
  determinantArray_weighted_expansion Ψ (fun _ => clusterOperatorWeight)
    (fun _ => clusterVectorWeight) (fun j => C ⟨j, A j⟩)
    (fun j => C ⟨j, B j⟩) (fun j => C ⟨j, O j⟩ 0)

/-- A scalar function depending only on the relative order of two internal
positions is annihilated by the two cluster weights. -/
theorem sum_cluster_pair_of_pattern (f : Fin 4 → Fin 4 → L)
    (h : ∀ p q p' q', ((p < q ↔ p' < q') ∧ (p = q ↔ p' = q')) →
      f p q = f p' q') :
    (∑ p, ∑ q, clusterOperatorWeight (R := L) p * clusterVectorWeight q * f p q) = 0 := by
  have hf (p q : Fin 4) : f p q =
      if p < q then f 0 1 else if p = q then f 0 0 else f 1 0 := by
    split_ifs with hpq heq
    · apply h
      omega
    · apply h
      omega
    · apply h
      omega
  calc
    _ = ∑ p, ∑ q, clusterOperatorWeight (R := L) p * clusterVectorWeight q *
        (if p < q then f 0 1 else if p = q then f 0 0 else f 1 0) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [hf p q]
    _ = 0 := sum_cluster_weights_order_pattern _ _ _

section Homogeneous

variable (Ψ : ClusterMap L k) (H : Set ℕ)
  (hpattern : ∀ (z z' : Fin 3 × Fin k → ℕ),
    (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
    (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
    clusterCoefficientTuple Ψ z = clusterCoefficientTuple Ψ z')
  (C : Sigma J → Fin 4 → ℕ) (hmono : ∀ g, StrictMono (C g))
  (hCH : ∀ g p, C g p ∈ H)
  (hsep : ∀ g h, g ≠ h →
    (∀ p q, C g p < C h q) ∨ (∀ p q, C h p < C g q))

include hpattern hmono hCH hsep

/-- Coefficient homogeneity transports exactly the permissible position changes
inside the two input blocks assigned to a single slot. -/
theorem assignedClusterCoefficient_update_eq (A B O : ∀ j, J j)
    (a y : Fin k → Fin 4) (j : Fin k) (p q p' q' : Fin 4)
    (hab : A j = B j → (p < q ↔ p' < q') ∧ (p = q ↔ p' = q'))
    (hao : A j = O j → p = p') (hbo : B j = O j → q = q') :
    assignedClusterCoefficient Ψ C A B O (Function.update a j p) (Function.update y j q) =
      assignedClusterCoefficient Ψ C A B O (Function.update a j p')
        (Function.update y j q') := by
  have h := hpattern
    (fun i => C (assignmentTag A B O i)
      (assignmentPosition (Function.update a j p) (Function.update y j q) i))
    (fun i => C (assignmentTag A B O i)
      (assignmentPosition (Function.update a j p') (Function.update y j q') i))
    (fun i => hCH _ _) (fun i => hCH _ _)
    (separated_blocks_order_pattern C hmono hsep (assignmentTag A B O) _ _
      (assignmentPosition_update_pattern A B O a y j p q p' q' hab hao hbo))
  simpa [clusterCoefficientTuple, assignedClusterCoefficient,
    assignmentTag, assignmentPosition] using h

/-- If an assigned operator block is not its slot's output block, the entire
assigned group of the genuine determinant-array expansion vanishes. -/
theorem assignedClusterValue_eq_zero_of_operator_free (A B O : ∀ j, J j)
    (j : Fin k) (hfree : A j ≠ O j) : assignedClusterValue Ψ C A B O = 0 := by
  classical
  rw [assignedClusterValue_expansion]
  apply sum_weighted_double_eq_zero j
  intro a y
  by_cases hab : A j = B j
  · apply sum_cluster_pair_of_pattern
    intro p q p' q' hpq
    apply assignedClusterCoefficient_update_eq Ψ H hpattern C hmono hCH hsep
    · exact fun _ => hpq
    · exact fun h => (hfree h).elim
    · exact fun h => (hfree (hab.trans h)).elim
  · have hc (p q : Fin 4) :
        assignedClusterCoefficient Ψ C A B O (Function.update a j p) (Function.update y j q) =
        assignedClusterCoefficient Ψ C A B O (Function.update a j 0) (Function.update y j q) :=
      assignedClusterCoefficient_update_eq Ψ H hpattern C hmono hCH hsep A B O a y j p q 0 q
        (fun h => (hab h).elim) (fun h => (hfree h).elim) (fun _ => rfl)
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q _
    calc
      _ = (∑ p, clusterOperatorWeight (R := L) p) *
          (clusterVectorWeight q * assignedClusterCoefficient Ψ C A B O
            (Function.update a j 0) (Function.update y j q)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        rw [hc p q]
        exact mul_assoc _ _ _
      _ = 0 := by rw [sum_clusterOperatorWeight, zero_mul]

/-- The corresponding cancellation when the free block occurs in a vector input. -/
theorem assignedClusterValue_eq_zero_of_vector_free (A B O : ∀ j, J j)
    (j : Fin k) (hfree : B j ≠ O j) : assignedClusterValue Ψ C A B O = 0 := by
  classical
  by_cases hab : A j = B j
  · exact assignedClusterValue_eq_zero_of_operator_free Ψ H hpattern C hmono hCH hsep
      A B O j (fun h => hfree (hab.symm.trans h))
  rw [assignedClusterValue_expansion]
  apply sum_weighted_double_eq_zero j
  intro a y
  have hc (p q : Fin 4) :
      assignedClusterCoefficient Ψ C A B O (Function.update a j p) (Function.update y j q) =
      assignedClusterCoefficient Ψ C A B O (Function.update a j p) (Function.update y j 0) :=
    assignedClusterCoefficient_update_eq Ψ H hpattern C hmono hCH hsep A B O a y j p q p 0
      (fun h => (hab h).elim) (fun _ => rfl) (fun h => (hfree h).elim)
  apply Finset.sum_eq_zero
  intro p _
  calc
    _ = clusterOperatorWeight (R := L) p * (∑ q, clusterVectorWeight (R := L) q) *
        assignedClusterCoefficient Ψ C A B O
          (Function.update a j p) (Function.update y j 0) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      rw [hc p q]
    _ = 0 := by rw [sum_clusterVectorWeight, mul_zero, zero_mul]

/-- The paper's output-free cluster cancellation lemma. Finite families are indexed
by `J j`, and `O j` chooses the output cluster in that family. The left side is the
actual evaluation of Ψ on the sums of all cluster inputs. -/
theorem cluster_family_cancellation [∀ j, Fintype (J j)] (O : ∀ j, J j) :
    determinantArray
      (Ψ (fun j => ∑ γ : J j, clusterInput clusterOperatorWeight (C ⟨j, γ⟩))
        (fun j => ∑ γ : J j, clusterInput clusterVectorWeight (C ⟨j, γ⟩)))
      (fun j => C ⟨j, O j⟩ 0) = clusterValue Ψ (fun j => C ⟨j, O j⟩) := by
  classical
  have hgroup : determinantArray
      (Ψ (fun j => ∑ γ : J j, clusterInput clusterOperatorWeight (C ⟨j, γ⟩))
        (fun j => ∑ γ : J j, clusterInput clusterVectorWeight (C ⟨j, γ⟩)))
      (fun j => C ⟨j, O j⟩ 0) =
      ∑ A : ∀ j, J j, ∑ B : ∀ j, J j, assignedClusterValue Ψ C A B O := by
    rw [Ψ.map_sum]
    simp only [_root_.sum_apply, MultilinearMap.map_sum, map_sum, Finset.sum_apply,
      assignedClusterValue]
  rw [hgroup]
  calc
    _ = ∑ B : ∀ j, J j, assignedClusterValue Ψ C O B O := by
      apply Finset.sum_eq_single O
      · intro A _ hA
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hA
        apply Finset.sum_eq_zero
        intro B _
        exact assignedClusterValue_eq_zero_of_operator_free Ψ H hpattern C hmono hCH hsep
          A B O j hj
      · simp
    _ = assignedClusterValue Ψ C O O O := by
      apply Finset.sum_eq_single O
      · intro B _ hB
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hB
        exact assignedClusterValue_eq_zero_of_vector_free Ψ H hpattern C hmono hCH hsep
          O B O j hj
      · simp
    _ = clusterValue Ψ (fun j => C ⟨j, O j⟩) := rfl

/-- The staircase interface: an entry from the fixed family-sum exterior vector
equals the value of any representative with the same labeled-block order. -/
theorem cluster_family_cancellation_of_order [∀ j, Fintype (J j)] (O : ∀ j, J j)
    (D : Fin k → Fin 4 → ℕ) (hD : ∀ j, StrictMono (D j))
    (hDH : ∀ j p, D j p ∈ H) (τ : Equiv.Perm (Fin k))
    (hordC : ∀ j l, τ j < τ l → ∀ p q, C ⟨j, O j⟩ p < C ⟨l, O l⟩ q)
    (hordD : ∀ j l, τ j < τ l → ∀ p q, D j p < D l q) :
    determinantArray
      (Ψ (fun j => ∑ γ : J j, clusterInput clusterOperatorWeight (C ⟨j, γ⟩))
        (fun j => ∑ γ : J j, clusterInput clusterVectorWeight (C ⟨j, γ⟩)))
      (fun j => C ⟨j, O j⟩ 0) = clusterValue Ψ D := by
  rw [cluster_family_cancellation Ψ H hpattern C hmono hCH hsep O]
  exact clusterValue_eq_of_order Ψ H hpattern _ D (fun j => hmono _) hD
    (fun j p => hCH _ _) hDH τ hordC hordD

end Homogeneous

/-- The cancellation theorem stated directly for pairwise disjoint consecutive
clusters of the homogeneous set, as in the paper. -/
theorem cluster_family_cancellation_of_intervals [∀ j, Fintype (J j)]
    (Ψ : ClusterMap L k) (H : Set ℕ)
    (hpattern : ∀ (z z' : Fin 3 × Fin k → ℕ),
      (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
      (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
      clusterCoefficientTuple Ψ z = clusterCoefficientTuple Ψ z')
    (C : Sigma J → Fin 4 → ℕ) (hmono : ∀ g, StrictMono (C g))
    (hCH : ∀ g p, C g p ∈ H)
    (hinterval : ∀ g x, x ∈ H → C g 0 ≤ x → x ≤ C g 3 → ∃ p, C g p = x)
    (hdisj : ∀ g h, g ≠ h → ∀ p q, C g p ≠ C h q) (O : ∀ j, J j) :
    determinantArray
      (Ψ (fun j => ∑ γ : J j, clusterInput clusterOperatorWeight (C ⟨j, γ⟩))
        (fun j => ∑ γ : J j, clusterInput clusterVectorWeight (C ⟨j, γ⟩)))
      (fun j => C ⟨j, O j⟩ 0) = clusterValue Ψ (fun j => C ⟨j, O j⟩) := by
  apply cluster_family_cancellation Ψ H hpattern C hmono hCH
  intro g h hgh
  exact cluster_separated_of_intervals H (C g) (C h) (hmono g) (hmono h)
    (hCH g) (hCH h) (hinterval g) (hinterval h) (hdisj g h hgh)

end AlternatingAnalytic
