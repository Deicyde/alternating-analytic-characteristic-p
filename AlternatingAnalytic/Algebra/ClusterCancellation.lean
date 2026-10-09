import AlternatingAnalytic.Algebra.ClusterValues
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases

/-!
# Cancellation of clusters containing no output index

Lemma B.11: for finite families of clusters, one family per slot, the determinant
array of Ψ on the sums of all cluster inputs, evaluated at the first points of chosen
output clusters, equals the cluster value of the output clusters. Every term with an
occupied cluster that is not an output cluster cancels. The main proof assumes the
clusters are pairwise separated (every point of one below every point of the other);
disjoint clusters of consecutive points of `H` are separated.
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

/-- If the weighted double sum over one coordinate vanishes, the full weighted sum
vanishes. -/
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

/-- For separated blocks, the order pattern of labeled points is determined by the
block labels and the positions within each block. -/
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

/-- Two disjoint clusters of four consecutive points of `H` are separated. -/
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

/-- The blocks holding the operator, vector and output indices. -/
def assignmentTag (A B O : ∀ j, J j) (i : Fin 3 × Fin k) : Sigma J :=
  ⟨i.2, ![A i.2, B i.2, O i.2] i.1⟩

/-- The positions of the operator, vector and output indices within their blocks. -/
def assignmentPosition (a y : Fin k → Fin 4) (i : Fin 3 × Fin k) : Fin 4 :=
  ![a i.2, y i.2, 0] i.1

/-- Changing the operator and vector positions in one slot preserves comparisons
within each block, under the stated conditions for blocks that coincide. -/
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

/-- The coefficient for a fixed assignment of operator, vector and output blocks. -/
noncomputable def assignedClusterCoefficient (Ψ : ClusterMap L k)
    (C : Sigma J → Fin 4 → ℕ) (A B O : ∀ j, J j) (a y : Fin k → Fin 4) : L :=
  clusterCoefficient Ψ (fun j => C ⟨j, A j⟩ (a j))
    (fun j => C ⟨j, B j⟩ (y j)) (fun j => C ⟨j, O j⟩ 0)

/-- The determinant array evaluation for a fixed assignment of operator and vector
blocks, at fixed output blocks. -/
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

/-- The cluster weights kill a function that depends only on the relative order of
two positions. -/
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

/-- On an order-homogeneous set, the coefficient is unchanged by moving the operator
and vector positions of one slot in a way that preserves the order pattern. -/
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

/-- The group of terms vanishes if some operator block is not its slot's output
block. -/
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

/-- The group of terms vanishes if some vector block is not its slot's output block. -/
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

/-- Lemma B.11 for separated clusters. The family for slot `j` is indexed by `J j`,
and `O j` is its output cluster. -/
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

/-- Lemma B.11, with the cluster value computed on any family with the same block
order. This is the form used in Lemma B.12. -/
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

/-- Lemma B.11: output-free clusters cancel, for pairwise disjoint clusters of four
consecutive points of `H`. -/
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
