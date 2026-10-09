import AlternatingAnalytic.Algebra.ClusterCancellation
import AlternatingAnalytic.Algebra.ExteriorFlattening
import AlternatingAnalytic.Algebra.StaircaseRank

/-!
# The cluster staircase

Lemma B.12: if τ' is τ with two adjacent positions exchanged, then χ(τ) = χ(τ').
Interlacing two families of `m` clusters gives one exterior vector ω whose sampled
determinant array is the staircase matrix with entries χ(τ) and χ(τ'). Its rank is at
most sdim(ω), which is bounded, so the two entries agree.
-/

open Finset Module

namespace AlternatingAnalytic

variable {L : Type*} [Field L] {k : ℕ}

/-- An infinite set of natural numbers contains the range of an increasing sequence. -/
theorem exists_strictMono_in_infinite_set (H : Set ℕ) (hH : H.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, e n ∈ H := by
  apply Nat.exists_strictMono_subsequence
  intro N
  obtain ⟨n, hn⟩ := (hH.sdiff (Finset.finite_toSet (Finset.range (N + 1)))).nonempty
  refine ⟨n, ?_, hn.1⟩
  have : ¬n < N + 1 := by simpa using hn.2
  omega

/-- A matrix of determinant array entries of ω has rank at most sdim(ω), when the
rows vary only the coordinate `α`. -/
theorem determinantArray_update_rank_le {R S : Type*} [Fintype R] [Fintype S]
    (ω : ⋀[L]^k (ℕ → L)) (α : Fin k) (rows : R → ℕ) (columns : S → Fin k → ℕ) :
    (Matrix.of fun r s => determinantArray ω
      (Function.update (columns s) α (rows r))).rank ≤ exteriorSupportDim ω := by
  classical
  obtain ⟨U, hU, hω, hdim⟩ := exteriorSupportDim_attained ω
  let := hU
  let restriction : (ℕ → L) →ₗ[L] (R → L) := LinearMap.pi fun r => LinearMap.proj (rows r)
  let M : Matrix R S L := fun r s => determinantArray ω
    (Function.update (columns s) α (rows r))
  have hcols : Submodule.span L (Set.range M.col) ≤ U.map restriction := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    let φ : Fin k → Module.Dual L (ℕ → L) := fun i => LinearMap.proj (columns s i)
    refine Submodule.mem_map.mpr
      ⟨exteriorContraction α φ ω, exteriorContraction_mem_support α φ U hω, ?_⟩
    funext r
    have hforms : Function.update φ α (LinearMap.proj (rows r)) =
        fun i => LinearMap.proj (Function.update (columns s) α (rows r) i) := by
      funext i
      by_cases hi : i = α <;> simp [φ, hi]
    have h := exteriorContraction_eval α φ (LinearMap.proj (rows r)) ω
    rw [hforms] at h
    change (exteriorContraction α φ ω) (rows r) = determinantArray ω
      (Function.update (columns s) α (rows r))
    simpa only [determinantArray, exteriorEvaluationArray, LinearMap.pi_apply, LinearMap.proj_apply,
      Function.comp_def] using h
  calc
    _ = Module.finrank L (Submodule.span L (Set.range M.col)) :=
      Matrix.rank_eq_finrank_span_cols M
    _ ≤ Module.finrank L (U.map restriction) := Submodule.finrank_mono hcols
    _ ≤ Module.finrank L U := Submodule.finrank_map_le restriction U
    _ = exteriorSupportDim ω := hdim

/-- A sum of cluster inputs on disjoint clusters, with weights in `{0,1,-1}`, takes
values in `{0,1,-1}`. -/
theorem sum_clusterInput_ternary {B : Type*} [Fintype B]
    (C : B → Fin 4 → ℕ) (hinj : Function.Injective (fun t : B × Fin 4 => C t.1 t.2))
    (w : Fin 4 → L) (hw : ∀ p, w p = 0 ∨ w p = 1 ∨ w p = -1) (x : ℕ) :
    (∑ b, clusterInput w (C b)) x = 0 ∨
      (∑ b, clusterInput w (C b)) x = 1 ∨ (∑ b, clusterInput w (C b)) x = -1 := by
  classical
  have he : (∑ b, clusterInput w (C b)) x =
      ∑ t : B × Fin 4, if C t.1 t.2 = x then w t.2 else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [clusterInput, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : C b p = x <;> simp [h]
  rw [he]
  by_cases hx : ∃ t : B × Fin 4, C t.1 t.2 = x
  · obtain ⟨t, rfl⟩ := hx
    have hs : (∑ u : B × Fin 4, if C u.1 u.2 = C t.1 t.2 then w u.2 else 0) = w t.2 := by
      rw [Finset.sum_eq_single t]
      · simp
      · intro u _ hut
        have : C u.1 u.2 ≠ C t.1 t.2 := fun h => hut (hinj h)
        simp [this]
      · simp
    rw [hs]
    exact hw t.2
  · have hs : (∑ t : B × Fin 4, if C t.1 t.2 = x then w t.2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      simp only [ite_eq_right (fun h => hx ⟨t, h⟩)]
    exact Or.inl hs

namespace StaircaseClusters

/-- The rank of the `n`-th cluster of family `j`. Each family has `m` clusters; the
families of `α` and `β` are interlaced, and the others keep the order given by τ. -/
def blockRank (τ : Equiv.Perm (Fin k)) (α β : Fin k) (m : ℕ)
    (j : Fin k) (n : Fin m) : ℕ :=
  if j = α then m * (τ α).val + 2 * n.val
  else if j = β then m * (τ α).val + 2 * n.val + 1
  else m * (τ j).val + n.val

section Rank

variable (τ : Equiv.Perm (Fin k)) (α β : Fin k) (hαβ : α ≠ β)
  (hadj : (τ β).val = (τ α).val + 1) {m : ℕ}

include hαβ hadj in
theorem blockRank_bounds (j : Fin k) (n : Fin m) :
    m * (if j = β then (τ α).val else (τ j).val) ≤ blockRank τ α β m j n ∧
    blockRank τ α β m j n < m * (if j = α then (τ α).val + 2 else (τ j).val + 1) := by
  by_cases hja : j = α
  · subst j
    simp only [blockRank, ite_true, ite_eq_right hαβ, Nat.mul_succ]
    omega
  · by_cases hjb : j = β
    · subst j
      simp only [blockRank, ite_eq_right hja, ite_true, hadj, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [blockRank, ite_eq_right hja, ite_eq_right hjb, Nat.mul_add, Nat.mul_one]
      omega

include hαβ hadj in
/-- Apart from the pair `(α, β)`, block ranks follow the order given by τ. -/
theorem blockRank_lt_of_order {j l : Fin k} (n t : Fin m) (hjl : τ j < τ l)
    (hpair : ¬(j = α ∧ l = β)) : blockRank τ α β m j n < blockRank τ α β m l t := by
  have hgap : (if j = α then (τ α).val + 2 else (τ j).val + 1) ≤
      (if l = β then (τ α).val else (τ l).val) := by
    change (τ j).val < (τ l).val at hjl
    by_cases hja : j = α
    · subst j
      have hlb : l ≠ β := fun h => hpair ⟨rfl, h⟩
      have hne : (τ l).val ≠ (τ β).val := fun h => hlb (τ.injective (Fin.ext h))
      simp only [ite_true, ite_eq_right hlb]
      omega
    · by_cases hlb : l = β
      · subst l
        have hne : (τ j).val ≠ (τ α).val := fun h => hja (τ.injective (Fin.ext h))
        simp only [ite_eq_right hja, ite_true]
        omega
      · simp only [ite_eq_right hja, ite_eq_right hlb]
        omega
  exact lt_of_lt_of_le (blockRank_bounds τ α β hαβ hadj j n).2
    ((Nat.mul_le_mul_left m hgap).trans (blockRank_bounds τ α β hαβ hadj l t).1)

include hαβ in
theorem blockRank_left_lt_right_iff (n t : Fin m) :
    blockRank τ α β m α n < blockRank τ α β m β t ↔ n ≤ t := by
  simp only [blockRank, ite_true, ite_eq_right hαβ.symm, Fin.le_def]
  omega

include hαβ in
theorem blockRank_right_lt_left_iff (n t : Fin m) :
    blockRank τ α β m β t < blockRank τ α β m α n ↔ t < n := by
  simp only [blockRank, ite_true, ite_eq_right hαβ.symm, Fin.lt_def]
  omega

include hαβ hadj in
theorem blockRank_injective :
    Function.Injective (fun t : Fin k × Fin m => blockRank τ α β m t.1 t.2) := by
  rintro ⟨j, n⟩ ⟨l, t⟩ heq
  change blockRank τ α β m j n = blockRank τ α β m l t at heq
  by_cases hjl : j = l
  · subst l
    have hnt : n = t := by
      apply Fin.ext
      simp only [blockRank] at heq
      split_ifs at heq <;> omega
    exact congrArg (Prod.mk j) hnt
  · exfalso
    by_cases hp : j = α ∧ l = β
    · rcases hp with ⟨hja, hlb⟩
      subst j
      subst l
      simp only [blockRank, ite_true, ite_eq_right hαβ.symm] at heq
      omega
    · by_cases hp' : l = α ∧ j = β
      · rcases hp' with ⟨hla, hjb⟩
        subst l
        subst j
        simp only [blockRank, ite_true, ite_eq_right hαβ.symm] at heq
        omega
      · rcases lt_or_gt_of_ne (fun h => hjl (τ.injective h)) with h | h
        · exact (ne_of_lt (blockRank_lt_of_order τ α β hαβ hadj n t h hp)) heq
        · exact (ne_of_gt (blockRank_lt_of_order τ α β hαβ hadj t n h hp')) heq

include hαβ hadj in
/-- An adjacent exchange reverses only the comparison of the exchanged pair. -/
theorem adjacent_swap_order_cases {j l : Fin k}
    (h : ((Equiv.swap α β).trans τ) j < ((Equiv.swap α β).trans τ) l) :
    (j = β ∧ l = α) ∨ (τ j < τ l ∧ ¬(j = α ∧ l = β)) := by
  have hja : j ≠ α → (τ j).val ≠ (τ α).val :=
    fun hne heq => hne (τ.injective (Fin.ext heq))
  have hjb : j ≠ β → (τ j).val ≠ (τ β).val :=
    fun hne heq => hne (τ.injective (Fin.ext heq))
  have hla : l ≠ α → (τ l).val ≠ (τ α).val :=
    fun hne heq => hne (τ.injective (Fin.ext heq))
  have hlb : l ≠ β → (τ l).val ≠ (τ β).val :=
    fun hne heq => hne (τ.injective (Fin.ext heq))
  simp only [Equiv.trans_apply, Equiv.swap_apply_def, Fin.lt_def] at h ⊢
  by_cases h₁ : j = α <;> by_cases h₂ : j = β <;>
    by_cases h₃ : l = α <;> by_cases h₄ : l = β <;>
    simp_all <;> omega

/-- The output cluster chosen in each family. -/
def selection [NeZero m] (n t : Fin m) (j : Fin k) : Fin m :=
  if j = α then n else if j = β then t else 0

include hαβ hadj in
theorem selected_order [NeZero m] (n t : Fin m) (hnt : n ≤ t)
    {j l : Fin k} (hjl : τ j < τ l) :
    blockRank τ α β m j (selection α β n t j) <
      blockRank τ α β m l (selection α β n t l) := by
  by_cases hp : j = α ∧ l = β
  · rcases hp with ⟨hja, hlb⟩
    subst j
    subst l
    simpa only [selection, ite_true, ite_eq_right hαβ.symm] using
      (blockRank_left_lt_right_iff τ α β hαβ n t).mpr hnt
  · exact blockRank_lt_of_order τ α β hαβ hadj _ _ hjl hp

include hαβ hadj in
theorem selected_swapped_order [NeZero m] (n t : Fin m) (hnt : t < n)
    {j l : Fin k} (hjl : ((Equiv.swap α β).trans τ) j < ((Equiv.swap α β).trans τ) l) :
    blockRank τ α β m j (selection α β n t j) <
      blockRank τ α β m l (selection α β n t l) := by
  rcases adjacent_swap_order_cases τ α β hαβ hadj hjl with hp | ⟨h, hp⟩
  · rcases hp with ⟨hjb, hla⟩
    subst j
    subst l
    simpa only [selection, ite_true, ite_eq_right hαβ.symm] using
      (blockRank_right_lt_left_iff τ α β hαβ n t).mpr hnt
  · exact blockRank_lt_of_order τ α β hαβ hadj _ _ h hp

end Rank

/-- The cluster with a given block rank: four successive terms of the increasing
sequence `e`. -/
def block (e : ℕ → ℕ) (τ : Equiv.Perm (Fin k)) (α β : Fin k) (m : ℕ)
    (g : Σ _ : Fin k, Fin m) (p : Fin 4) : ℕ :=
  e (4 * blockRank τ α β m g.1 g.2 + p.val)

theorem block_strictMono (e : ℕ → ℕ) (he : StrictMono e)
    (τ : Equiv.Perm (Fin k)) (α β : Fin k) (m : ℕ) (g : Σ _ : Fin k, Fin m) :
    StrictMono (block e τ α β m g) := by
  intro p q hpq
  apply he
  change p.val < q.val at hpq
  omega

theorem block_lt_of_rank (e : ℕ → ℕ) (he : StrictMono e)
    (τ : Equiv.Perm (Fin k)) (α β : Fin k) {m : ℕ}
    (g h : Σ _ : Fin k, Fin m)
    (hgh : blockRank τ α β m g.1 g.2 < blockRank τ α β m h.1 h.2) (p q : Fin 4) :
    block e τ α β m g p < block e τ α β m h q := by
  apply he
  omega

theorem block_coordinates_injective (e : ℕ → ℕ) (he : StrictMono e)
    (τ : Equiv.Perm (Fin k)) (α β : Fin k) (hαβ : α ≠ β)
    (hadj : (τ β).val = (τ α).val + 1) (m : ℕ) :
    Function.Injective (fun t : (Σ _ : Fin k, Fin m) × Fin 4 =>
      block e τ α β m t.1 t.2) := by
  rintro ⟨⟨j, n⟩, p⟩ ⟨⟨l, t⟩, q⟩ h
  have heq := he.injective h
  change 4 * blockRank τ α β m j n + p.val = 4 * blockRank τ α β m l t + q.val at heq
  have hr : blockRank τ α β m j n = blockRank τ α β m l t := by omega
  have hp : p = q := Fin.ext (by omega)
  have hjn : (j, n) = (l, t) := blockRank_injective τ α β hαβ hadj hr
  rcases Prod.mk.inj hjn with ⟨rfl, rfl⟩
  subst q
  rfl

theorem block_separated (e : ℕ → ℕ) (he : StrictMono e)
    (τ : Equiv.Perm (Fin k)) (α β : Fin k) (hαβ : α ≠ β)
    (hadj : (τ β).val = (τ α).val + 1) (m : ℕ)
    (g h : Σ _ : Fin k, Fin m) (hgh : g ≠ h) :
    (∀ p q, block e τ α β m g p < block e τ α β m h q) ∨
      (∀ p q, block e τ α β m h p < block e τ α β m g q) := by
  have hr : blockRank τ α β m g.1 g.2 ≠ blockRank τ α β m h.1 h.2 := by
    intro hr
    have heq : (g.1, g.2) = (h.1, h.2) := blockRank_injective τ α β hαβ hadj hr
    cases g with | mk j n =>
      cases h with | mk l t =>
        rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact hgh rfl
  rcases lt_or_gt_of_ne hr with hr | hr
  · exact Or.inl (block_lt_of_rank e he τ α β g h hr)
  · exact Or.inr (block_lt_of_rank e he τ α β h g hr)

theorem family_input_ternary (e : ℕ → ℕ) (he : StrictMono e)
    (τ : Equiv.Perm (Fin k)) (α β : Fin k) (hαβ : α ≠ β)
    (hadj : (τ β).val = (τ α).val + 1) (m : ℕ)
    (w : Fin 4 → L) (hw : ∀ p, w p = 0 ∨ w p = 1 ∨ w p = -1)
    (j : Fin k) (x : ℕ) :
    (∑ n : Fin m, clusterInput w (block e τ α β m ⟨j, n⟩)) x = 0 ∨
      (∑ n : Fin m, clusterInput w (block e τ α β m ⟨j, n⟩)) x = 1 ∨
      (∑ n : Fin m, clusterInput w (block e τ α β m ⟨j, n⟩)) x = -1 := by
  apply sum_clusterInput_ternary _ _ w hw x
  rintro ⟨n, p⟩ ⟨t, q⟩ h
  have hinj := block_coordinates_injective e he τ α β hαβ hadj m
  have hpair : ((⟨j, n⟩ : Σ _ : Fin k, Fin m), p) = (⟨j, t⟩, q) := hinj h
  have hn : n = t := congrArg (fun z : (Σ _ : Fin k, Fin m) × Fin 4 => z.1.2) hpair
  have hp : p = q := congrArg (fun z : (Σ _ : Fin k, Fin m) × Fin 4 => z.2) hpair
  exact Prod.ext hn hp

end StaircaseClusters

/-- Lemma B.12 for given interlaced families: if the support dimension of the single
vector ω built from them is at most `d`, the two cluster values agree. -/
theorem cluster_staircase_of_families (Ψ : ClusterMap L k) (H : Set ℕ)
    (hpattern : ∀ (z z' : Fin 3 × Fin k → ℕ),
      (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
      (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
      clusterCoefficientTuple Ψ z = clusterCoefficientTuple Ψ z')
    (d : ℕ) (α β : Fin k) (C : (Σ _ : Fin k, Fin (d + 2)) → Fin 4 → ℕ)
    (hmono : ∀ g, StrictMono (C g)) (hCH : ∀ g p, C g p ∈ H)
    (hsep : ∀ g h, g ≠ h → (∀ p q, C g p < C h q) ∨ (∀ p q, C h p < C g q))
    (τ : Equiv.Perm (Fin k)) (A B : Fin k → Fin 4 → ℕ)
    (hA : ∀ j, StrictMono (A j)) (hB : ∀ j, StrictMono (B j))
    (hAH : ∀ j p, A j p ∈ H) (hBH : ∀ j p, B j p ∈ H)
    (hordA : ∀ j l, τ j < τ l → ∀ p q, A j p < A l q)
    (hordB : ∀ j l, ((Equiv.swap α β).trans τ) j < ((Equiv.swap α β).trans τ) l →
      ∀ p q, B j p < B l q)
    (hupper : ∀ n t : Fin (d + 2), n ≤ t → ∀ j l, τ j < τ l → ∀ p q,
      C ⟨j, StaircaseClusters.selection α β n t j⟩ p <
        C ⟨l, StaircaseClusters.selection α β n t l⟩ q)
    (hlower : ∀ n t : Fin (d + 2), t < n → ∀ j l,
      ((Equiv.swap α β).trans τ) j < ((Equiv.swap α β).trans τ) l → ∀ p q,
      C ⟨j, StaircaseClusters.selection α β n t j⟩ p <
        C ⟨l, StaircaseClusters.selection α β n t l⟩ q)
    (hbound : exteriorSupportDim
      (Ψ (fun j => ∑ n : Fin (d + 2), clusterInput clusterOperatorWeight (C ⟨j, n⟩))
        (fun j => ∑ n : Fin (d + 2), clusterInput clusterVectorWeight (C ⟨j, n⟩))) ≤ d) :
    clusterValue Ψ A = clusterValue Ψ B := by
  classical
  let ω := Ψ (fun j => ∑ n : Fin (d + 2), clusterInput clusterOperatorWeight (C ⟨j, n⟩))
    (fun j => ∑ n : Fin (d + 2), clusterInput clusterVectorWeight (C ⟨j, n⟩))
  let M : Matrix (Fin (d + 2)) (Fin (d + 2)) L := fun n t =>
    determinantArray ω (fun j => C ⟨j, StaircaseClusters.selection α β n t j⟩ 0)
  have hM : M = staircaseMatrix (clusterValue Ψ A) (clusterValue Ψ B) (d + 2) := by
    ext n t
    change determinantArray ω _ = if n ≤ t then clusterValue Ψ A else clusterValue Ψ B
    by_cases hnt : n ≤ t
    · rw [ite_eq_left hnt]
      exact cluster_family_cancellation_of_order Ψ H hpattern C hmono hCH hsep
        (StaircaseClusters.selection α β n t) A hA hAH τ (hupper n t hnt) hordA
    · rw [ite_eq_right hnt]
      exact cluster_family_cancellation_of_order Ψ H hpattern C hmono hCH hsep
        (StaircaseClusters.selection α β n t) B hB hBH ((Equiv.swap α β).trans τ)
        (hlower n t (lt_of_not_ge hnt)) hordB
  let rows : Fin (d + 2) → ℕ := fun n => C ⟨α, n⟩ 0
  let columns : Fin (d + 2) → Fin k → ℕ := fun t j =>
    C ⟨j, StaircaseClusters.selection α β 0 t j⟩ 0
  have hflat : M = Matrix.of (fun n t =>
      determinantArray ω (Function.update (columns t) α (rows n))) := by
    ext n t
    change determinantArray ω _ = determinantArray ω _
    apply congrArg (determinantArray ω)
    funext j
    by_cases hj : j = α
    · subst j
      simp [StaircaseClusters.selection, rows]
    · simp [StaircaseClusters.selection, columns, hj]
  apply staircaseMatrix_letters_eq_of_rank_le _ _ d
  rw [← hM, hflat]
  exact (determinantArray_update_rank_le ω α rows columns).trans hbound

/-- Lemma B.12: χ(τ) = χ(τ') for an adjacent exchange, assuming a uniform bound `d` on
the support dimension of Ψ(u; v) for finitely supported inputs with entries in
`{0,1,-1}`. -/
theorem clusterValue_adjacent_eq (Ψ : ClusterMap L k) (H : Set ℕ) (hH : H.Infinite)
    (hpattern : ∀ (z z' : Fin 3 × Fin k → ℕ),
      (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
      (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
      clusterCoefficientTuple Ψ z = clusterCoefficientTuple Ψ z')
    (d : ℕ) (hbound : ∀ (u v : Fin k → ℕ →₀ L),
      (∀ j x, u j x = 0 ∨ u j x = 1 ∨ u j x = -1) →
      (∀ j x, v j x = 0 ∨ v j x = 1 ∨ v j x = -1) → exteriorSupportDim (Ψ u v) ≤ d)
    (τ : Equiv.Perm (Fin k)) (α β : Fin k) (hαβ : α ≠ β)
    (hadj : (τ β).val = (τ α).val + 1) (A B : Fin k → Fin 4 → ℕ)
    (hA : ∀ j, StrictMono (A j)) (hB : ∀ j, StrictMono (B j))
    (hAH : ∀ j p, A j p ∈ H) (hBH : ∀ j p, B j p ∈ H)
    (hordA : ∀ j l, τ j < τ l → ∀ p q, A j p < A l q)
    (hordB : ∀ j l, ((Equiv.swap α β).trans τ) j < ((Equiv.swap α β).trans τ) l →
      ∀ p q, B j p < B l q) :
    clusterValue Ψ A = clusterValue Ψ B := by
  classical
  obtain ⟨e, he, heH⟩ := exists_strictMono_in_infinite_set H hH
  let C := StaircaseClusters.block e τ α β (d + 2)
  apply cluster_staircase_of_families Ψ H hpattern d α β C
    (StaircaseClusters.block_strictMono e he τ α β (d + 2))
    (fun g p => heH _) (StaircaseClusters.block_separated e he τ α β hαβ hadj (d + 2))
    τ A B hA hB hAH hBH hordA hordB
  · intro n t hnt j l hjl p q
    exact StaircaseClusters.block_lt_of_rank e he τ α β _ _
      (StaircaseClusters.selected_order τ α β hαβ hadj n t hnt hjl) p q
  · intro n t hnt j l hjl p q
    exact StaircaseClusters.block_lt_of_rank e he τ α β _ _
      (StaircaseClusters.selected_swapped_order τ α β hαβ hadj n t hnt hjl) p q
  · apply hbound
    · intro j x
      apply StaircaseClusters.family_input_ternary e he τ α β hαβ hadj (d + 2)
        clusterOperatorWeight _ j x
      intro p
      fin_cases p <;> simp [clusterOperatorWeight]
    · intro j x
      apply StaircaseClusters.family_input_ternary e he τ α β hαβ hadj (d + 2)
        clusterVectorWeight _ j x
      intro p
      fin_cases p <;> simp [clusterVectorWeight]

end AlternatingAnalytic
