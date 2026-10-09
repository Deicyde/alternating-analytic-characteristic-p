import AlternatingAnalytic.Algebra.FullPolarization
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Grouping the expansion of a diagonal by word orbits

The orbit of a word `a : Fin d → J` is the set of its distinct rearrangements. We choose one
representative per orbit and give it the sum of `M` over the orbit as coefficient; other words
get coefficient zero. Expanding `M (fun _ => ∑ j ∈ s, x j • b j)` in these coefficients needs
no factorial. Over an infinite field, every coefficient lies in any submodule containing the
diagonal of `M`. The coefficient lifts of Theorem 4.5 on c₀ and ℓ¹ use this grouping.
-/

noncomputable section

open scoped BigOperators Classical

namespace FiniteWord

section

variable {J : Type*} {d : ℕ}

/-- The finite set of distinct rearrangements of a word. -/
def wordOrbit (a : Fin d → J) : Finset (Fin d → J) := by
  classical
  exact Finset.univ.image (fun σ : Equiv.Perm (Fin d) => a ∘ σ)

theorem mem_wordOrbit_iff {a u : Fin d → J} :
    u ∈ wordOrbit a ↔ ∃ σ : Equiv.Perm (Fin d), a ∘ σ = u := by
  classical
  simp [wordOrbit]

@[simp]
theorem mem_wordOrbit_self (a : Fin d → J) : a ∈ wordOrbit a := by
  exact mem_wordOrbit_iff.mpr ⟨Equiv.refl _, rfl⟩

theorem mem_wordOrbit_symm {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    a ∈ wordOrbit u := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp h
  apply mem_wordOrbit_iff.mpr
  refine ⟨σ.symm, ?_⟩
  funext i
  simp

theorem mem_wordOrbit_trans {a u v : Fin d → J}
    (hu : u ∈ wordOrbit a) (hv : v ∈ wordOrbit u) : v ∈ wordOrbit a := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp hu
  obtain ⟨τ, rfl⟩ := mem_wordOrbit_iff.mp hv
  exact mem_wordOrbit_iff.mpr ⟨τ.trans σ, rfl⟩

theorem wordOrbit_eq_of_mem {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    wordOrbit u = wordOrbit a := by
  ext v
  exact ⟨mem_wordOrbit_trans h, mem_wordOrbit_trans (mem_wordOrbit_symm h)⟩

theorem wordOrbit_nonempty (a : Fin d → J) : (wordOrbit a).Nonempty :=
  ⟨a, mem_wordOrbit_self a⟩

/-- A representative of the orbit of `a`, depending only on the orbit. -/
def wordRepresentative (a : Fin d → J) : Fin d → J :=
  (wordOrbit_nonempty a).choose

theorem wordRepresentative_mem (a : Fin d → J) :
    wordRepresentative a ∈ wordOrbit a :=
  (wordOrbit_nonempty a).choose_spec

theorem wordRepresentative_eq_of_mem {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    wordRepresentative u = wordRepresentative a := by
  unfold wordRepresentative
  congr 1
  rw [wordOrbit_eq_of_mem h]

@[simp]
theorem wordRepresentative_idempotent (a : Fin d → J) :
    wordRepresentative (wordRepresentative a) = wordRepresentative a :=
  wordRepresentative_eq_of_mem (wordRepresentative_mem a)

@[simp]
theorem wordOrbit_representative (a : Fin d → J) :
    wordOrbit (wordRepresentative a) = wordOrbit a :=
  wordOrbit_eq_of_mem (wordRepresentative_mem a)

theorem card_wordOrbit_le (a : Fin d → J) : (wordOrbit a).card ≤ d.factorial := by
  classical
  calc
    (wordOrbit a).card ≤ (Finset.univ : Finset (Equiv.Perm (Fin d))).card :=
      Finset.card_image_le
    _ = d.factorial := by simp [Fintype.card_perm]

theorem prod_eq_of_mem_wordOrbit {R : Type*} [CommMonoid R]
    (x : J → R) {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    (∏ i, x (u i)) = ∏ i, x (a i) := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp h
  exact Equiv.prod_comp σ (fun i => x (a i))

theorem forall_mem_of_mem_wordOrbit {s : Finset J} {a u : Fin d → J}
    (ha : ∀ i, a i ∈ s) (h : u ∈ wordOrbit a) : ∀ i, u i ∈ s := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp h
  exact fun i => ha (σ i)

@[simp]
theorem wordOrbit_comp_perm (a : Fin d → J) (σ : Equiv.Perm (Fin d)) :
    wordOrbit (a ∘ σ) = wordOrbit a :=
  wordOrbit_eq_of_mem (mem_wordOrbit_iff.mpr ⟨σ, rfl⟩)

@[simp]
theorem wordRepresentative_comp_perm (a : Fin d → J) (σ : Equiv.Perm (Fin d)) :
    wordRepresentative (a ∘ σ) = wordRepresentative a :=
  wordRepresentative_eq_of_mem (mem_wordOrbit_iff.mpr ⟨σ, rfl⟩)

theorem wordRepresentative_eq_iff_mem_wordOrbit {a u : Fin d → J} :
    wordRepresentative u = wordRepresentative a ↔ u ∈ wordOrbit a := by
  constructor
  · intro h
    have hu : u ∈ wordOrbit (wordRepresentative u) :=
      mem_wordOrbit_symm (wordRepresentative_mem u)
    rw [h, wordOrbit_representative] at hu
    exact hu
  · exact wordRepresentative_eq_of_mem

end

section

variable {J : Type*} {d : ℕ}

/-- The number of coordinates carrying a given label. -/
def wordMultiplicity (a : Fin d → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i = j)).card

@[simp]
theorem wordMultiplicity_comp_perm (a : Fin d → J) (σ : Equiv.Perm (Fin d)) :
    wordMultiplicity (a ∘ σ) = wordMultiplicity a := by
  classical
  funext j
  exact Finset.card_equiv σ (by simp)

theorem wordMultiplicity_eq_iff_exists_perm (u a : Fin d → J) :
    wordMultiplicity u = wordMultiplicity a ↔ ∃ σ : Equiv.Perm (Fin d), a ∘ σ = u := by
  classical
  constructor
  · intro h
    let e (j : J) : { i : Fin d // u i = j } ≃ { i : Fin d // a i = j } :=
      Fintype.equivOfCardEq (by simpa [Fintype.card_subtype, wordMultiplicity] using congrFun h j)
    exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩
  · rintro ⟨σ, rfl⟩
    exact wordMultiplicity_comp_perm a σ

@[simp]
theorem selectionType_eq_wordMultiplicity [Fintype J] (a : Fin d → J) :
    Polarization.selectionType a = wordMultiplicity a := rfl

/-- Two words have the same multiplicities iff they lie in the same orbit. -/
theorem wordMultiplicity_eq_iff_mem_wordOrbit (u a : Fin d → J) :
    wordMultiplicity u = wordMultiplicity a ↔ u ∈ wordOrbit a := by
  rw [wordMultiplicity_eq_iff_exists_perm, mem_wordOrbit_iff]

/-- For finite `J`, `selectionType` fibers are word orbits. -/
theorem selectionType_eq_iff_mem_wordOrbit [Fintype J] (u a : Fin d → J) :
    Polarization.selectionType u = Polarization.selectionType a ↔ u ∈ wordOrbit a :=
  wordMultiplicity_eq_iff_mem_wordOrbit u a

/-- The orbit of `a` is the set of words with the same `selectionType`. -/
theorem wordOrbit_eq_selectionType_fiber [Fintype J] (a : Fin d → J) :
    wordOrbit a = Finset.univ.filter
      (fun u => Polarization.selectionType u = Polarization.selectionType a) := by
  classical
  ext u
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (selectionType_eq_iff_mem_wordOrbit u a).symm

end

section

variable {J J' : Type*} {d : ℕ}

/-- Relabeling commutes with taking orbits. -/
theorem wordOrbit_map (f : J → J') (a : Fin d → J) :
    (wordOrbit a).image (fun u => f ∘ u) = wordOrbit (f ∘ a) := by
  classical
  simp only [wordOrbit, Finset.image_image, Function.comp_assoc]
  rfl

section Algebra

variable {K E Z : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup Z] [Module K Z]

/-- The orbit sum is the grouped sum `sumOfType` at the multiplicities of `a`. -/
theorem sum_wordOrbit_eq_sumOfType [Fintype J]
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E) (a : Fin d → J) :
    (∑ u ∈ wordOrbit a, M (fun i => b (u i))) =
      M.sumOfType b (Polarization.selectionType a) := by
  classical
  rw [wordOrbit_eq_selectionType_fiber]
  rfl

/-- Over an infinite field, if the diagonal of `M` lies in `W` then so does every grouped sum.
Proved by polarization in the quotient `Z ⧸ W`. -/
theorem sumOfType_mem [Infinite K] [Fintype J]
    (W : Submodule K Z) (M : MultilinearMap K (fun _ : Fin d => E) Z)
    (b : J → E) (hM : ∀ x, M (fun _ => x) ∈ W) (α : J → ℕ) :
    M.sumOfType b α ∈ W := by
  classical
  have h := MultilinearMap.sumOfType_eq_of_diagonal_eq
    (W.mkQ.compMultilinearMap M) 0
    (fun x => by simpa using (Submodule.Quotient.mk_eq_zero W).mpr (hM x)) b α
  apply (Submodule.Quotient.mk_eq_zero W).mp
  simpa [MultilinearMap.sumOfType, ← Submodule.mkQ_apply, map_sum] using h

/-- Over an infinite field, if the diagonal of `M` lies in `W` then so does every orbit sum.
The label type `J` may be infinite, since a word uses finitely many labels. -/
theorem sum_wordOrbit_mem [Infinite K]
    (W : Submodule K Z) (M : MultilinearMap K (fun _ : Fin d => E) Z)
    (b : J → E) (hM : ∀ x, M (fun _ => x) ∈ W) (a : Fin d → J) :
    (∑ u ∈ wordOrbit a, M (fun i => b (u i))) ∈ W := by
  classical
  let s : Finset J := Finset.univ.image a
  let a' : Fin d → s := fun i => ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hi : Function.Injective (fun u : Fin d → s => (Subtype.val ∘ u : Fin d → J)) := by
    intro u v h
    funext i
    exact Subtype.ext (congrFun h i)
  have he : (∑ u ∈ wordOrbit a, M (fun i => b (u i))) =
      ∑ u ∈ wordOrbit a', M (fun i => b (u i)) := by
    change (∑ u ∈ wordOrbit (Subtype.val ∘ a'), M (fun i => b (u i))) = _
    rw [← wordOrbit_map, Finset.sum_image hi.injOn]
    rfl
  rw [he, sum_wordOrbit_eq_sumOfType M (fun j : s => b j) a']
  exact sumOfType_mem W M (fun j : s => b j) hM _

end Algebra

end

section

variable {K J E Z : Type*} {d : ℕ}
  [Field K] [AddCommGroup E] [Module K E] [AddCommGroup Z] [Module K Z]

/-- The orbit sum at the chosen representative, and zero at other words. -/
def groupedCoefficient (M : MultilinearMap K (fun _ : Fin d => E) Z)
    (b : J → E) (a : Fin d → J) : Z := by
  classical
  exact if wordRepresentative a = a then
    ∑ u ∈ wordOrbit a, M (fun i => b (u i)) else 0

@[simp]
theorem groupedCoefficient_of_representative
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    {a : Fin d → J} (ha : wordRepresentative a = a) :
    groupedCoefficient M b a = ∑ u ∈ wordOrbit a, M (fun i => b (u i)) := by
  classical
  simp [groupedCoefficient, ha]

@[simp]
theorem groupedCoefficient_of_not_representative
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    {a : Fin d → J} (ha : wordRepresentative a ≠ a) :
    groupedCoefficient M b a = 0 := by
  classical
  simp [groupedCoefficient, ha]

/-- At the representative, the grouped coefficient is the orbit sum. -/
@[simp]
theorem groupedCoefficient_representative
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E) (a : Fin d → J) :
    groupedCoefficient M b (wordRepresentative a) =
      ∑ u ∈ wordOrbit a, M (fun i => b (u i)) := by
  rw [groupedCoefficient_of_representative M b (wordRepresentative_idempotent a),
    wordOrbit_representative]

private theorem representative_fiber_of_fixed
    (S : Finset (Fin d → J))
    (hS : ∀ a ∈ S, ∀ u ∈ wordOrbit a, u ∈ S)
    {a : Fin d → J} (haS : a ∈ S) (ha : wordRepresentative a = a) :
    S.filter (fun u => wordRepresentative u = a) = wordOrbit a := by
  classical
  ext u
  simp only [Finset.mem_filter]
  constructor
  · intro hu
    exact mem_wordOrbit_symm (hu.2 ▸ wordRepresentative_mem u)
  · intro hu
    exact ⟨hS a haS u hu, (wordRepresentative_eq_of_mem hu).trans ha⟩

private theorem representative_fiber_of_not_fixed
    (S : Finset (Fin d → J)) {a : Fin d → J} (ha : wordRepresentative a ≠ a) :
    S.filter (fun u => wordRepresentative u = a) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  apply ha
  have hu' := (Finset.mem_filter.mp hu).2
  rw [← hu', wordRepresentative_idempotent]

private theorem sum_groupedCoefficient_of_orbit_closed
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    (S : Finset (Fin d → J))
    (hS : ∀ a ∈ S, ∀ u ∈ wordOrbit a, u ∈ S) (x : J → K) :
    ∑ a ∈ S, (∏ i, x (a i)) • groupedCoefficient M b a =
      ∑ a ∈ S, (∏ i, x (a i)) • M (fun i => b (a i)) := by
  classical
  have hmaps : ∀ a ∈ S, wordRepresentative a ∈ S :=
    fun a ha => hS a ha _ (wordRepresentative_mem a)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => (∏ i, x (a i)) • M (fun i => b (a i)))]
  apply Finset.sum_congr rfl
  intro a haS
  by_cases ha : wordRepresentative a = a
  · rw [representative_fiber_of_fixed S hS haS ha,
      groupedCoefficient_of_representative M b ha, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [prod_eq_of_mem_wordOrbit x hu]
  · rw [representative_fiber_of_not_fixed S ha,
      groupedCoefficient_of_not_representative M b ha]
    simp

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

/-- Expansion of the diagonal at a finite combination in terms of grouped coefficients. -/
theorem finite_diagonal_grouping
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    (s : Finset J) (x : J → K) :
    M (fun _ => ∑ j ∈ s, x j • b j) =
      ∑ a : Fin d → s,
        (∏ i, x (a i)) • groupedCoefficient M b (fun i => (a i : J)) := by
  classical
  rw [M.map_sum_finset (fun _ j => x j • b j) (fun _ => s)]
  have hS : ∀ a ∈ Fintype.piFinset (fun _ : Fin d => s),
      ∀ u ∈ wordOrbit a, u ∈ Fintype.piFinset (fun _ : Fin d => s) := by
    intro a ha u hu
    exact Fintype.mem_piFinset.mpr
      (forall_mem_of_mem_wordOrbit (Fintype.mem_piFinset.mp ha) hu)
  calc
    _ = ∑ a ∈ Fintype.piFinset (fun _ : Fin d => s),
        (∏ i, x (a i)) • M (fun i => b (a i)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact M.map_smul_univ (fun i => x (a i)) (fun i => b (a i))
    _ = ∑ a ∈ Fintype.piFinset (fun _ : Fin d => s),
        (∏ i, x (a i)) • groupedCoefficient M b a :=
      (sum_groupedCoefficient_of_orbit_closed M b _ hS x).symm
    _ = _ := sum_piFinset_eq_sum_subtype s _

end

section

variable {K J E Z : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup Z] [Module K Z] {d : ℕ}

/-- Over an infinite field, every grouped coefficient lies in any submodule containing
the diagonal. -/
theorem groupedCoefficient_mem [Infinite K]
    (W : Submodule K Z) (M : MultilinearMap K (fun _ : Fin d => E) Z)
    (b : J → E) (hM : ∀ x, M (fun _ => x) ∈ W) (a : Fin d → J) :
    groupedCoefficient M b a ∈ W := by
  classical
  by_cases ha : wordRepresentative a = a
  · rw [groupedCoefficient_of_representative M b ha]
    exact sum_wordOrbit_mem W M b hM a
  · rw [groupedCoefficient_of_not_representative M b ha]
    exact W.zero_mem

/-- The orbit size bound `d!`, membership of the coefficients in `W`, and the finite
expansion of the diagonal. -/
theorem finite_word_grouping_spec [Infinite K]
    (d : ℕ) (W : Submodule K Z)
    (M : MultilinearMap K (fun _ : Fin d => E) Z)
    (b : J → E) (hM : ∀ x, M (fun _ => x) ∈ W) :
    (∀ a : Fin d → J,
      wordRepresentative a ∈ wordOrbit a ∧ (wordOrbit a).card ≤ d.factorial) ∧
    (∀ a : Fin d → J, groupedCoefficient M b a ∈ W) ∧
    (∀ (s : Finset J) (x : J → K),
      M (fun _ => ∑ j ∈ s, x j • b j) =
        ∑ a : Fin d → s,
          (∏ i, x (a i)) • groupedCoefficient M b (fun i => (a i : J))) := by
  exact ⟨fun a => ⟨wordRepresentative_mem a, card_wordOrbit_le a⟩,
    groupedCoefficient_mem W M b hM, finite_diagonal_grouping M b⟩

end

end FiniteWord
