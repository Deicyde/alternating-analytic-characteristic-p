import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Bases
import AlternatingAnalytic.Scalar.ChainGap

/-!
# Chain-limit subspaces of bounded families on the word tree

Let `L` be a set of labels and `List L` the word tree `L^{<ω}`. A `j`-chain sequence is a
sequence of words `s₀, s₁, …` with `s_r ++ [j]` a prefix of `s_{r+1}`. For each label `j` let
`ρ j` be a continuous linear map on a normed space `V`; in applications `ρ j` is an idempotent
whose kernel is the subspace `Σ^j`, so that `ρ j v` measures the distance of `v` to `Σ^j`. The
chain-limit space `chainSpace ρ` consists of the bounded families `x : List L → V` with
`ρ j (x (s n)) → 0` along every `j`-chain sequence `s`. This is the space `E` of Appendix F of
the paper (F.6), with the distance to `Σ^j` replaced by the residual `ρ j`. We show that it is a
closed submodule of `ℓ^∞(List L; V)` containing `c₀`, that it contains every bounded
`ker (ρ j)`-valued family supported on a `j`-chain (by the chain gap lemma, chains with different
labels meet at most once), that it is ultrametric and complete when `V` is, and that it is not
separable as soon as some `ker (ρ j)` is nonzero.
-/

open Filter Topology
open scoped ENNReal

namespace AlternatingAnalytic.ChainSpaces

section Chains

variable {L : Type*}

/-- `s` is a `j`-chain sequence: `s r ++ [j]` is a prefix of `s (r + 1)` for every `r`. -/
def IsChainSeq (j : L) (s : ℕ → List L) : Prop :=
  ∀ r, s r ++ [j] <+: s (r + 1)

theorem IsChainSeq.length_lt {j : L} {s : ℕ → List L} (hs : IsChainSeq j s) (r : ℕ) :
    (s r).length < (s (r + 1)).length := by
  have := (hs r).length_le
  simp only [List.length_append, List.length_singleton] at this
  omega

/-- A chain sequence is injective (word lengths strictly increase). -/
theorem IsChainSeq.injective {j : L} {s : ℕ → List L} (hs : IsChainSeq j s) :
    Function.Injective s :=
  Function.Injective.of_comp (f := List.length) (strictMono_nat_of_lt_succ hs.length_lt).injective

/-- The words of a chain sequence form a chain in the sense of the chain gap lemma. -/
theorem IsChainSeq.isLabelChain {j : L} {s : ℕ → List L} (hs : IsChainSeq j s) :
    ChainGap.IsLabelChain j (Set.range s) :=
  ⟨s, hs, rfl⟩

/-- The words `j^n` form a `j`-chain sequence. -/
theorem isChainSeq_replicate (j : L) : IsChainSeq j (fun n => List.replicate n j) := by
  intro r
  show List.replicate r j ++ [j] <+: List.replicate (r + 1) j
  rw [List.replicate_succ']

/-- A chain with a different label meets a `j`-chain in at most one word, so its words
eventually avoid the `j`-chain. -/
theorem IsChainSeq.eventually_notMem_range {j h : L} (hjh : j ≠ h) {s s' : ℕ → List L}
    (hs : IsChainSeq j s) (hs' : IsChainSeq h s') :
    ∀ᶠ n in atTop, s' n ∉ Set.range s := by
  have hsub := ChainGap.labelChain_inter_subsingleton hjh hs.isLabelChain hs'.isLabelChain
  by_cases hex : ∃ n₀, s' n₀ ∈ Set.range s
  · obtain ⟨n₀, hn₀⟩ := hex
    filter_upwards [eventually_gt_atTop n₀] with n hn hmem
    have := hsub ⟨hmem, n, rfl⟩ ⟨hn₀, n₀, rfl⟩
    exact absurd (hs'.injective this) (ne_of_gt hn)
  · exact Eventually.of_forall fun n hn => hex ⟨n, hn⟩

end Chains

section Space

variable {K : Type*} [NontriviallyNormedField K] {L : Type*}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]

/-- The chain-limit space: bounded families `x` on the word tree with `ρ j (x (s n)) → 0` along
every `j`-chain sequence `s`. -/
def chainSpace (ρ : L → V →L[K] V) : Submodule K (lp (fun _ : List L => V) ∞) where
  carrier := {x | ∀ j s, IsChainSeq j s → Tendsto (fun n => ρ j (x (s n))) atTop (𝓝 0)}
  add_mem' {x y} hx hy j s hs := by
    simpa only [lp.coeFn_add, Pi.add_apply, map_add, add_zero] using (hx j s hs).add (hy j s hs)
  zero_mem' j s hs := by
    simpa only [lp.coeFn_zero, Pi.zero_apply, map_zero] using tendsto_const_nhds
  smul_mem' c x hx j s hs := by
    simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_zero] using
      (hx j s hs).const_smul c

theorem mem_chainSpace {ρ : L → V →L[K] V} {x : lp (fun _ : List L => V) ∞} :
    x ∈ chainSpace ρ ↔
      ∀ j s, IsChainSeq j s → Tendsto (fun n => ρ j (x (s n))) atTop (𝓝 0) :=
  Iff.rfl

/-- The condition along one sequence of words is closed in the sup norm. -/
theorem isClosed_setOf_tendsto_comp (A : V →L[K] V) (s : ℕ → List L) :
    IsClosed {x : lp (fun _ : List L => V) ∞ | Tendsto (fun n => A (x (s n))) atTop (𝓝 0)} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  change Tendsto (fun n => A (x (s n))) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC : 0 < ‖A‖ + 1 := by positivity
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2 / (‖A‖ + 1)) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hy (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_zero_right] at h1 ⊢
  have h2 : ‖A (x (s n)) - A (y (s n))‖ ≤ ‖A‖ * ‖x - y‖ := by
    rw [← map_sub]
    refine (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have := lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) (s n)
    rwa [lp.coeFn_sub, Pi.sub_apply] at this
  have h3 : ‖A‖ * ‖x - y‖ < ε / 2 := by
    rw [dist_eq_norm] at hxy
    calc ‖A‖ * ‖x - y‖ ≤ (‖A‖ + 1) * ‖x - y‖ := by
          gcongr
          linarith
      _ < (‖A‖ + 1) * (ε / 2 / (‖A‖ + 1)) := by gcongr
      _ = ε / 2 := by field_simp
  have h4 := norm_sub_norm_le (A (x (s n))) (A (y (s n)))
  linarith

/-- The chain-limit space is closed. -/
theorem isClosed_chainSpace (ρ : L → V →L[K] V) :
    IsClosed (chainSpace ρ : Set (lp (fun _ : List L => V) ∞)) := by
  have : (chainSpace ρ : Set (lp (fun _ : List L => V) ∞)) =
      ⋂ j, ⋂ s, ⋂ (_ : IsChainSeq j s),
        {x | Tendsto (fun n => ρ j (x (s n))) atTop (𝓝 0)} := by
    ext x
    simp only [Set.mem_iInter, SetLike.mem_coe, mem_chainSpace, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun j => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_setOf_tendsto_comp (ρ j) s

/-- The chain-limit space contains `c₀`. -/
theorem mem_chainSpace_of_tendsto (ρ : L → V →L[K] V) {x : lp (fun _ : List L => V) ∞}
    (hx : Tendsto (fun w => x w) cofinite (𝓝 0)) : x ∈ chainSpace ρ := by
  intro j s hs
  have h1 : Tendsto (fun n => x (s n)) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hx.comp hs.injective.tendsto_cofinite
  simpa only [map_zero, Function.comp_def] using ((ρ j).continuous.tendsto 0).comp h1

/-- **Chain generators.** A bounded family with values in `ker (ρ j)`, supported on the words of
a `j`-chain sequence, lies in the chain-limit space. -/
theorem mem_chainSpace_of_supported (ρ : L → V →L[K] V) {j : L} {s : ℕ → List L}
    (hs : IsChainSeq j s) {y : lp (fun _ : List L => V) ∞} (hker : ∀ w, ρ j (y w) = 0)
    (hsupp : ∀ w, w ∉ Set.range s → y w = 0) : y ∈ chainSpace ρ := by
  intro h s' hs'
  by_cases hjh : j = h
  · subst hjh
    simpa only [hker] using tendsto_const_nhds
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hs.eventually_notMem_range hjh hs'] with n hn
    rw [hsupp _ hn, map_zero]

/-- `ℓ^∞` of an ultrametric normed group is ultrametric. -/
theorem isUltrametricDist_lp_infty {ι : Type*} [IsUltrametricDist V] :
    IsUltrametricDist (lp (fun _ : ι => V) ∞) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
    lp.norm_le_of_forall_le (le_max_of_le_left (norm_nonneg _)) fun i => by
      rw [lp.coeFn_add, Pi.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max (lp.norm_apply_le_norm ENNReal.top_ne_zero x i)
          (lp.norm_apply_le_norm ENNReal.top_ne_zero y i))

theorem isUltrametricDist_chainSpace [IsUltrametricDist V] (ρ : L → V →L[K] V) :
    IsUltrametricDist (chainSpace ρ) := by
  have := isUltrametricDist_lp_infty (V := V) (ι := List L)
  exact IsUltrametricDist.subtype _

theorem completeSpace_chainSpace [CompleteSpace V] (ρ : L → V →L[K] V) :
    CompleteSpace (chainSpace ρ) :=
  (isClosed_chainSpace ρ).completeSpace_coe

/-- The family equal to `v` on the words `j^n`, `n ∈ S`, and zero elsewhere. -/
noncomputable def replicateIndicator (j : L) (v : V) (S : Set ℕ) : lp (fun _ : List L => V) ∞ :=
  ⟨Set.indicator ((fun n => List.replicate n j) '' S) (fun _ => v),
    memℓp_infty ⟨‖v‖, by
      rintro _ ⟨w, rfl⟩
      exact norm_indicator_le_norm_self _ _⟩⟩

theorem replicateIndicator_apply (j : L) (v : V) (S : Set ℕ) (w : List L) :
    replicateIndicator j v S w =
      Set.indicator ((fun n => List.replicate n j) '' S) (fun _ => v) w :=
  rfl

theorem replicateIndicator_mem (ρ : L → V →L[K] V) {j : L} {v : V} (hv : ρ j v = 0)
    (S : Set ℕ) : replicateIndicator j v S ∈ chainSpace ρ := by
  refine mem_chainSpace_of_supported ρ (isChainSeq_replicate j) (fun w => ?_) (fun w hw => ?_)
  · rw [replicateIndicator_apply]
    by_cases h : w ∈ (fun n => List.replicate n j) '' S
    · rw [Set.indicator_of_mem h, hv]
    · rw [Set.indicator_of_notMem h, map_zero]
  · rw [replicateIndicator_apply, Set.indicator_of_notMem]
    rintro ⟨n, -, rfl⟩
    exact hw ⟨n, rfl⟩

theorem norm_le_norm_replicateIndicator_sub (j : L) (v : V) {S S' : Set ℕ} (hSS' : S ≠ S') :
    ‖v‖ ≤ ‖replicateIndicator j v S - replicateIndicator j v S'‖ := by
  obtain ⟨n, hn⟩ : ∃ n, ¬ (n ∈ S ↔ n ∈ S') := by
    by_contra h
    exact hSS' (Set.ext fun n => not_not.1 (not_exists.1 h n))
  have hinj := (isChainSeq_replicate j).injective
  have hmem : ∀ T : Set ℕ, List.replicate n j ∈ (fun n => List.replicate n j) '' T ↔ n ∈ T :=
    fun T => hinj.mem_set_image
  refine le_trans ?_ (lp.norm_apply_le_norm ENNReal.top_ne_zero _ (List.replicate n j))
  rw [lp.coeFn_sub, Pi.sub_apply, replicateIndicator_apply, replicateIndicator_apply]
  by_cases hS : n ∈ S
  · have hS' : n ∉ S' := fun h => hn ⟨fun _ => h, fun _ => hS⟩
    rw [Set.indicator_of_mem ((hmem S).2 hS),
      Set.indicator_of_notMem (fun h => hS' ((hmem S').1 h)), sub_zero]
  · have hS' : n ∈ S' := by
      by_contra h
      exact hn ⟨fun h' => absurd h' hS, fun h' => absurd h' h⟩
    rw [Set.indicator_of_notMem (fun h => hS ((hmem S).1 h)),
      Set.indicator_of_mem ((hmem S').2 hS'), zero_sub, norm_neg]

/-- The chain-limit space is not separable as soon as some `ker (ρ j)` is nonzero: the families
`replicateIndicator j v S`, `S ⊆ ℕ`, are uncountably many and pairwise `‖v‖` apart. -/
theorem not_separableSpace_chainSpace (ρ : L → V →L[K] V) {j : L} {v : V} (hv0 : v ≠ 0)
    (hv : ρ j v = 0) : ¬ TopologicalSpace.SeparableSpace (chainSpace ρ) := by
  intro hsep
  let f : Set ℕ → chainSpace ρ := fun S => ⟨replicateIndicator j v S, replicateIndicator_mem ρ hv S⟩
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hc : Countable (Set ℕ) := by
    refine Pairwise.countable_of_isOpen_disjoint (s := fun S => Metric.ball (f S) (‖v‖ / 2))
      (fun S S' hSS' => ?_) (fun _ => Metric.isOpen_ball)
      (fun S => ⟨f S, Metric.mem_ball_self (by positivity)⟩)
    refine Metric.ball_disjoint_ball ?_
    rw [Subtype.dist_eq, dist_eq_norm]
    have := norm_le_norm_replicateIndicator_sub j v hSS'
    linarith
  obtain ⟨g, hg⟩ := exists_surjective_nat (Set ℕ)
  exact Function.cantor_surjective g hg

end Space

end AlternatingAnalytic.ChainSpaces
