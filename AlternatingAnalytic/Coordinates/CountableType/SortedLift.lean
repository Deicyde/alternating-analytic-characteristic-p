import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# The sorted lift on a basis with bounded coordinates

Let `b` be a Hamel basis of a normed space `M` over a nonarchimedean field `K`, indexed by a
linear order, whose coordinates satisfy `‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖`. For a scalar
`k`-linear form `g` on `M`, the sorted lift
`S g (y₁, …, y_k) = ∑_{i₁ < ⋯ < i_k} g (b_{i₁}, …, b_{i_k}) ∏ₐ b.coord iₐ yₐ`
is a finitely supported sum. It defines a bounded linear operator `sortedLift` of norm at most
`C ^ k`, and unnormalized alternatization is a left inverse of `S` on alternating forms
(`alternatization_sortedLift`), in every characteristic. This is the sorted-lift step in the
proof of Proposition I.1.
-/

noncomputable section

open scoped BigOperators

namespace AlternatingAnalytic.CountableType

variable {K M ι : Type*} [NontriviallyNormedField K] [NormedAddCommGroup M] [NormedSpace K M]
  [LinearOrder ι]

/-- The coordinate monomial `y ↦ ∏ₐ b.coord (e a) (y a)` of an increasing index tuple. -/
def coordMonomial (b : Module.Basis ι K M) (k : ℕ) (e : Fin k ↪o ι) :
    MultilinearMap K (fun _ : Fin k => M) K :=
  (MultilinearMap.mkPiAlgebra K (Fin k) K).compLinearMap fun a => b.coord (e a)

theorem coordMonomial_apply (b : Module.Basis ι K M) (k : ℕ) (e : Fin k ↪o ι)
    (y : Fin k → M) : coordMonomial b k e y = ∏ a, b.coord (e a) (y a) := by
  simp [coordMonomial, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- Only finitely many coordinate monomials are nonzero at a given tuple. -/
theorem coordMonomial_hasFiniteSupport (b : Module.Basis ι K M) (k : ℕ)
    (c : (Fin k ↪o ι) → K) (y : Fin k → M) :
    Function.HasFiniteSupport fun e : Fin k ↪o ι => c e * coordMonomial b k e y := by
  classical
  have hfin : ((fun e : Fin k ↪o ι => (e : Fin k → ι)) ⁻¹'
      Set.pi Set.univ fun a => ((b.repr (y a)).support : Set ι)).Finite :=
    (Set.Finite.pi fun a => (b.repr (y a)).support.finite_toSet).preimage
      (DFunLike.coe_injective.injOn)
  refine hfin.subset fun e he => ?_
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Finset.mem_coe,
    Finsupp.mem_support_iff, forall_true_left]
  intro a ha
  apply he
  simp only [coordMonomial_apply, Module.Basis.coord_apply]
  rw [Finset.prod_eq_zero (Finset.mem_univ a) ha, mul_zero]

theorem coordMonomial_summable (b : Module.Basis ι K M) (k : ℕ)
    (c : (Fin k ↪o ι) → K) (y : Fin k → M) :
    Summable fun e : Fin k ↪o ι => c e * coordMonomial b k e y :=
  summable_of_hasFiniteSupport (coordMonomial_hasFiniteSupport b k c y)

/-- The sorted lift of a scalar multilinear form, as an algebraic multilinear map. -/
def sortedLiftMultilinear (b : Module.Basis ι K M) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) :
    MultilinearMap K (fun _ : Fin k => M) K where
  toFun y := ∑' e : Fin k ↪o ι, g (fun a => b (e a)) * coordMonomial b k e y
  map_update_add' y a u v := by
    simp only [MultilinearMap.map_update_add, mul_add]
    exact (coordMonomial_summable b k _ _).tsum_add (coordMonomial_summable b k _ _)
  map_update_smul' y a r u := by
    simp only [MultilinearMap.map_update_smul, smul_eq_mul]
    rw [← tsum_mul_left]
    exact tsum_congr fun e => by ring

theorem sortedLiftMultilinear_apply (b : Module.Basis ι K M) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) (y : Fin k → M) :
    sortedLiftMultilinear b k g y =
      ∑' e : Fin k ↪o ι, g (fun a => b (e a)) * ∏ a, b.coord (e a) (y a) := by
  simp only [sortedLiftMultilinear, MultilinearMap.coe_mk, coordMonomial_apply]

variable [IsUltrametricDist K]

theorem norm_sortedLiftMultilinear_le (b : Module.Basis ι K M) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) (y : Fin k → M) :
    ‖sortedLiftMultilinear b k g y‖ ≤ C ^ k * ‖g‖ * ∏ a, ‖y a‖ := by
  rw [sortedLiftMultilinear_apply]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
  intro e
  rw [norm_mul, norm_prod]
  calc ‖g (fun a => b (e a))‖ * ∏ a, ‖b.coord (e a) (y a)‖
      ≤ (‖g‖ * ∏ a, ‖b (e a)‖) * ∏ a, ‖b.coord (e a) (y a)‖ :=
        mul_le_mul_of_nonneg_right (g.le_opNorm _) (by positivity)
    _ = ‖g‖ * ∏ a, (‖b.coord (e a) (y a)‖ * ‖b (e a)‖) := by
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ ‖g‖ * ∏ a, (C * ‖y a‖) :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod₀ (fun a _ => by positivity) (fun a _ => hb _ _)) (norm_nonneg _)
    _ = C ^ k * ‖g‖ * ∏ a, ‖y a‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- The sorted lift of a scalar multilinear form, as a continuous multilinear map. -/
def sortedLiftCont (b : Module.Basis ι K M) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) :
    ContinuousMultilinearMap K (fun _ : Fin k => M) K :=
  (sortedLiftMultilinear b k g).mkContinuous (C ^ k * ‖g‖)
    (norm_sortedLiftMultilinear_le b hC hb k g)

/-- The sorted lift `S`, a bounded linear operator on scalar `k`-linear forms of norm at most
`C ^ k`. -/
def sortedLift (b : Module.Basis ι K M) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖) (k : ℕ) :
    ContinuousMultilinearMap K (fun _ : Fin k => M) K →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => M) K :=
  LinearMap.mkContinuous
    { toFun := sortedLiftCont b hC hb k
      map_add' := fun g h => by
        ext y
        simp only [sortedLiftCont, MultilinearMap.coe_mkContinuous,
          _root_.add_apply, sortedLiftMultilinear, MultilinearMap.coe_mk,
          add_mul]
        exact (coordMonomial_summable b k _ _).tsum_add (coordMonomial_summable b k _ _)
      map_smul' := fun r g => by
        ext y
        simp only [sortedLiftCont, MultilinearMap.coe_mkContinuous,
          _root_.smul_apply, sortedLiftMultilinear, MultilinearMap.coe_mk,
          smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        exact tsum_congr fun e => by ring }
    (C ^ k) (fun g => by
      change ‖sortedLiftCont b hC hb k g‖ ≤ C ^ k * ‖g‖
      exact MultilinearMap.mkContinuous_norm_le _ (by positivity) _)

theorem sortedLift_apply (b : Module.Basis ι K M) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) (y : Fin k → M) :
    sortedLift b hC hb k g y =
      ∑' e : Fin k ↪o ι, g (fun a => b (e a)) * ∏ a, b.coord (e a) (y a) :=
  sortedLiftMultilinear_apply b k g y

theorem norm_sortedLift_le (b : Module.Basis ι K M) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖) (k : ℕ) :
    ‖sortedLift b hC hb k‖ ≤ C ^ k :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- On basis tuples, the sorted lift keeps the increasing tuples and kills all others. -/
theorem sortedLift_basis (b : Module.Basis ι K M) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) (t : Fin k → ι) :
    sortedLift b hC hb k g (fun a => b (t a)) =
      if StrictMono t then g (fun a => b (t a)) else 0 := by
  classical
  rw [sortedLift_apply]
  have hterm : ∀ e : Fin k ↪o ι, (∏ a, b.coord (e a) (b (t a))) =
      if ∀ a, t a = e a then 1 else 0 := by
    intro e
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    rw [Fintype.prod_boole]
    congr
  simp_rw [hterm]
  split_ifs with ht
  · rw [tsum_eq_single (OrderEmbedding.ofStrictMono t ht)]
    · simp [OrderEmbedding.coe_ofStrictMono]
    · intro e he
      have : ¬ ∀ a, t a = e a := fun h => he (by ext a; exact (h a).symm)
      simp [this]
  · have : ∀ e : Fin k ↪o ι, ¬ ∀ a, t a = e a := fun e h => ht (by
      have : t = e := funext h
      rw [this]; exact e.strictMono)
    simp [this]

/-- Alternatization of the sorted lift recovers every alternating form. -/
theorem alternatization_sortedLift (b : Module.Basis ι K M) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖) (k : ℕ)
    (g : M [⋀^Fin k]→L[K] K) :
    ContinuousMultilinearMap.alternatization (sortedLift b hC hb k g.toContinuousMultilinearMap)
      = g := by
  classical
  have key :
      (ContinuousMultilinearMap.alternatization (sortedLift b hC hb k
        g.toContinuousMultilinearMap)).toContinuousMultilinearMap.toMultilinearMap =
        g.toContinuousMultilinearMap.toMultilinearMap := by
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro t
    change ContinuousMultilinearMap.alternatization
      (sortedLift b hC hb k g.toContinuousMultilinearMap) (fun a => b (t a)) =
        g (fun a => b (t a))
    rw [ContinuousMultilinearMap.alternatization_apply_apply]
    have hperm : ∀ σ : Equiv.Perm (Fin k),
        sortedLift b hC hb k g.toContinuousMultilinearMap ((fun a => b (t a)) ∘ σ) =
          if StrictMono (t ∘ σ) then g (fun a => b (t (σ a))) else 0 := fun σ =>
      sortedLift_basis b hC hb k _ (t ∘ σ)
    simp_rw [hperm]
    by_cases hinj : Function.Injective t
    · set σ₀ := Tuple.sort t
      have hmono₀ : StrictMono (t ∘ σ₀) :=
        (Tuple.monotone_sort t).strictMono_of_injective (hinj.comp σ₀.injective)
      rw [Finset.sum_eq_single σ₀]
      · simp only [hmono₀, ↓reduceIte]
        have h := g.toAlternatingMap.map_perm (fun a => b (t a)) σ₀
        change g (fun a => b (t (σ₀ a))) = Equiv.Perm.sign σ₀ • g (fun a => b (t a)) at h
        rw [h, smul_smul, Int.units_mul_self, one_smul]
      · intro σ _ hσ
        have : ¬ StrictMono (t ∘ σ) := fun hs => hσ (by
          have heq := Tuple.unique_monotone hs.monotone (Tuple.monotone_sort t)
          ext a
          exact congrArg Fin.val (hinj (congrFun heq a)))
        simp only [this, ↓reduceIte, smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hz : ∀ σ : Equiv.Perm (Fin k), ¬ StrictMono (t ∘ σ) := fun σ hs => hinj (by
        have := hs.injective.comp σ.symm.injective
        simpa [Function.comp_def] using this)
      simp only [hz, ↓reduceIte, smul_zero, Finset.sum_const_zero]
      obtain ⟨a, a', hne, heq⟩ : ∃ a a', a ≠ a' ∧ t a = t a' := by
        simp only [Function.Injective, not_forall] at hinj
        obtain ⟨a, a', h, hne⟩ := hinj
        exact ⟨a, a', hne, h⟩
      exact (g.map_eq_zero_of_eq (fun a => b (t a)) (congrArg b heq) hne).symm
  ext v
  exact congrArg (fun f : MultilinearMap K (fun _ : Fin k => M) K => f v) key

end AlternatingAnalytic.CountableType
