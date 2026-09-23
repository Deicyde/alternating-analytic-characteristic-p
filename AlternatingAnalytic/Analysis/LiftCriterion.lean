/-
Characteristic-free bounded-lift criterion and transfer for precomposition on continuous
alternating maps. No completeness assumptions are used.

Source: round24/charp/lean/Transfer.lean, integrated on 2026-09-23.
Original declaration names in `Round24Transfer` are retained for paper references.
Provenance and verification: planning/charp-paper/planning/integration-manifest.json.
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

open scoped ContDiff

namespace Round24Transfer

/-! ## Part 1. One-variable top-coefficient identification (series-specific form) -/

section Extraction


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The one-variable formal power series of `t ↦ ∑_{r ≤ k} t ^ r • b r`. -/
noncomputable def polySeries (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (k : ℕ) (b : ℕ → Z) :
    FormalMultilinearSeries 𝕜 𝕜 Z :=
  fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (if n ≤ k then b n else 0)

lemma polySeries_apply (k : ℕ) (b : ℕ → Z) (n : ℕ) (m : Fin n → 𝕜) :
    polySeries 𝕜 k b n m = (∏ i, m i) • (if n ≤ k then b n else 0) :=
  ContinuousMultilinearMap.mkPiRing_apply _ _

lemma polySeries_eq_zero_of_gt (k : ℕ) (b : ℕ → Z) {n : ℕ} (hn : k < n) :
    polySeries 𝕜 k b n = 0 := by
  have hb : (if n ≤ k then b n else 0) = 0 := by simp [Nat.not_le.mpr hn]
  rw [polySeries, hb]
  exact ContinuousMultilinearMap.mkPiRing_zero

lemma hasFPowerSeriesAt_polySeries (k : ℕ) (b : ℕ → Z) :
    HasFPowerSeriesAt (fun t : 𝕜 => ∑ r ∈ Finset.range (k + 1), t ^ r • b r)
      (polySeries 𝕜 k b) 0 := by
  have H : HasFiniteFPowerSeriesOnBall
      (fun t : 𝕜 => ∑ r ∈ Finset.range (k + 1), t ^ r • b r) (polySeries 𝕜 k b) 0 (k + 1) ⊤ := by
    refine HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
    · intro m hm
      exact polySeries_eq_zero_of_gt k b (by omega)
    · intro y _
      have : ∀ r ∈ Finset.range (k + 1),
          polySeries 𝕜 k b r (fun _ => y) = y ^ r • b r := by
        intro r hr
        rw [polySeries_apply]
        have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        simp [hrk]
      rw [Finset.sum_congr rfl this]
      simp
  exact H.hasFiniteFPowerSeriesAt.hasFPowerSeriesAt

/-- Shift a power series statement from base point `x₀` to base point `0`, keeping the series. -/
lemma hasFPowerSeriesAt_shift {Q : X → Z} {x₀ : X} {p : FormalMultilinearSeries 𝕜 X Z}
    (hp : HasFPowerSeriesAt Q p x₀) : HasFPowerSeriesAt (fun z => Q (x₀ + z)) p 0 := by
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, { r_le := hr.r_le, r_pos := hr.r_pos,
              hasSum := fun {y} hy => by simpa using hr.hasSum hy }⟩

/-- **Series-specific top-coefficient identification.** If `Q` has the power series `p` at `x₀`,
and along every line through `x₀` the map `Q` is a polynomial of degree `≤ k` with coefficient
functions `B r`, then the `k`-th term of the *given* series `p` has diagonal `B k`. -/
theorem coeff_eq_of_hasFPowerSeriesAt (Q : X → Z) (x₀ : X) (k : ℕ) (B : ℕ → X → Z)
    (hB : ∀ (t : 𝕜) (x : X), Q (x₀ + t • x) = ∑ r ∈ Finset.range (k + 1), t ^ r • B r x)
    (p : FormalMultilinearSeries 𝕜 X Z) (hp : HasFPowerSeriesAt Q p x₀) :
    ∀ x, p k (fun _ => x) = B k x := by
  intro y
  have hp0 : HasFPowerSeriesAt (fun z => Q (x₀ + z)) p 0 := hasFPowerSeriesAt_shift hp
  obtain ⟨u, huapp⟩ : ∃ u : 𝕜 →L[𝕜] X, ∀ t : 𝕜, u t = t • y :=
    ⟨(ContinuousLinearMap.id 𝕜 𝕜).smulRight y, fun _ => rfl⟩
  have hp0' : HasFPowerSeriesAt (fun z => Q (x₀ + z)) p (u 0) := by
    rw [huapp, zero_smul]; exact hp0
  have h1 : HasFPowerSeriesAt ((fun z => Q (x₀ + z)) ∘ u) (p.compContinuousLinearMap u) 0 :=
    hp0'.compContinuousLinearMap
  have h2 : ((fun z => Q (x₀ + z)) ∘ u) =
      fun t : 𝕜 => ∑ r ∈ Finset.range (k + 1), t ^ r • B r y := by
    funext t
    simp only [Function.comp_apply, huapp, hB]
  rw [h2] at h1
  have heq := h1.eq_formalMultilinearSeries (hasFPowerSeriesAt_polySeries k (fun r => B r y))
  have key : (p.compContinuousLinearMap u) k (fun _ => (1 : 𝕜))
      = polySeries 𝕜 k (fun r => B r y) k (fun _ => (1 : 𝕜)) := by rw [heq]
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply, polySeries_apply] at key
  simp only [Function.comp_def, huapp, one_smul, Finset.prod_const_one] at key
  simpa using key

/-- **Ambient form of the extraction (the repaired step (iv) ⇒ (i)).** Let `j : Z →L W` be
injective. If `Q : X → Z` has power series `p` at `x₀` (in `Z`), and the *ambient* identity
`j (Q (x₀ + t • x)) = ∑_{r ≤ k} t ^ r • B r x` holds in `W` with top coefficient
`B k x = j (Qtop x)`, then the `k`-th term of the `Z`-valued series `p` has diagonal `Qtop`. -/
theorem coeff_eq_of_ambient (Q : X → Z) (x₀ : X) (k : ℕ) (B : ℕ → X → W) (j : Z →L[𝕜] W)
    (hj : Function.Injective j) (Qtop : X → Z)
    (hB : ∀ (t : 𝕜) (x : X), j (Q (x₀ + t • x)) = ∑ r ∈ Finset.range (k + 1), t ^ r • B r x)
    (htop : ∀ x, B k x = j (Qtop x))
    (p : FormalMultilinearSeries 𝕜 X Z) (hp : HasFPowerSeriesAt Q p x₀) :
    ∀ x, p k (fun _ => x) = Qtop x := by
  have hjp : HasFPowerSeriesAt (j ∘ Q) (j.compFormalMultilinearSeries p) x₀ := by
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, j.comp_hasFPowerSeriesOnBall hr⟩
  have h := coeff_eq_of_hasFPowerSeriesAt (j ∘ Q) x₀ k B
    (by intro t x; simpa using hB t x) (j.compFormalMultilinearSeries p) hjp
  intro x
  apply hj
  have h1 := h x
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply] at h1
  simpa [htop x] using h1

end Extraction

/-! ## Part 2. Line expansion of a continuous multilinear map on the diagonal -/

section LineExpansion


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `r`-th coefficient of `t ↦ A (x₀ + t • h, …, x₀ + t • h)`: the sum over all `r`-element
sets `s` of slots of `A` evaluated with `h` in the slots of `s` and `x₀` elsewhere. -/
noncomputable def lineCoeff (A : ContinuousMultilinearMap 𝕜 (fun _ : ι => X) W) (x₀ : X)
    (r : ℕ) (h : X) : W :=
  ∑ s ∈ (Finset.univ : Finset (Finset ι)).filter (fun s => s.card = r),
    A (s.piecewise (fun _ => h) (fun _ => x₀))

/-- **Line expansion of a multilinear map on the diagonal.** -/
theorem map_diag_add_smul (A : ContinuousMultilinearMap 𝕜 (fun _ : ι => X) W) (x₀ h : X)
    (t : 𝕜) :
    A (fun _ => x₀ + t • h) =
      ∑ r ∈ Finset.range (Fintype.card ι + 1), t ^ r • lineCoeff A x₀ r h := by
  have h1 : (fun _ : ι => x₀ + t • h) = (fun _ : ι => t • h) + (fun _ : ι => x₀) := by
    funext i; simp [add_comm]
  rw [h1, A.map_add_univ]
  have h2 : ∀ s : Finset ι, A (s.piecewise (fun _ => t • h) (fun _ => x₀)) =
      t ^ s.card • A (s.piecewise (fun _ => h) (fun _ => x₀)) := by
    intro s
    have := A.map_piecewise_smul (fun _ => t) (s.piecewise (fun _ => h) (fun _ => x₀)) s
    rw [Finset.prod_const] at this
    rw [← this]
    congr 1
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  simp_rw [h2]
  unfold lineCoeff
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset ι)))
    (t := Finset.range (Fintype.card ι + 1)) (g := Finset.card)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [(Finset.mem_filter.mp hs).2]
  · intro s _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ s))

/-- The top line coefficient is `A` on the diagonal, independently of the base point. -/
theorem lineCoeff_card (A : ContinuousMultilinearMap 𝕜 (fun _ : ι => X) W) (x₀ h : X) :
    lineCoeff A x₀ (Fintype.card ι) h = A (fun _ => h) := by
  unfold lineCoeff
  have : (Finset.univ : Finset (Finset ι)).filter (fun s => s.card = Fintype.card ι) =
      {Finset.univ} := by
    ext s
    simp [Finset.card_eq_iff_eq_univ]
  rw [this, Finset.sum_singleton, Finset.piecewise_univ]

end LineExpansion

/-! ## Part 3. T1 for precomposition on continuous alternating maps -/

section T1

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 ι E E' F) in
/-- The precomposition map `Q f m = m ∘ (f, …, f)` (Mathlib's `compContinuousLinearMapCLM`). -/
noncomputable abbrev Q : (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  compContinuousLinearMapCLM

variable (𝕜 ι E E' F) in
/-- Post-composition with the isometric inclusion `ι_* : Alt(E,F) → Mult(E,F)`. -/
noncomputable def jAmb : ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) →L[𝕜]
    ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :=
  ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) (E [⋀^ι]→L[𝕜] F)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (toContinuousMultilinearMapCLM 𝕜)

lemma jAmb_apply_apply (T : (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) (m : E' [⋀^ι]→L[𝕜] F) :
    jAmb 𝕜 ι E E' F T m = (T m).toContinuousMultilinearMap := rfl

lemma jAmb_injective : Function.Injective (jAmb 𝕜 ι E E' F) := by
  intro T₁ T₂ h
  refine ContinuousLinearMap.ext fun m => toContinuousMultilinearMap_injective ?_
  have := congrArg (fun T => T m) h
  simpa only [jAmb_apply_apply] using this

variable (𝕜 ι E E' F) in
/-- The ambient lift `A (f₁, …, f_k) m = m ∘ (f₁, …, f_k)`, valued in `L(Alt(E',F), Mult(E,F))`.
It always exists; this is why the ambient space alone carries no information. -/
noncomputable def ambLift : ContinuousMultilinearMap 𝕜 (fun _ : ι => E →L[𝕜] E')
    ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :=
  ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) (ContinuousMultilinearMap 𝕜 (fun _ : ι => E') F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)).flip
      (toContinuousMultilinearMapCLM 𝕜)).compContinuousMultilinearMap
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
      (fun _ : ι => E) (fun _ => E') F)

lemma ambLift_diag (f : E →L[𝕜] E') :
    ambLift 𝕜 ι E E' F (fun _ => f) = jAmb 𝕜 ι E E' F (Q 𝕜 ι E E' F f) := by
  ext m x
  rfl

/-- **Key step of T1, (iv) ⇒ (i), repaired form.** If `Q` has power series `p` at *any* base point
`f₀`, then the `card ι`-th term of `p` is a bounded `card ι`-linear lift of `Q`. -/
theorem coeff_card_eq_Q {p} {f₀ : E →L[𝕜] E'}
    (hp : HasFPowerSeriesAt (𝕜 := 𝕜) (Q 𝕜 ι E E' F) p f₀) (h : E →L[𝕜] E') :
    p (Fintype.card ι) (fun _ => h) = Q 𝕜 ι E E' F h := by
  classical
  have hdiag : ∀ x, jAmb 𝕜 ι E E' F (Q 𝕜 ι E E' F x) = ambLift 𝕜 ι E E' F (fun _ => x) :=
    fun x => (ambLift_diag x).symm
  have hinj : Function.Injective (jAmb 𝕜 ι E E' F) := jAmb_injective
  have hB : ∀ (t : 𝕜) (x : E →L[𝕜] E'), jAmb 𝕜 ι E E' F (Q 𝕜 ι E E' F (f₀ + t • x)) =
      ∑ r ∈ Finset.range (Fintype.card ι + 1),
        t ^ r • lineCoeff (𝕜 := 𝕜) (ambLift 𝕜 ι E E' F) f₀ r x := by
    intro t x
    rw [hdiag]
    exact map_diag_add_smul (𝕜 := 𝕜) (ι := ι) (X := E →L[𝕜] E')
      (W := ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)) (ambLift 𝕜 ι E E' F) f₀ x t
  have htop : ∀ x, lineCoeff (𝕜 := 𝕜) (ambLift 𝕜 ι E E' F) f₀ (Fintype.card ι) x =
      jAmb 𝕜 ι E E' F (Q 𝕜 ι E E' F x) := by
    intro x
    rw [hdiag]
    exact lineCoeff_card (𝕜 := 𝕜) (ι := ι) (X := E →L[𝕜] E')
      (W := ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)) (ambLift 𝕜 ι E E' F) f₀ x
  exact coeff_eq_of_ambient (𝕜 := 𝕜) (X := E →L[𝕜] E') (Z := ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))
    (W := ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)) (Q 𝕜 ι E E' F) f₀ (Fintype.card ι)
    (fun r x => lineCoeff (𝕜 := 𝕜) (ambLift 𝕜 ι E E' F) f₀ r x) (jAmb 𝕜 ι E E' F) hinj
    (Q 𝕜 ι E E' F) hB htop p hp h

variable (𝕜 ι E E' F) in
/-- `Q` admits a bounded `card ι`-linear lift. -/
def HasBoundedLift : Prop :=
  ∃ P : ContinuousMultilinearMap 𝕜 (fun _ : Fin (Fintype.card ι) => E →L[𝕜] E')
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)),
    ∀ f, P (fun _ => f) = Q 𝕜 ι E E' F f

/-- (iv) ⇒ (i). -/
theorem hasBoundedLift_of_analyticAt {f₀ : E →L[𝕜] E'} (h : AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₀) :
    HasBoundedLift 𝕜 ι E E' F := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p (Fintype.card ι), coeff_card_eq_Q hp⟩

/-- (i) ⇒ (ii), for a lift of any arity. -/
theorem cpolynomialAt_of_lift {n : ℕ} (P : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E →L[𝕜] E')
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))
    (hP : ∀ f, P (fun _ => f) = Q 𝕜 ι E E' F f) (f₀ : E →L[𝕜] E') :
    CPolynomialAt 𝕜 (Q 𝕜 ι E E' F) f₀ := by
  have hQ : Q 𝕜 ι E E' F = P ∘ (fun f => fun _ : Fin n => f) := funext fun f => (hP f).symm
  rw [hQ]
  exact CPolynomialAt.comp (g := ⇑P) (f := fun f : E →L[𝕜] E' => fun _ : Fin n => f)
    (ContinuousMultilinearMap.cpolynomialAt _)
    (ContinuousLinearMap.cpolynomialAt
      (ContinuousLinearMap.pi fun _ : Fin n => ContinuousLinearMap.id 𝕜 (E →L[𝕜] E')) f₀)

/-- **T1 (LEAN).** The six conditions are equivalent. Items 5–6 (`C^ω` in Mathlib's sense, globally
or at one point) were added in repair round 1; no completeness is needed anywhere. -/
theorem tfae_Q : List.TFAE
    [HasBoundedLift 𝕜 ι E E' F,
     ∀ f₀, CPolynomialAt 𝕜 (Q 𝕜 ι E E' F) f₀,
     ∀ f₀, AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₀,
     ∃ f₀, AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₀,
     ContDiff 𝕜 ω (Q 𝕜 ι E E' F),
     ∃ f₀, ContDiffAt 𝕜 ω (Q 𝕜 ι E E' F) f₀] := by
  tfae_have 1 → 2 := fun ⟨P, hP⟩ f₀ => cpolynomialAt_of_lift P hP f₀
  tfae_have 2 → 3 := fun h f₀ => (h f₀).analyticAt
  tfae_have 3 → 4 := fun h => ⟨0, h 0⟩
  tfae_have 4 → 1 := fun ⟨_, h⟩ => hasBoundedLift_of_analyticAt h
  tfae_have 2 → 5 := fun h => contDiff_iff_contDiffAt.2 fun f₀ => (h f₀).contDiffAt
  tfae_have 5 → 6 := fun h => ⟨0, h.contDiffAt⟩
  tfae_have 6 → 4 := fun ⟨f₀, h⟩ => ⟨f₀, h.analyticAt⟩
  tfae_finish

/-- **`C^ω` form of T1 (LEAN).** The project question "is `Q` of class `C^ω`?" is exactly the
bounded-lift question. -/
theorem contDiff_omega_iff_hasBoundedLift :
    ContDiff 𝕜 ω (Q 𝕜 ι E E' F) ↔ HasBoundedLift 𝕜 ι E E' F :=
  (tfae_Q (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F)).out 5 1

/-- **Dichotomy.** Analytic at one point ⇒ continuously polynomial at every point. -/
theorem cpolynomialAt_of_analyticAt {f₀ : E →L[𝕜] E'} (h : AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₀)
    (f₁ : E →L[𝕜] E') : CPolynomialAt 𝕜 (Q 𝕜 ι E E' F) f₁ := by
  obtain ⟨P, hP⟩ := hasBoundedLift_of_analyticAt h
  exact cpolynomialAt_of_lift P hP f₁

/-- **Nowhere-analytic transfer.** Not analytic at one point ⇒ analytic at no point. -/
theorem not_analyticAt_of_not_analyticAt {f₀ : E →L[𝕜] E'} (h : ¬ AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₀)
    (f₁ : E →L[𝕜] E') : ¬ AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₁ :=
  fun h₁ => h (cpolynomialAt_of_analyticAt h₁ f₀).analyticAt

/-- The lift may equally be indexed by `ι` itself. -/
theorem hasBoundedLift_iff_exists_ι :
    HasBoundedLift 𝕜 ι E E' F ↔
      ∃ P : ContinuousMultilinearMap 𝕜 (fun _ : ι => E →L[𝕜] E')
          ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)),
        ∀ f, P (fun _ => f) = Q 𝕜 ι E E' F f := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.domDomCongr (Fintype.equivFin ι).symm, fun f => hP f⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.domDomCongr (Fintype.equivFin ι), fun f => hP f⟩

end T1

/-! ## Part 4. T2: degree propagation `k + 1 → k` -/

section T2

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

variable (𝕜 E' F n) in
/-- `S m ((y₀,t₀),…,(yₙ,tₙ)) = ∑ᵢ (-1)^i • tᵢ • m(y₀,…,ŷᵢ,…,yₙ)`: division-free "wedge with the
last coordinate", built from Mathlib's `alternatizeUncurryFin` (whose alternating property is proved
in Mathlib with no hypothesis on the characteristic). -/
noncomputable def Smap : (E' [⋀^Fin n]→L[𝕜] F) →L[𝕜] ((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) :=
  (alternatizeUncurryFinCLM 𝕜 (E' × 𝕜) F).comp
    ((ContinuousLinearMap.smulRightL 𝕜 (E' × 𝕜) ((E' × 𝕜) [⋀^Fin n]→L[𝕜] F)
        (ContinuousLinearMap.snd 𝕜 E' 𝕜)).comp
      (compContinuousLinearMapCLM (ContinuousLinearMap.fst 𝕜 E' 𝕜)))

lemma Smap_apply (m : E' [⋀^Fin n]→L[𝕜] F) (v : Fin (n + 1) → E' × 𝕜) :
    Smap 𝕜 E' F n m v =
      ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • ((v i).2 • m (fun j => (i.removeNth v j).1)) := by
  simp [Smap, alternatizeUncurryFin_apply]
  rfl

variable (𝕜 E F n) in
/-- `R M (x₁,…,xₙ) = M((0,1),(x₁,0),…,(xₙ,0))`. -/
noncomputable def Rmap : ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] (E [⋀^Fin n]→L[𝕜] F) :=
  (compContinuousLinearMapCLM (ContinuousLinearMap.inl 𝕜 E 𝕜)).comp
    ((ContinuousLinearMap.apply 𝕜 ((E × 𝕜) [⋀^Fin n]→L[𝕜] F) ((0 : E), (1 : 𝕜))).comp
      (curryLeftLI (𝕜 := 𝕜) (E := E × 𝕜) (F := F) (n := n)).toContinuousLinearMap)

lemma Rmap_apply (M : (E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) (x : Fin n → E) :
    Rmap 𝕜 E F n M x = M (Matrix.vecCons ((0 : E), (1 : 𝕜)) (fun j => (x j, (0 : 𝕜)))) := rfl

/-- Sign bookkeeping: with these conventions `R ∘ S = id` (no sign), in every characteristic. -/
theorem Rmap_Smap (m : E' [⋀^Fin n]→L[𝕜] F) : Rmap 𝕜 E' F n (Smap 𝕜 E' F n m) = m := by
  ext x
  rw [Rmap_apply, Smap_apply, Fin.sum_univ_succ]
  simp

variable (𝕜 E E' F n) in
/-- `Γ T = R ∘ T ∘ S`. -/
noncomputable def Γ : (((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)) →L[𝕜]
    ((E' [⋀^Fin n]→L[𝕜] F) →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :=
  (ContinuousLinearMap.compL 𝕜 (E' [⋀^Fin n]→L[𝕜] F) ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)
      (E [⋀^Fin n]→L[𝕜] F) (Rmap 𝕜 E F n)).comp
    ((ContinuousLinearMap.compL 𝕜 (E' [⋀^Fin n]→L[𝕜] F) ((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)
      ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)).flip (Smap 𝕜 E' F n))

lemma Γ_apply (T : ((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F))
    (m : E' [⋀^Fin n]→L[𝕜] F) : Γ 𝕜 E E' F n T m = Rmap 𝕜 E F n (T (Smap 𝕜 E' F n m)) := rfl

variable (𝕜 E E') in
/-- `φ f = f ⊕ 0 : E × 𝕜 → E' × 𝕜`, linear in `f`. -/
noncomputable def φ : (E →L[𝕜] E') →L[𝕜] (E × 𝕜 →L[𝕜] E' × 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 (E × 𝕜) E' (E' × 𝕜) (ContinuousLinearMap.inl 𝕜 E' 𝕜)).comp
    ((ContinuousLinearMap.compL 𝕜 (E × 𝕜) E E').flip (ContinuousLinearMap.fst 𝕜 E 𝕜))

lemma φ_apply (f : E →L[𝕜] E') (x : E × 𝕜) : φ 𝕜 E E' f x = (f x.1, 0) := rfl

variable (𝕜 E E') in
/-- `j = 0 ⊕ id_𝕜`. -/
noncomputable def jj : E × 𝕜 →L[𝕜] E' × 𝕜 :=
  (ContinuousLinearMap.inr 𝕜 E' 𝕜).comp (ContinuousLinearMap.snd 𝕜 E 𝕜)

lemma jj_apply (x : E × 𝕜) : jj 𝕜 E E' x = (0, x.2) := rfl

/-- **Intertwining identity** `R ∘ Q_{n+1}(f ⊕ id) ∘ S = Q_n(f)` (no sign with these conventions). -/
theorem Γ_Q_succ (f : E →L[𝕜] E') :
    Γ 𝕜 E E' F n (Q 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F (φ 𝕜 E E' f + jj 𝕜 E E')) =
      Q 𝕜 (Fin n) E E' F f := by
  ext m x
  rw [Γ_apply, Rmap_apply]
  simp only [Q, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply]
  rw [Smap_apply, Fin.sum_univ_succ]
  simp [φ_apply, jj_apply]
  congr 1
  funext j
  simp [Fin.tail, φ_apply, jj_apply]

/-- **T2 (LEAN).** A bounded `(n+1)`-linear lift of `Q_{n+1}` on `(E × 𝕜, E' × 𝕜, F)` yields a
bounded `n`-linear lift of `Q_n` on `(E, E', F)`. The target `F` is unchanged. -/
theorem hasBoundedLift_of_hasBoundedLift_succ
    (h : HasBoundedLift 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F) : HasBoundedLift 𝕜 (Fin n) E E' F := by
  obtain ⟨P, hP⟩ := h
  -- upstairs: the lift makes `Q_(n+1)` continuously polynomial, in particular analytic at `j`
  have hup : AnalyticAt 𝕜 (Q 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F) (φ 𝕜 E E' 0 + jj 𝕜 E E') :=
    (cpolynomialAt_of_lift P hP _).analyticAt
  -- the affine map `f ↦ φ f + j` is analytic
  have haff : AnalyticAt 𝕜 (fun f : E →L[𝕜] E' => φ 𝕜 E E' f + jj 𝕜 E E') 0 :=
    ((φ 𝕜 E E').analyticAt 0).add analyticAt_const
  have h2 : AnalyticAt 𝕜
      ((Q 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F) ∘ (fun f : E →L[𝕜] E' => φ 𝕜 E E' f + jj 𝕜 E E'))
      0 := AnalyticAt.comp (𝕜 := 𝕜) hup haff
  have h3 : AnalyticAt 𝕜 ((Γ 𝕜 E E' F n) ∘
      ((Q 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F) ∘ (fun f : E →L[𝕜] E' => φ 𝕜 E E' f + jj 𝕜 E E')))
      0 := by
    have hΓ : AnalyticAt 𝕜 (Γ 𝕜 E E' F n)
        (((Q 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F) ∘
          (fun f : E →L[𝕜] E' => φ 𝕜 E E' f + jj 𝕜 E E')) 0) :=
      ContinuousLinearMap.analyticAt (𝕜 := 𝕜) (E := (((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F))) (F := ((E' [⋀^Fin n]→L[𝕜] F) →L[𝕜] (E [⋀^Fin n]→L[𝕜] F))) (Γ 𝕜 E E' F n) _
    exact AnalyticAt.comp (𝕜 := 𝕜) (E := E →L[𝕜] E') (F := (((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F))) (G := ((E' [⋀^Fin n]→L[𝕜] F) →L[𝕜] (E [⋀^Fin n]→L[𝕜] F))) hΓ h2
  -- downstairs: by the intertwining identity this composite IS `Q_n`, so `Q_n` is analytic at 0
  have heq : ((Γ 𝕜 E E' F n) ∘
      ((Q 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F) ∘ (fun f : E →L[𝕜] E' => φ 𝕜 E E' f + jj 𝕜 E E')))
      = Q 𝕜 (Fin n) E E' F := funext fun f => Γ_Q_succ f
  rw [heq] at h3
  exact hasBoundedLift_of_analyticAt h3

end T2

/-! ## Part 5. The conjugation transfer principle and its corollaries -/

section Conjugation

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι ι₁ : Type*} [Fintype ι] [Fintype ι₁]
  {E E' F E₁ E₁' F₁ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₁'] [NormedSpace 𝕜 E₁'] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]

/-- **Conjugation transfer (LEAN).** If `Q₁ = Ψ ∘ Q ∘ A` with `Ψ` continuous linear and `A` analytic
at one point, then a bounded lift of `Q` gives a bounded lift of `Q₁`. -/
theorem hasBoundedLift_of_eq_comp
    (A : (E₁ →L[𝕜] E₁') → (E →L[𝕜] E')) {a : E₁ →L[𝕜] E₁'} (hA : AnalyticAt 𝕜 A a)
    (Ψ : ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) →L[𝕜]
      ((E₁' [⋀^ι₁]→L[𝕜] F₁) →L[𝕜] (E₁ [⋀^ι₁]→L[𝕜] F₁)))
    (hΨ : ∀ f, Q 𝕜 ι₁ E₁ E₁' F₁ f = Ψ (Q 𝕜 ι E E' F (A f)))
    (h : HasBoundedLift 𝕜 ι E E' F) : HasBoundedLift 𝕜 ι₁ E₁ E₁' F₁ := by
  obtain ⟨P, hP⟩ := h
  have hQ : AnalyticAt 𝕜 (Q 𝕜 ι E E' F) (A a) := (cpolynomialAt_of_lift P hP _).analyticAt
  have h2 : AnalyticAt 𝕜 ((Q 𝕜 ι E E' F) ∘ A) a := AnalyticAt.comp (𝕜 := 𝕜) hQ hA
  have hΨa : AnalyticAt 𝕜 Ψ (((Q 𝕜 ι E E' F) ∘ A) a) :=
    ContinuousLinearMap.analyticAt (𝕜 := 𝕜)
      (E := (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F))
      (F := (E₁' [⋀^ι₁]→L[𝕜] F₁) →L[𝕜] (E₁ [⋀^ι₁]→L[𝕜] F₁)) Ψ _
  have h3 : AnalyticAt 𝕜 (Ψ ∘ ((Q 𝕜 ι E E' F) ∘ A)) a :=
    AnalyticAt.comp (𝕜 := 𝕜) (E := E₁ →L[𝕜] E₁')
      (F := (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F))
      (G := (E₁' [⋀^ι₁]→L[𝕜] F₁) →L[𝕜] (E₁ [⋀^ι₁]→L[𝕜] F₁)) hΨa h2
  have heq : (Ψ ∘ ((Q 𝕜 ι E E' F) ∘ A)) = Q 𝕜 ι₁ E₁ E₁' F₁ := funext fun f => (hΨ f).symm
  rw [heq] at h3
  exact hasBoundedLift_of_analyticAt h3

/-- **Naturality in the source spaces (LEAN).** Continuous linear equivalences `E ≃ E₁`, `E' ≃ E₁'`
transport bounded lifts (no isometry needed). -/
theorem hasBoundedLift_of_equiv (e : E ≃L[𝕜] E₁) (e' : E' ≃L[𝕜] E₁')
    (h : HasBoundedLift 𝕜 ι E E' F) : HasBoundedLift 𝕜 ι E₁ E₁' F := by
  refine hasBoundedLift_of_eq_comp (a := 0)
    (((ContinuousLinearMap.compL 𝕜 E E₁' E') (e'.symm : E₁' →L[𝕜] E')).comp
      ((ContinuousLinearMap.compL 𝕜 E E₁ E₁').flip (e : E →L[𝕜] E₁)))
    (ContinuousLinearMap.analyticAt _ _)
    ((ContinuousLinearMap.compL 𝕜 (E₁' [⋀^ι]→L[𝕜] F) (E [⋀^ι]→L[𝕜] F) (E₁ [⋀^ι]→L[𝕜] F)
        (compContinuousLinearMapCLM (e.symm : E₁ →L[𝕜] E))).comp
      ((ContinuousLinearMap.compL 𝕜 (E₁' [⋀^ι]→L[𝕜] F) (E' [⋀^ι]→L[𝕜] F)
        (E [⋀^ι]→L[𝕜] F)).flip (compContinuousLinearMapCLM (e' : E' →L[𝕜] E₁'))))
    ?_ h
  intro f
  ext m x
  simp only [Q, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  congr 1
  funext i
  simp

theorem hasBoundedLift_equiv_iff (e : E ≃L[𝕜] E₁) (e' : E' ≃L[𝕜] E₁') :
    HasBoundedLift 𝕜 ι E E' F ↔ HasBoundedLift 𝕜 ι E₁ E₁' F :=
  ⟨hasBoundedLift_of_equiv e e', hasBoundedLift_of_equiv e.symm e'.symm⟩

/-- **Target retracts (LEAN; round 23 Lemma 5.2).** If `F` is a retract of `F₁`
(`π ∘ g = id`), a bounded lift for the target `F₁` gives one for `F`. -/
theorem hasBoundedLift_of_retract (g : F →L[𝕜] F₁) (π : F₁ →L[𝕜] F) (hπg : ∀ y, π (g y) = y)
    (h : HasBoundedLift 𝕜 ι E E' F₁) : HasBoundedLift 𝕜 ι E E' F := by
  refine hasBoundedLift_of_eq_comp (a := 0) id (analyticAt_id)
    ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) (E [⋀^ι]→L[𝕜] F₁) (E [⋀^ι]→L[𝕜] F)
        (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F₁ F ι π)).comp
      ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) (E' [⋀^ι]→L[𝕜] F₁)
        (E [⋀^ι]→L[𝕜] F₁)).flip (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E' F F₁ ι g)))
    ?_ h
  intro f
  ext m x
  simp [hπg]

end Conjugation

/-! ## Part 5b. Same-degree summand transfer (added in repair round 2)

Adding a line to both sources, in the SAME degree, cannot create a lift. This is Theorem 4.1 with
`A = φ` (linear, so analytic) and `Ψ(T) = inl^* ∘ T ∘ fst^*`. It was first machine-checked by the
round-2 controls auditor (`round24/audit/transfer-r2-controls/build/SameDegreeSummand.lean`,
`audit_hasBoundedLift_of_prod_same_degree`); it is re-proved here so that the track's own file
contains it. It is used in THEOREM.md §8, Scope item 1 (no downward propagation, also over
incomplete `𝕜`). -/

section SameDegree

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Same-degree summand transfer (LEAN, repair round 2).** A bounded lift in degree `ι` for
`(E × 𝕜, E' × 𝕜, F)` gives one in the same degree for `(E, E', F)`. -/
theorem hasBoundedLift_of_prod_same_degree
    (h : HasBoundedLift 𝕜 ι (E × 𝕜) (E' × 𝕜) F) : HasBoundedLift 𝕜 ι E E' F := by
  refine hasBoundedLift_of_eq_comp (a := 0) (φ 𝕜 E E') ((φ 𝕜 E E').analyticAt 0)
    ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) ((E × 𝕜) [⋀^ι]→L[𝕜] F) (E [⋀^ι]→L[𝕜] F)
        (compContinuousLinearMapCLM (ContinuousLinearMap.inl 𝕜 E 𝕜))).comp
      ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) ((E' × 𝕜) [⋀^ι]→L[𝕜] F)
        ((E × 𝕜) [⋀^ι]→L[𝕜] F)).flip
          (compContinuousLinearMapCLM (ContinuousLinearMap.fst 𝕜 E' 𝕜))))
    ?_ h
  intro f
  ext m x
  simp only [Q, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  congr 1

/-- **Contrapositive with T1 (LEAN, repair round 2).** If `Q` fails to be analytic at one point for
`(E, E', F)`, then in the same degree it is analytic at no point for `(E × 𝕜, E' × 𝕜, F)`. -/
theorem not_analyticAt_prod_of_not_analyticAt {f₀ : E →L[𝕜] E'}
    (h : ¬ AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₀) (g₀ : E × 𝕜 →L[𝕜] E' × 𝕜) :
    ¬ AnalyticAt 𝕜 (Q 𝕜 ι (E × 𝕜) (E' × 𝕜) F) g₀ := by
  intro hg
  obtain ⟨P, hP⟩ := hasBoundedLift_of_prod_same_degree (hasBoundedLift_of_analyticAt hg)
  exact h (cpolynomialAt_of_lift P hP f₀).analyticAt

end SameDegree

/-! ## Part 6. Iterated degree propagation -/

section Iterate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **All degrees (LEAN).** If `E × 𝕜 ≃ E` and `E' × 𝕜 ≃ E'` (e.g. `E = E' = ℓ∞`), failure of the
bounded-lift property in degree `n` propagates to every degree `m ≥ n`, with the SAME `E, E', F`. -/
theorem not_hasBoundedLift_of_le (u : (E × 𝕜) ≃L[𝕜] E) (u' : (E' × 𝕜) ≃L[𝕜] E') {n : ℕ}
    (h : ¬ HasBoundedLift 𝕜 (Fin n) E E' F) {m : ℕ} (hm : n ≤ m) :
    ¬ HasBoundedLift 𝕜 (Fin m) E E' F := by
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
    intro hsucc
    exact ih (hasBoundedLift_of_hasBoundedLift_succ
      (hasBoundedLift_of_equiv u.symm u'.symm hsucc))

/-- **All degrees, all base points (LEAN).** Under the same hypotheses, if `Q_n` fails to be
analytic at one point then `Q_m` is analytic at no point, for every `m ≥ n`. -/
theorem not_analyticAt_of_le (u : (E × 𝕜) ≃L[𝕜] E) (u' : (E' × 𝕜) ≃L[𝕜] E') {n : ℕ}
    {f₀ : E →L[𝕜] E'} (h : ¬ AnalyticAt 𝕜 (Q 𝕜 (Fin n) E E' F) f₀) {m : ℕ} (hm : n ≤ m)
    (f₁ : E →L[𝕜] E') : ¬ AnalyticAt 𝕜 (Q 𝕜 (Fin m) E E' F) f₁ := by
  intro h₁
  have hn : ¬ HasBoundedLift 𝕜 (Fin n) E E' F := fun ⟨P, hP⟩ =>
    h (cpolynomialAt_of_lift P hP f₀).analyticAt
  exact not_hasBoundedLift_of_le u u' hn hm (hasBoundedLift_of_analyticAt h₁)

end Iterate

/-! ## Part 7. Reindexing: the index type only matters through its cardinality -/

section Reindex

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι ι₁ : Type*} [Fintype ι] [Fintype ι₁]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Reindexing a continuous alternating map along `σ : ι ≃ ι₁`. -/
def reindexAlt (σ : ι ≃ ι₁) (m : E [⋀^ι]→L[𝕜] F) : E [⋀^ι₁]→L[𝕜] F where
  toContinuousMultilinearMap := m.toContinuousMultilinearMap.domDomCongr σ
  map_eq_zero_of_eq' v i j hv hij := by
    change m (fun k => v (σ k)) = 0
    exact m.map_eq_zero_of_eq (fun k => v (σ k)) (i := σ.symm i) (j := σ.symm j)
      (by simpa using hv) (by simpa using hij)

omit [Fintype ι] [Fintype ι₁] in
lemma reindexAlt_apply (σ : ι ≃ ι₁) (m : E [⋀^ι]→L[𝕜] F) (v : ι₁ → E) :
    reindexAlt σ m v = m (fun k => v (σ k)) := rfl

variable (𝕜 E F) in
/-- Reindexing as a continuous linear map (of norm `≤ 1`). -/
noncomputable def reindexCLM (σ : ι ≃ ι₁) : (E [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι₁]→L[𝕜] F) :=
  LinearMap.mkContinuous
    { toFun := reindexAlt σ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun m => by
      rw [one_mul]
      change ‖(m.toContinuousMultilinearMap.domDomCongr σ)‖ ≤ ‖m.toContinuousMultilinearMap‖
      exact (ContinuousMultilinearMap.norm_domDomCongr 𝕜 E F σ _).le)

lemma reindexCLM_apply (σ : ι ≃ ι₁) (m : E [⋀^ι]→L[𝕜] F) (v : ι₁ → E) :
    reindexCLM 𝕜 E F σ m v = m (fun k => v (σ k)) := rfl

/-- **Reindexing (LEAN).** The bounded-lift property depends on `ι` only through `card ι`. -/
theorem hasBoundedLift_reindex (σ : ι ≃ ι₁) (h : HasBoundedLift 𝕜 ι E E' F) :
    HasBoundedLift 𝕜 ι₁ E E' F := by
  refine hasBoundedLift_of_eq_comp (a := 0) id analyticAt_id
    ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι₁]→L[𝕜] F) (E [⋀^ι]→L[𝕜] F) (E [⋀^ι₁]→L[𝕜] F)
        (reindexCLM 𝕜 E F σ)).comp
      ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι₁]→L[𝕜] F) (E' [⋀^ι]→L[𝕜] F)
        (E [⋀^ι]→L[𝕜] F)).flip (reindexCLM 𝕜 E' F σ.symm)))
    ?_ h
  intro f
  ext m v
  simp only [Q, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, reindexCLM_apply, id]
  congr 1
  funext l
  simp

theorem hasBoundedLift_reindex_iff (σ : ι ≃ ι₁) :
    HasBoundedLift 𝕜 ι E E' F ↔ HasBoundedLift 𝕜 ι₁ E E' F :=
  ⟨hasBoundedLift_reindex σ, hasBoundedLift_reindex σ.symm⟩

/-- **Nowhere-analyticity along `ι ≃ ι₁` (LEAN, repair round 1).** If `Q_ι` fails to be analytic at
one point, then `Q_{ι₁}` is analytic at no point. -/
theorem not_analyticAt_of_equiv_index (σ : ι ≃ ι₁) {f₀ : E →L[𝕜] E'}
    (h : ¬ AnalyticAt 𝕜 (Q 𝕜 ι E E' F) f₀) (f₁ : E →L[𝕜] E') :
    ¬ AnalyticAt 𝕜 (Q 𝕜 ι₁ E E' F) f₁ := by
  intro h₁
  obtain ⟨P, hP⟩ := hasBoundedLift_reindex σ.symm (hasBoundedLift_of_analyticAt h₁)
  exact h (cpolynomialAt_of_lift P hP f₀).analyticAt

/-- **T2 for arbitrary index types (LEAN).** If `card ι₁ = card ι + 1`, a bounded lift of
`Q_{ι₁}` on `(E × 𝕜, E' × 𝕜, F)` gives a bounded lift of `Q_ι` on `(E, E', F)`. -/
theorem hasBoundedLift_of_card_eq_succ (hcard : Fintype.card ι₁ = Fintype.card ι + 1)
    (h : HasBoundedLift 𝕜 ι₁ (E × 𝕜) (E' × 𝕜) F) : HasBoundedLift 𝕜 ι E E' F :=
  hasBoundedLift_reindex (Fintype.equivFin ι).symm
    (hasBoundedLift_of_hasBoundedLift_succ
      (hasBoundedLift_reindex (Fintype.equivFinOfCardEq hcard) h))

end Reindex

end Round24Transfer
