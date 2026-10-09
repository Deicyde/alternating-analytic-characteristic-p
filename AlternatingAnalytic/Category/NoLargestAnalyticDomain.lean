import AlternatingAnalytic.Category.AnalyticDomainWitnesses
import AlternatingAnalytic.Category.FiniteUltrametricDomains
import AlternatingAnalytic.Analysis.PaddedIncompatiblePairs
import AlternatingAnalytic.Analysis.PaddedCompletionAnalytic

/-!
# No largest analytic domain over F_p(t)

Theorem H.4: over `F_p(t)` with the `t`-adic norm and `k ≥ p`, `Alt^k` has no largest full
analytic domain, also among isomorphism-closed domains and inside the finite-dimensional
ultrametric pairs. The witnesses are the padded pairs `X = (E_k, G)` and `Y = (D_k, G)`; `Y` is
split and the action from `Y` to `X` is not analytic. Its contravariant coordinate is a map
`E_k → D_k`. Nothing is said about maximal domains.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair.Padding

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (n : ℕ)
attribute [local instance] DeterminantPair.preferredNormedFieldK
  DeterminantPair.preferredFieldK DeterminantPair.preferredFieldL

/-- The rigid pair `X_k = (E_k, G)`. -/
def objectX : (NormedSpaceCat (K p r))ᵒᵖ × NormedSpaceCat (K p r) :=
  (op (NormedSpaceCat.of (K p r) (E p r n)), NormedSpaceCat.of (K p r) (G p r))

/-- The split pair `Y_k = (D_k, G)`. -/
def objectY : (NormedSpaceCat (K p r))ᵒᵖ × NormedSpaceCat (K p r) :=
  (op (NormedSpaceCat.of (K p r) (D p r n)), NormedSpaceCat.of (K p r) (G p r))

/-- The hom `Y_k ⟶ X_k` at which the action fails to be analytic. -/
def badHom : objectY p r n ⟶ objectX p r n :=
  (Quiver.Hom.op (show NormedSpaceCat.of (K p r) (E p r n) ⟶
      NormedSpaceCat.of (K p r) (D p r n) from auxiliaryIdentity p r n),
    ContinuousLinearMap.id (K p r) (G p r))

@[simp] theorem badHom_coordinates :
    NormedSpaceCat.pairHomCoordinates (objectY p r n) (objectX p r n) (badHom p r n) =
      (auxiliaryIdentity p r n, ContinuousLinearMap.id (K p r) (G p r)) := rfl

theorem objectX_singleton_analytic :
    IsAlternatingAnalyticDomain (K p r) (p+n) (fun Z => Z = objectX p r n) := by
  apply (isAlternatingAnalyticDomain_singleton_iff (K p r) (p+n) _).2
  exact fun h _ => analyticAt_selfActionE p r n h

theorem objectY_split : splitPairs (K p r) (p+n) (objectY p r n) :=
  isSplitAlternatingPair_canonical p r n

theorem objectY_singleton_analytic :
    IsAlternatingAnalyticDomain (K p r) (p+n) (fun Z => Z = objectY p r n) := by
  apply (isAlternatingAnalyticDomain_singleton_iff (K p r) (p+n) _).2
  exact analyticOnNhd_alternatingMapAction_of_split_destination (p+n)
    (isSplitAlternatingPair_canonical p r n)

/-- The action on homs `Y_k ⟶ X_k` is not analytic at `badHom`. -/
theorem not_analyticAt_badHom :
    ¬ AnalyticAt (K p r)
      (fun h : objectY p r n ⟶ objectX p r n => (alternatingFunctor (K p r) (p+n)).map h)
      (badHom p r n) := by
  intro h
  have hc := (analyticAt_functorMapInCoordinates_iff (alternatingFunctor (K p r) (p+n))
    (NormedSpaceCat.pairHomCoordinates (objectY p r n) (objectX p r n))
    (NormedSpaceCat.homCoordinates _ _) (badHom p r n)).2 h
  rw [alternatingFunctor_mapInCoordinates, badHom_coordinates] at hc
  exact not_analyticAt_crossAction p r n hc

theorem no_greatest_analyticDomain :
    ¬ ∃ S, IsGreatest {P | IsAlternatingAnalyticDomain (K p r) (p+n) P} S := by
  apply no_greatest_analyticDomain_of_incompatible (K p r) (p+n)
    (objectX p r n) (objectY p r n)
  · exact fun h _ => analyticAt_selfActionE p r n h
  · exact analyticOnNhd_alternatingMapAction_of_split_destination (p+n)
      (isSplitAlternatingPair_canonical p r n)
  · intro h
    exact not_analyticAt_crossAction p r n (h _ (Set.mem_univ _))

theorem no_greatest_repleteAnalyticDomain :
    ¬ ∃ S, IsGreatest
      {P | IsAlternatingAnalyticDomain (K p r) (p+n) P ∧ P.IsClosedUnderIsomorphisms} S := by
  apply no_greatest_repleteAnalyticDomain_of_incompatible (K p r) (p+n)
    (objectX p r n) (objectY p r n)
  · exact fun h _ => analyticAt_selfActionE p r n h
  · exact analyticOnNhd_alternatingMapAction_of_split_destination (p+n)
      (isSplitAlternatingPair_canonical p r n)
  · intro h
    exact not_analyticAt_crossAction p r n (h _ (Set.mem_univ _))

theorem objectX_finiteUltrametric : finiteUltrametricPairs (K p r) (objectX p r n) := by
  change FiniteDimensional (K p r) (E p r n) ∧ FiniteDimensional (K p r) (G p r) ∧
    IsUltrametricDist (E p r n) ∧ IsUltrametricDist (G p r)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem objectY_finiteUltrametric : finiteUltrametricPairs (K p r) (objectY p r n) := by
  change FiniteDimensional (K p r) (D p r n) ∧ FiniteDimensional (K p r) (G p r) ∧
    IsUltrametricDist (D p r n) ∧ IsUltrametricDist (G p r)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- `objectX` as an object of `FiniteUltrametricPairCat`. -/
def finiteObjectX : FiniteUltrametricPairCat (K p r) :=
  ⟨objectX p r n, objectX_finiteUltrametric p r n⟩

/-- `objectY` as an object of `FiniteUltrametricPairCat`. -/
def finiteObjectY : FiniteUltrametricPairCat (K p r) :=
  ⟨objectY p r n, objectY_finiteUltrametric p r n⟩

theorem no_greatest_finiteUltrametricAnalyticDomain :
    ¬ ∃ S, IsGreatest {P | IsFiniteUltrametricAnalyticDomain (K p r) (p+n) P} S := by
  apply no_greatest_relative_analytic_domain (K p r) (p+n)
    (finiteUltrametricPairs (K p r)) (finiteObjectX p r n) (finiteObjectY p r n)
  · exact fun h _ => analyticAt_selfActionE p r n h
  · exact analyticOnNhd_alternatingMapAction_of_split_destination (p+n)
      (isSplitAlternatingPair_canonical p r n)
  · intro h
    exact not_analyticAt_crossAction p r n (h _ (Set.mem_univ _))

/-- No largest isomorphism-closed analytic domain among finite-dimensional ultrametric pairs,
with isomorphism closure taken inside `FiniteUltrametricPairCat`. -/
theorem no_greatest_repleteFiniteUltrametricAnalyticDomain :
    ¬ ∃ S, IsGreatest
      {P | IsFiniteUltrametricAnalyticDomain (K p r) (p+n) P ∧
        P.IsClosedUnderIsomorphisms} S := by
  apply no_greatest_replete_relative_analytic_domain (K p r) (p+n)
    (finiteUltrametricPairs (K p r)) (finiteObjectX p r n) (finiteObjectY p r n)
  · exact fun h _ => analyticAt_selfActionE p r n h
  · exact analyticOnNhd_alternatingMapAction_of_split_destination (p+n)
      (isSplitAlternatingPair_canonical p r n)
  · intro h
    exact not_analyticAt_crossAction p r n (h _ (Set.mem_univ _))

/-- No analytic domain contains all split pairs together with `X_k`. -/
theorem not_analyticDomain_of_splitPairs_and_objectX
    (S : ObjectProperty ((NormedSpaceCat (K p r))ᵒᵖ × NormedSpaceCat (K p r)))
    (hSplit : splitPairs (K p r) (p+n) ≤ S) (hX : S (objectX p r n)) :
    ¬ IsAlternatingAnalyticDomain (K p r) (p+n) S := by
  intro hS
  have h := (isAlternatingAnalyticDomain_iff_coordinates (K p r) (p+n) S).1 hS
    (objectY p r n) (objectX p r n) (hSplit _ (objectY_split p r n)) hX
  exact not_analyticAt_crossAction p r n (h _ (Set.mem_univ _))

/-- Theorem H.4, with its witnesses and all four variants. In the last conclusion, isomorphism
closure is taken inside the finite-dimensional ultrametric pairs. -/
theorem no_largest_full_analytic_domain (k : ℕ) (hpk : p ≤ k) :
    ¬ CompleteSpace (K p r) ∧
    finiteUltrametricPairs (K p r) (objectX p r (k-p)) ∧
    finiteUltrametricPairs (K p r) (objectY p r (k-p)) ∧
    IsAlternatingAnalyticDomain (K p r) k (fun Z => Z = objectX p r (k-p)) ∧
    IsAlternatingAnalyticDomain (K p r) k (fun Z => Z = objectY p r (k-p)) ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := E p r (k-p)) (E' := E p r (k-p))
        (F := G p r) (F' := G p r) k) Set.univ ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := D p r (k-p)) (E' := D p r (k-p))
        (F := G p r) (F' := G p r) k) Set.univ ∧
    splitPairs (K p r) k (objectY p r (k-p)) ∧
    (NormedSpaceCat.pairHomCoordinates (objectY p r (k-p)) (objectX p r (k-p))
      (badHom p r (k-p)) =
        (auxiliaryIdentity p r (k-p), ContinuousLinearMap.id (K p r) (G p r))) ∧
    (¬ AnalyticAt (K p r)
      (fun h : objectY p r (k-p) ⟶ objectX p r (k-p) =>
        (alternatingFunctor (K p r) k).map h) (badHom p r (k-p))) ∧
    (¬ AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r (k-p)) (E' := E p r (k-p))
        (F := G p r) (F' := G p r) k)
      (auxiliaryIdentity p r (k-p), ContinuousLinearMap.id (K p r) (G p r))) ∧
    IsAlternatingAnalyticDomain (K p r) k
      (ObjectProperty.isoClosure (fun Z => Z = objectX p r (k-p))) ∧
    IsAlternatingAnalyticDomain (K p r) k
      (ObjectProperty.isoClosure (fun Z => Z = objectY p r (k-p))) ∧
    (¬ ∃ S, IsGreatest {P | IsAlternatingAnalyticDomain (K p r) k P} S) ∧
    (¬ ∃ S, IsGreatest
      {P | IsAlternatingAnalyticDomain (K p r) k P ∧ P.IsClosedUnderIsomorphisms} S) ∧
    (¬ ∃ S, IsGreatest {P | IsFiniteUltrametricAnalyticDomain (K p r) k P} S) ∧
    (¬ ∃ S, IsGreatest
      {P | IsFiniteUltrametricAnalyticDomain (K p r) k P ∧ P.IsClosedUnderIsomorphisms} S) := by
  have hk : p + (k-p) = k := Nat.add_sub_of_le hpk
  generalize hn : k-p = m at *
  subst k
  exact ⟨RationalField.not_completeSpace (ZMod p) r,
    objectX_finiteUltrametric p r m, objectY_finiteUltrametric p r m,
    objectX_singleton_analytic p r m, objectY_singleton_analytic p r m,
    (fun h _ => analyticAt_selfActionE p r m h),
    analyticOnNhd_alternatingMapAction_of_split_destination (p+m)
      (isSplitAlternatingPair_canonical p r m),
    objectY_split p r m, badHom_coordinates p r m, not_analyticAt_badHom p r m,
    not_analyticAt_crossAction p r m,
    (objectX_singleton_analytic p r m).isoClosure (K p r) (p+m),
    (objectY_singleton_analytic p r m).isoClosure (K p r) (p+m),
    no_greatest_analyticDomain p r m, no_greatest_repleteAnalyticDomain p r m,
    no_greatest_finiteUltrametricAnalyticDomain p r m,
    no_greatest_repleteFiniteUltrametricAnalyticDomain p r m⟩

/-- The closing remark of Appendix H: `X_k` cannot be adjoined to all split pairs, but completion
removes the obstruction. The completions of `E_k`, `D_k`, `G` and `C` are identified with explicit
`L`-spaces compatibly with the inclusions, and there the action over `L = F_p((t))` is analytic,
with an explicit coordinate lift. -/
theorem no_largest_domain_limits (k : ℕ) (hpk : p ≤ k) :
    (∀ S : ObjectProperty ((NormedSpaceCat (K p r))ᵒᵖ × NormedSpaceCat (K p r)),
      splitPairs (K p r) k ≤ S → S (objectX p r (k-p)) →
        ¬ IsAlternatingAnalyticDomain (K p r) k S) ∧
    (∀ x : E p r (k-p),
      completionE p r (k-p) (x : UniformSpace.Completion (E p r (k-p))) =
        inclusionE p r (k-p) x) ∧
    (∀ x : D p r (k-p),
      completionD p r (k-p) (x : UniformSpace.Completion (D p r (k-p))) =
        inclusionD p r (k-p) x) ∧
    (∀ x : G p r,
      DeterminantPair.completionG p r (x : UniformSpace.Completion (G p r)) = (x : L p r)) ∧
    (∀ x : C p r,
      completionC p r (x : UniformSpace.Completion (C p r)) = (x : L p r)) ∧
    CompleteSpace (H p r (k-p)) ∧ FiniteDimensional (L p r) (H p r (k-p)) ∧
    CompleteSpace (L p r) ∧
    AnalyticOnNhd (L p r)
      (alternatingMapAction (K := L p r) (E := H p r (k-p)) (E' := H p r (k-p))
        (F := L p r) (F' := L p r) k) Set.univ ∧
    (∀ z : Fin p → H p r (k-p),
      coordinateLift p r (k-p) z = ∏ j, constantCoefficient p r (k-p) (z j)) ∧
    (∀ z : H p r (k-p),
      coordinateLift p r (k-p) (fun _ => z) = (constantCoefficient p r (k-p) z) ^ p) ∧
    (∀ x : DeterminantPair.E p r,
      coordinateLift p r (k-p) (fun _ => inclusionE p r (k-p) (x, 0)) =
        (determinantCoordinate p r x : L p r)) ∧
    (∀ (x : DeterminantPair.E p r) (y : E p r (k-p)),
      completedPaddedMultiplication p r (k-p) (x : A p r) (inclusionE p r (k-p) y) =
        inclusionD p r (k-p) (paddedMultiplication p r (k-p) x y)) ∧
    (∀ x : A p r,
      LinearMap.det (completedPaddedMultiplication p r (k-p) x).toLinearMap =
        TruncatedPolynomial.coeff (L p r) p x 0 ^ p) ∧
    (∀ z : Fin (p+(k-p)) → D p r (k-p),
      completedDeterminant p r (k-p) (fun i => inclusionD p r (k-p) (z i)) =
        (determinantD p r (k-p) z : L p r)) ∧
    (∀ z : H p r (k-p),
      coordinateLift p r (k-p) (fun _ => z) =
        alternatingMapAction (p+(k-p))
          (completedPaddedMultiplication p r (k-p) z.1,
            ContinuousLinearMap.id (L p r) (L p r))
          (completedDeterminant p r (k-p)) (basis p r (k-p))) ∧
    (∀ x : DeterminantPair.E p r,
      coordinateLift p r (k-p) (fun _ => inclusionE p r (k-p) (x, 0)) =
        (crossActionEvaluation p r (k-p)
          (alternatingMapAction (p+(k-p)) (crossActionSlice p r (k-p) x)) : L p r)) := by
  have hk : p + (k-p) = k := Nat.add_sub_of_le hpk
  generalize hn : k-p = m at *
  subst k
  exact ⟨not_analyticDomain_of_splitPairs_and_objectX p r m,
    completionE_apply_coe p r m, completionD_apply_coe p r m,
    DeterminantPair.completionG_apply_coe p r, completionC_apply_coe p r,
    inferInstance, inferInstance, inferInstance,
    (fun h _ => analyticAt_completedAction p r m h),
    coordinateLift_apply p r m, coordinateLift_diagonal p r m,
    coordinateLift_original p r m, completedPaddedMultiplication_original p r m,
    det_completedPaddedMultiplication p r m, completedDeterminant_original p r m,
    coordinateLift_completedAction p r m,
    coordinateLift_originalAction p r m⟩

end AlternatingAnalytic.DeterminantPair.Padding
