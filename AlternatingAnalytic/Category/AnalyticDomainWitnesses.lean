import AlternatingAnalytic.Category.AnalyticDomainIsoClosure

/-!
# Incompatible analytic singleton domains

A greatest full analytic domain must contain every analytic singleton. Thus two
analytic self-actions and one nonanalytic directed cross-action exclude a greatest
domain. This does not exclude maximal domains.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K] (k : ℕ)

/-- The actual singleton full restriction is analytic exactly when its self-action is. -/
theorem isAlternatingAnalyticDomain_singleton_iff
    (X : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :
    IsAlternatingAnalyticDomain K k (fun Z => Z = X) ↔
      AnalyticOnNhd K (alternatingMapAction (K := K)
        (E := X.1.unop) (E' := X.1.unop) (F := X.2) (F' := X.2) k) Set.univ := by
  rw [isAlternatingAnalyticDomain_iff_coordinates]
  constructor
  · intro h
    exact h X X rfl rfl
  · rintro h _ _ rfl rfl
    exact h

/-- The bad arrow is from `Y` to `X`, with first coordinate `X.1 →L Y.1`. -/
theorem no_greatest_analyticDomain_of_incompatible
    (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)
    (hX : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := X.1.unop) (E' := X.1.unop) (F := X.2) (F' := X.2) k) Set.univ)
    (hY : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.1.unop) (E' := Y.1.unop) (F := Y.2) (F' := Y.2) k) Set.univ)
    (hYX : ¬ AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.1.unop) (E' := X.1.unop) (F := Y.2) (F' := X.2) k) Set.univ) :
    ¬ ∃ S, IsGreatest {P | IsAlternatingAnalyticDomain K k P} S := by
  rintro ⟨S, hS, hgreatest⟩
  have hXS : S X := hgreatest
    ((isAlternatingAnalyticDomain_singleton_iff K k X).2 hX) X rfl
  have hYS : S Y := hgreatest
    ((isAlternatingAnalyticDomain_singleton_iff K k Y).2 hY) Y rfl
  exact hYX ((isAlternatingAnalyticDomain_iff_coordinates K k S).1 hS Y X hYS hXS)

/-- The two full isomorphism closures are analytic witnesses in the class of
replete domains. The ordering is still inclusion of actual object properties. -/
theorem no_greatest_repleteAnalyticDomain_of_incompatible
    (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)
    (hX : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := X.1.unop) (E' := X.1.unop) (F := X.2) (F' := X.2) k) Set.univ)
    (hY : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.1.unop) (E' := Y.1.unop) (F := Y.2) (F' := Y.2) k) Set.univ)
    (hYX : ¬ AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.1.unop) (E' := X.1.unop) (F := Y.2) (F' := X.2) k) Set.univ) :
    ¬ ∃ S, IsGreatest
      {P | IsAlternatingAnalyticDomain K k P ∧ P.IsClosedUnderIsomorphisms} S := by
  rintro ⟨S, hS, hgreatest⟩
  have hXS : S X := hgreatest
    ⟨((isAlternatingAnalyticDomain_singleton_iff K k X).2 hX).isoClosure K k,
      inferInstance⟩ X (ObjectProperty.le_isoClosure (fun Z => Z = X) X rfl)
  have hYS : S Y := hgreatest
    ⟨((isAlternatingAnalyticDomain_singleton_iff K k Y).2 hY).isoClosure K k,
      inferInstance⟩ Y (ObjectProperty.le_isoClosure (fun Z => Z = Y) Y rfl)
  exact hYX ((isAlternatingAnalyticDomain_iff_coordinates K k S).1 hS.1 Y X hYS hXS)

end AlternatingAnalytic
