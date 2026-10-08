import AlternatingAnalytic.Exterior.Representation.Linearization

/-!
# The representation isometry `Alt^k(E; F) ≅ L(Λ^k_π E, F)`

Let `X` be a seminormed space identified with `⋀^k E` by a linear equivalence `e` under which the
seminorm of `X` is the projective exterior seminorm. Its separation quotient `Λ = X/{‖·‖ = 0}`
carries the universal alternating map `ω(x) = [e (x_1 ∧ ⋯ ∧ x_k)]`, of norm at most one. A bounded
alternating map `m` descends to `Λ` through its linearization with norm at most `‖m‖`, and
composition with `ω` is inverse to this; together they give a linear isometric equivalence
`Alt^k(E; F) ≃ L(Λ, F)`. Precomposition by `u : E → D` corresponds to precomposition by the
induced map `Λ_E → Λ_D`, whose norm is at most `‖u‖ ^ k`.
-/

namespace AlternatingAnalytic.ExteriorRepresentation

universe uF

variable {K : Type*} [NontriviallyNormedField K] {k : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {X : Type*} [SeminormedAddCommGroup X] [NormedSpace K X]
  (e : (⋀[K]^k E) ≃ₗ[K] X) (he : ∀ z, ‖e z‖ = projectiveExteriorSeminorm z)

/-- The universal alternating map `ω(x) = [e (x_1 ∧ ⋯ ∧ x_k)]` into the separation quotient. -/
noncomputable def wedge : E [⋀^Fin k]→L[K] SeparationQuotient X :=
  (((SeparationQuotient.mkCLM K X).toLinearMap ∘ₗ e.toLinearMap).compAlternatingMap
    (exteriorPower.ιMulti K k)).mkContinuous 1 fun x => by
      change ‖SeparationQuotient.mk (e (exteriorPower.ιMulti K k x))‖ ≤ 1 * ∏ i, ‖x i‖
      rw [SeparationQuotient.norm_mk, he, one_mul]
      exact projectiveExteriorSeminorm_ιMulti_le x

theorem wedge_apply (x : Fin k → E) :
    wedge e he x = SeparationQuotient.mk (e (exteriorPower.ιMulti K k x)) := rfl

theorem norm_wedge_le : ‖wedge e he‖ ≤ 1 :=
  AlternatingMap.mkContinuous_norm_le _ zero_le_one _

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]

/-- Bounded linear maps on the separation quotient are determined by their values on wedges. -/
theorem ext_wedge {T T' : SeparationQuotient X →L[K] F}
    (h : ∀ x : Fin k → E, T (wedge e he x) = T' (wedge e he x)) : T = T' := by
  have hlin : T.toLinearMap ∘ₗ (SeparationQuotient.mkCLM K X).toLinearMap ∘ₗ e.toLinearMap =
      T'.toLinearMap ∘ₗ (SeparationQuotient.mkCLM K X).toLinearMap ∘ₗ e.toLinearMap :=
    exteriorPower.linearMap_ext (AlternatingMap.ext fun x => h x)
  ext q
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk q
  have := LinearMap.congr_fun hlin (e.symm y)
  simpa using this

/-- The linearization of `m`, transported to `X`, as a bounded linear map. -/
noncomputable def linearizationCLM (m : E [⋀^Fin k]→L[K] F) : X →L[K] F :=
  ((exteriorLinearization m) ∘ₗ e.symm.toLinearMap).mkContinuous ‖m‖ fun y => by
    change ‖exteriorLinearization m (e.symm y)‖ ≤ ‖m‖ * ‖y‖
    have := norm_exteriorLinearization_le m (e.symm y)
    rwa [← he, LinearEquiv.apply_symm_apply] at this

/-- The descent of a bounded alternating map `m` to a bounded linear map on the separation
quotient. -/
noncomputable def lift (m : E [⋀^Fin k]→L[K] F) : SeparationQuotient X →L[K] F :=
  SeparationQuotient.liftCLM (linearizationCLM e he m) fun _ _ h =>
    (h.map (linearizationCLM e he m).continuous).eq

@[simp]
theorem lift_wedge (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E) : lift e he m (wedge e he x) = m x := by
  change exteriorLinearization m (e.symm (e (exteriorPower.ιMulti K k x))) = m x
  rw [LinearEquiv.symm_apply_apply, exteriorLinearization_ιMulti]

theorem norm_lift_le (m : E [⋀^Fin k]→L[K] F) : ‖lift e he m‖ ≤ ‖m‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m) fun q => ?_
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk q
  rw [SeparationQuotient.norm_mk]
  exact (linearizationCLM e he m).le_of_opNorm_le
    (LinearMap.mkContinuous_norm_le _ (norm_nonneg m) _) y

theorem norm_lift (m : E [⋀^Fin k]→L[K] F) : ‖lift e he m‖ = ‖m‖ := by
  refine le_antisymm (norm_lift_le e he m) ?_
  refine ContinuousAlternatingMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [← lift_wedge e he m x]
  refine ((lift e he m).le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left
    (((wedge e he).le_of_opNorm_le (norm_wedge_le e he) x).trans_eq (one_mul _)) (norm_nonneg _)

/-- Descent as a linear isometry `Alt^k(E; F) → L(Λ, F)`. -/
noncomputable def liftLinearIsometry : (E [⋀^Fin k]→L[K] F) →ₗᵢ[K] (SeparationQuotient X →L[K] F)
    where
  toFun := lift e he
  map_add' m m' := ext_wedge e he fun x => by simp
  map_smul' a m := ext_wedge e he fun x => by simp
  norm_map' := norm_lift e he

theorem lift_compContinuousAlternatingMap_wedge (T : SeparationQuotient X →L[K] F) :
    lift e he (T.compContinuousAlternatingMap (wedge e he)) = T :=
  ext_wedge e he fun x => by simp

/-- **Representation.** The linear isometric equivalence `Alt^k(E; F) ≃ L(Λ, F)` given by
descent, with inverse composition with the universal alternating map. -/
noncomputable def representation :
    (E [⋀^Fin k]→L[K] F) ≃ₗᵢ[K] (SeparationQuotient X →L[K] F) :=
  LinearIsometryEquiv.ofSurjective (liftLinearIsometry e he) fun T =>
    ⟨T.compContinuousAlternatingMap (wedge e he), lift_compContinuousAlternatingMap_wedge e he T⟩

@[simp]
theorem representation_apply_wedge (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    representation e he m (wedge e he x) = m x :=
  lift_wedge e he m x

include he in
theorem exists_representation (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F] :
    ∃ Φ : (E [⋀^Fin k]→L[K] F) ≃ₗᵢ[K] (SeparationQuotient X →L[K] F),
      ∀ (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E),
        Φ m (SeparationQuotient.mk (e (exteriorPower.ιMulti K k x))) = m x :=
  ⟨representation e he, representation_apply_wedge e he⟩

section Naturality

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace K D]
  {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace K Y]
  (eD : (⋀[K]^k D) ≃ₗ[K] Y) (heD : ∀ z, ‖eD z‖ = projectiveExteriorSeminorm z)

/-- The bounded linear map `Λ u : Λ_E → Λ_D` induced by `u : E → D`. -/
noncomputable def map (u : E →L[K] D) : SeparationQuotient X →L[K] SeparationQuotient Y :=
  lift e he ((wedge eD heD).compContinuousLinearMap u)

@[simp]
theorem map_wedge (u : E →L[K] D) (x : Fin k → E) :
    map e he eD heD u (wedge e he x) = wedge eD heD (u ∘ x) := by
  simp [map]

/-- The induced map satisfies `‖Λ u‖ ≤ ‖u‖ ^ k`. -/
theorem norm_map_le (u : E →L[K] D) : ‖map e he eD heD u‖ ≤ ‖u‖ ^ k :=
  calc ‖map e he eD heD u‖ ≤ ‖(wedge eD heD).compContinuousLinearMap u‖ := norm_lift_le e he _
    _ ≤ ‖wedge eD heD‖ * ‖u‖ ^ Fintype.card (Fin k) :=
      (wedge eD heD).norm_compContinuousLinearMap_le u
    _ ≤ 1 * ‖u‖ ^ k := by
      rw [Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (norm_wedge_le eD heD) (by positivity)
    _ = ‖u‖ ^ k := one_mul _

/-- Under descent, precomposition by `u` is precomposition by `Λ u`. -/
theorem lift_compContinuousLinearMap (u : E →L[K] D) (m : D [⋀^Fin k]→L[K] F) :
    lift e he (m.compContinuousLinearMap u) = (lift eD heD m).comp (map e he eD heD u) :=
  ext_wedge e he fun x => by simp

include he heD in
theorem exists_naturality (u : E →L[K] D) :
    ∃ Λu : SeparationQuotient X →L[K] SeparationQuotient Y,
      (∀ x : Fin k → E, Λu (SeparationQuotient.mk (e (exteriorPower.ιMulti K k x))) =
        SeparationQuotient.mk (eD (exteriorPower.ιMulti K k (u ∘ x)))) ∧
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
        (ΦE : (E [⋀^Fin k]→L[K] F) ≃ₗᵢ[K] (SeparationQuotient X →L[K] F))
        (ΦD : (D [⋀^Fin k]→L[K] F) ≃ₗᵢ[K] (SeparationQuotient Y →L[K] F)),
        (∀ (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E),
          ΦE m (SeparationQuotient.mk (e (exteriorPower.ιMulti K k x))) = m x) →
        (∀ (m : D [⋀^Fin k]→L[K] F) (x : Fin k → D),
          ΦD m (SeparationQuotient.mk (eD (exteriorPower.ιMulti K k x))) = m x) →
        ∀ m : D [⋀^Fin k]→L[K] F,
          ΦE (m.compContinuousLinearMap u) = (ΦD m).comp Λu := by
  refine ⟨map e he eD heD u, map_wedge e he eD heD u, ?_⟩
  intro F _ _ ΦE ΦD hE hD m
  refine ext_wedge e he fun x => ?_
  rw [ContinuousLinearMap.comp_apply, map_wedge, wedge_apply, wedge_apply, hE, hD]
  rfl

end Naturality

end AlternatingAnalytic.ExteriorRepresentation
