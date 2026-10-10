import AlternatingAnalytic.Analysis.SphericalAnalytic
import AlternatingAnalytic.Analysis.AlternatingActionRegularity

/-!
# Targets with an equivalent spherically complete ultrametric norm

`ContinuousAlternatingMap.hasBoundedLift_of_sphericallyComplete` needs the norm of the target
to be ultrametric and spherically complete. Here the target `F` only carries an equivalent
seminorm `q` with these properties. We put `q` on the type synonym `WithSeminorm q` and transfer
the bounded lift back to `F`. Consequently the alternating action is a continuous polynomial for
such targets, as used in the first row of Corollary 4.6.
-/

open Metric

namespace AlternatingAnalytic.EquivalentSphericalNorm

variable {K F : Type*} [NontriviallyNormedField K] [NormedAddCommGroup F] [NormedSpace K F]

/-- The type `F` with the norm given by a seminorm `q`. -/
def WithSeminorm (_q : Seminorm K F) : Type _ := F

instance (q : Seminorm K F) : AddCommGroup (WithSeminorm q) := inferInstanceAs (AddCommGroup F)

instance (q : Seminorm K F) : Module K (WithSeminorm q) := inferInstanceAs (Module K F)

/-- The normed group structure on `WithSeminorm q` given by `q`, when `q` is definite. -/
noncomputable abbrev normedAddCommGroup (q : Seminorm K F) (hq : ∀ x, q x = 0 → x = 0) :
    NormedAddCommGroup (WithSeminorm q) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x : WithSeminorm q => q (x : F)
      map_zero' := map_zero q
      add_le' := fun x y => map_add_le_add q (x : F) y
      neg' := fun x => map_neg_eq_map q (x : F)
      eq_zero_of_map_eq_zero' := hq }

/-- The normed space structure on `WithSeminorm q` given by `q`. -/
noncomputable abbrev normedSpace (q : Seminorm K F) (hq : ∀ x, q x = 0 → x = 0) :
    letI := normedAddCommGroup q hq
    NormedSpace K (WithSeminorm q) :=
  letI := normedAddCommGroup q hq
  { norm_smul_le := fun a x => (map_smul_eq_mul q a (x : F)).le }

/-- A seminorm dominating a positive multiple of the norm is definite. -/
theorem eq_zero_of_seminorm_eq_zero (q : Seminorm K F) {C : ℝ} (hC : ∀ x, ‖x‖ ≤ C * q x)
    (x : F) (hx : q x = 0) : x = 0 :=
  norm_le_zero_iff.mp (by simpa [hx] using hC x)

variable [IsUltrametricDist K]

/-- If `F` carries a seminorm `q` equivalent to its norm, ultrametric, and such that
pairwise-intersecting families of closed `q`-balls have a common point, then precomposition on
`F`-valued alternating maps has a bounded multilinear lift. -/
theorem hasBoundedLift_of_equivalentSphericalNorm {ι : Type*} [Fintype ι]
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E'] (q : Seminorm K F)
    (hmax : ∀ x y, q (x + y) ≤ max (q x) (q y))
    (hlow : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * q x)
    (hup : ∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖)
    (hsph : ∀ S : Set (F × ℝ), S.Nonempty →
      (∀ p ∈ S, ∀ p' ∈ S, ∃ z, q (z - p.1) ≤ p.2 ∧ q (z - p'.1) ≤ p'.2) →
      ∃ z, ∀ p ∈ S, q (z - p.1) ≤ p.2) :
    LiftCriterion.HasBoundedLift K ι E E' F := by
  obtain ⟨C₁, hC₁, hlow⟩ := hlow
  obtain ⟨C₂, hC₂, hup⟩ := hup
  have hq := eq_zero_of_seminorm_eq_zero q hlow
  let := normedAddCommGroup q hq
  let := normedSpace q hq
  have hnorm : ∀ x : WithSeminorm q, ‖x‖ = q (x : F) := fun _ => rfl
  have : IsUltrametricDist (WithSeminorm q) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => hmax x y
  have : SphericallyCompleteSpace (WithSeminorm q) := by
    refine ⟨fun S hS hpair => ?_⟩
    have hmem : ∀ (z c : WithSeminorm q) (r : ℝ), z ∈ closedBall c r ↔ q ((z - c : F)) ≤ r :=
      fun z c r => by rw [mem_closedBall, dist_eq_norm, hnorm]
    obtain ⟨z, hz⟩ := hsph S hS fun p hp p' hp' => by
      obtain ⟨z, hz₁, hz₂⟩ := hpair p hp p' hp'
      exact ⟨z, (hmem _ _ _).mp hz₁, (hmem _ _ _).mp hz₂⟩
    exact ⟨z, Set.mem_iInter₂.mpr fun p hp => (hmem _ _ _).mpr (hz p hp)⟩
  let l : F ≃ₗ[K] WithSeminorm q := LinearEquiv.refl K F
  let e : F ≃L[K] WithSeminorm q :=
    l.toContinuousLinearEquivOfBounds C₂ C₁ (fun x => hup x) (fun x => hlow x)
  exact LiftCriterion.hasBoundedLift_of_retract (e : F →L[K] WithSeminorm q)
    (e.symm : WithSeminorm q →L[K] F) (fun y => e.symm_apply_apply y)
    ContinuousAlternatingMap.hasBoundedLift_of_sphericallyComplete

/-- The alternating action is a continuous polynomial when the target `F` admits an equivalent
spherically complete ultrametric norm. -/
theorem cpolynomialAt_alternatingMapAction_of_equivalentSphericalNorm
    {E E' F' : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E'] [NormedAddCommGroup F'] [NormedSpace K F']
    (q : Seminorm K F)
    (hmax : ∀ x y, q (x + y) ≤ max (q x) (q y))
    (hlow : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * q x)
    (hup : ∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖)
    (hsph : ∀ S : Set (F × ℝ), S.Nonempty →
      (∀ p ∈ S, ∀ p' ∈ S, ∃ z, q (z - p.1) ≤ p.2 ∧ q (z - p'.1) ≤ p'.2) →
      ∃ z, ∀ p ∈ S, q (z - p.1) ≤ p.2)
    (k : ℕ) (z₀ : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K (alternatingMapAction k) z₀ :=
  cpolynomialAt_alternatingMapAction_of_boundedLift k
    (hasBoundedLift_of_equivalentSphericalNorm q hmax hlow hup hsph) z₀

end AlternatingAnalytic.EquivalentSphericalNorm
