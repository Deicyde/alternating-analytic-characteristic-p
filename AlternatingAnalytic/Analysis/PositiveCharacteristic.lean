import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.FieldTheory.Finite.Basic

/-!
# Normed fields of positive characteristic are nonarchimedean

Lemma A.2: a normed field of prime characteristic `p` is ultrametric.
-/

/-- A normed field of prime characteristic is ultrametric. -/
theorem charP_isUltrametricDist {K : Type*} [NormedField K] (p : ℕ) [hp : Fact p.Prime]
    [CharP K p] : IsUltrametricDist K := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one (fun n => ?_)
  -- (n : K) lies in the prime field, so (n : K)^p = (n : K)
  have h1 : (n : K) ^ p = (n : K) := by
    have h := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card (n : ZMod p))
    rw [map_pow, map_natCast] at h
    exact h
  have h2 : ‖(n : K)‖ ^ p = ‖(n : K)‖ := by rw [← norm_pow, h1]
  by_contra h
  have h3 : ‖(n : K)‖ ^ 1 < ‖(n : K)‖ ^ p := pow_lt_pow_right₀ (not_le.mp h) hp.out.one_lt
  rw [pow_one, h2] at h3
  exact lt_irrefl _ h3
