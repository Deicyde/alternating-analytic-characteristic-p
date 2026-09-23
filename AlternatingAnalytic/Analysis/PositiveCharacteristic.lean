/-
Positive prime characteristic forces a normed field to be ultrametric.

Source: round24/ultrametric-huge/lean/CharPUltrametric.lean, integrated on 2026-09-23.
The original root declaration `charP_isUltrametricDist` is retained.
Provenance and verification: planning/charp-paper/planning/integration-positive-manifest.json.
-/
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.FieldTheory.Finite.Basic

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
