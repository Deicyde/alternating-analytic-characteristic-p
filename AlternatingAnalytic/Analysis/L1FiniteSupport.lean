import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Finite-support approximation in ordinary ℓ¹

Finite coordinate expansions and approximation for continuous multilinear maps on the
ordinary sum-norm `lp` space. No completeness of the scalar field or domain is used.
-/

open scoped BigOperators lp
open Filter Topology

noncomputable section

namespace L1Coordinates

variable {K J W : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup W] [NormedSpace K W] {d : ℕ}

local instance : DecidableEq J := Classical.decEq J

/-- Expand a continuous multilinear map on finite coordinate truncations. -/
theorem map_sum_single
    (C : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) W)
    (x : Fin d → J → K) (s : Fin d → Finset J) :
    C (fun r => ∑ j ∈ s r, lp.single 1 j (x r j)) =
      ∑ a ∈ Fintype.piFinset s,
        (∏ r, x r (a r)) • C (fun r => lp.single 1 (a r) (1 : K)) := by
  classical
  rw [C.map_sum_finset]
  apply Finset.sum_congr rfl
  intro a ha
  have hsingle (r : Fin d) :
      lp.single (E := fun _ : J => K) 1 (a r) (x r (a r)) =
        x r (a r) • lp.single 1 (a r) (1 : K) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : J => K) 1 (a r) (x r (a r)) (1 : K))
  simp only [hsingle, C.map_smul_univ]

/-- Common finite coordinate truncations converge in the ordinary ℓ¹ norm, even over an
incomplete scalar field. -/
theorem tendsto_sum_single (x : Fin d → lp (fun _ : J => K) 1) :
    Tendsto (fun s : Finset J => fun r : Fin d => ∑ j ∈ s, lp.single 1 j (x r j))
      atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro r
  exact lp.hasSum_single (by simp) (x r)

/-- Continuous multilinear maps respect the canonical finite coordinate approximation. -/
theorem tendsto_map_sum_single
    (C : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) W)
    (x : Fin d → lp (fun _ : J => K) 1) :
    Tendsto (fun s : Finset J => C (fun r => ∑ j ∈ s, lp.single 1 j (x r j)))
      atTop (𝓝 (C x)) :=
  C.cont.continuousAt.tendsto.comp (tendsto_sum_single x)

end L1Coordinates
