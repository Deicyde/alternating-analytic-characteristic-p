import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic

open scoped lp BigOperators

namespace L1Coordinates

variable {K J : Type*} [NontriviallyNormedField K]

/-- In ordinary `ℓ¹`, the coordinate norms sum to the norm, with no completeness
assumption on the scalar field. -/
theorem hasSum_norm (x : lp (fun _ : J => K) 1) :
    HasSum (fun j => ‖x j‖) ‖x‖ := by
  simpa using lp.hasSum_norm (p := 1) (by simp) x

/-- The arbitrary-index product of the real coordinate-norm series.  The
induction includes the unique empty tuple in degree zero. -/
theorem hasSum_prod_norm (d : ℕ) (x : Fin d → lp (fun _ : J => K) 1) :
    HasSum (fun a : Fin d → J => ∏ r, ‖x r (a r)‖) (∏ r, ‖x r‖) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have h₀ := hasSum_norm (x 0)
      have ht := ih (fun r => x r.succ)
      have hs := h₀.summable.mul_of_nonneg ht.summable
        (fun j => norm_nonneg (x 0 j))
        (fun a => Finset.prod_nonneg fun r _ => norm_nonneg (x r.succ (a r)))
      have hp := h₀.mul ht hs
      apply (Fin.consEquiv (fun _ : Fin (d + 1) => J)).hasSum_iff.mp
      simpa [Fin.prod_univ_succ, Fin.consEquiv, Function.comp_def] using hp

end L1Coordinates
