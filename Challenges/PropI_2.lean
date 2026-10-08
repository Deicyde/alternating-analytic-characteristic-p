import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Proposition I.2 (continuous algebraic polynomials on c₀), pp. 62-63

Paper statement (Appendix I.2, `fam:prop:c0-algebraic`): Let `K` be nontrivially normed and
nonarchimedean, let `Z` be complete and nonarchimedean, and let `n ≥ 1`. Suppose
`p : c₀(I,K) → Z` is continuous and is an algebraic homogeneous polynomial: there exists a
`K`-multilinear map `b : c₀(I,K)^n → Z`, not assumed continuous, with `p(x) = b(x,…,x)`.
Then `p` has a bounded `n`-linear lift `q`. More precisely, there is `C_{K,n} < ∞`, independent
of `I, Z, p`, such that
`‖q‖ ≤ C_{K,n} ‖p‖_diag`, where `‖p‖_diag := inf {D ≥ 0 : ‖p(x)‖ ≤ D ‖x‖^n for all x}`.
No completeness assumption on `K` is needed.

## Formalization notes
* `c₀(I,K)` is Mathlib's `C₀(I, K)` (continuous functions vanishing at infinity) for an
  arbitrary index type `I` with the discrete topology, with its supremum norm. This is the
  same model of `c₀` used by the library's `CZero*` files.
* `K` is a `NontriviallyNormedField` with `[IsUltrametricDist K]`; it is not assumed complete.
  `Z` is a normed `K`-space with `[CompleteSpace Z]` and `[IsUltrametricDist Z]`.
* The algebraic polynomial hypothesis is `∃ b : MultilinearMap K (fun _ : Fin n => C₀(I,K)) Z,
  ∀ x, p x = b (fun _ => x)` (no continuity of `b`); continuity of `p` is `Continuous p`.
* A "bounded `n`-linear lift" is a `ContinuousMultilinearMap K (fun _ : Fin n => C₀(I,K)) Z`
  whose diagonal is `p`.
* `‖p‖_diag` is defined below as `diagNorm n p`, the real `sInf` of the set of admissible
  constants `D ≥ 0`. The paper's first proof step (`‖p‖_diag < ∞`) is stated as an explicit
  conjunct: the set of admissible constants is nonempty (so the `sInf` is the true infimum).
* Uniformity: the constant `C` is quantified after `K` and `n` and before `I`, `Z`, `p`, so it
  is independent of them; `I` and `Z` range over fixed (arbitrary) universes `uI`, `uZ`. The
  paper's `C_{K,n} < ∞` is a real number; `0 ≤ C` is added (harmless: the paper's constant
  `L_n^n ≥ 1`).
* Imports: Mathlib only; no library module is needed for the statement.
-/

open scoped ZeroAtInfty

namespace AlternatingAnalyticChallenge.PropI_2

universe uK uI uZ

/-- The diagonal norm `‖p‖_diag = inf {D ≥ 0 : ‖p x‖ ≤ D ‖x‖^n for all x}` of a map on a
normed space (a real `sInf`; it is the true infimum when the set is nonempty). -/
noncomputable def diagNorm {X : Type uI} {Z : Type uZ} [Norm X] [Norm Z] (n : ℕ)
    (p : X → Z) : ℝ :=
  sInf {D : ℝ | 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n}

/-- **Proposition I.2.** Over a nonarchimedean field `K` (not necessarily complete) and for
`n ≥ 1`, there is a constant `C` depending only on `K, n` such that every continuous algebraic
homogeneous polynomial `p : c₀(I,K) → Z` of degree `n`, into a complete nonarchimedean `Z`, has
finite diagonal norm and a bounded `n`-linear lift `q` with `‖q‖ ≤ C ‖p‖_diag`. -/
theorem exists_boundedLift_of_continuous_algebraicPolynomial
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Type uI) [TopologicalSpace I] [DiscreteTopology I]
        (Z : Type uZ) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
        [IsUltrametricDist Z] (p : C₀(I, K) → Z),
        Continuous p →
        (∃ b : MultilinearMap K (fun _ : Fin n => C₀(I, K)) Z, ∀ x, p x = b (fun _ => x)) →
        (∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n) ∧
        ∃ q : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z,
          (∀ x, q (fun _ => x) = p x) ∧ ‖q‖ ≤ C * diagNorm n p := by
  sorry

end AlternatingAnalyticChallenge.PropI_2
