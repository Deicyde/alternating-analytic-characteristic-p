import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Lemma D.5 (extension), p. 45

Paper statement: "Let K ∈ {K₁, K′} and let C ≥ 0.
(1) Let V₀ be a dense K-subspace of a normed K-space V, let Y be a K-Banach space and
T₀ : V₀ → Y a K-linear map with ‖T₀ x‖ ≤ C‖x‖. Then T₀ extends uniquely to a continuous map
T : V → Y, which is K-linear with ‖T x‖ ≤ C‖x‖.
(2) Let V₁, …, V_k be normed K′-spaces with dense subspaces V_i⁰, Y a K′-Banach space, and
M : ∏ᵢ V_i⁰ → Y a K′-multilinear map with ‖M(d)‖ ≤ C ∏ᵢ ‖dᵢ‖. Then M extends uniquely to a
continuous K′-multilinear map M : ∏ᵢ Vᵢ → Y with ‖M‖ ≤ C."

## Formalization notes

* The field is any `NontriviallyNormedField K` in both parts; the paper needs only
  `K ∈ {K₁, K′}`.
* A dense subspace is a `Submodule K V` with `Dense` carrier; a Banach space is a normed space
  with `CompleteSpace`.
* (1): uniqueness is among all continuous maps `V → Y` that agree with `T₀` on `V₀`.
* (2): the index set is `Fin k`; uniqueness is among continuous multilinear maps that agree
  with `M` on `∏ Vᵢ⁰`.
-/

namespace AlternatingAnalyticChallenge.LemD_5

universe uK uV uY

/-- A linear map `T₀ : V₀ → Y` on a dense subspace with `‖T₀ x‖ ≤ C ‖x‖` extends uniquely to
a continuous map `V → Y`, which is linear and satisfies the same bound. -/
theorem part1
    (K : Type uK) [NontriviallyNormedField K]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace K V]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    (V₀ : Submodule K V) (hV₀ : Dense (V₀ : Set V)) (C : ℝ) (hC : 0 ≤ C)
    (T₀ : V₀ →ₗ[K] Y) (hT₀ : ∀ x : V₀, ‖T₀ x‖ ≤ C * ‖(x : V)‖) :
    ∃ T : V →L[K] Y, (∀ x : V₀, T x = T₀ x) ∧ (∀ x : V, ‖T x‖ ≤ C * ‖x‖) ∧
      ∀ T' : V → Y, Continuous T' → (∀ x : V₀, T' x = T₀ x) → T' = T := by
  sorry

/-- A multilinear map on dense subspaces with `‖M d‖ ≤ C ∏ ‖dᵢ‖` extends uniquely to a
continuous multilinear map of norm at most `C`. -/
theorem part2
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    {V : Fin k → Type uV} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace K (V i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    (V₀ : ∀ i, Submodule K (V i)) (hV₀ : ∀ i, Dense (V₀ i : Set (V i))) (C : ℝ) (hC : 0 ≤ C)
    (M : MultilinearMap K (fun i => V₀ i) Y)
    (hM : ∀ d : ∀ i, V₀ i, ‖M d‖ ≤ C * ∏ i, ‖(d i : V i)‖) :
    ∃ M' : ContinuousMultilinearMap K V Y,
      (∀ d : ∀ i, V₀ i, M' (fun i => (d i : V i)) = M d) ∧ ‖M'‖ ≤ C ∧
      ∀ M'' : ContinuousMultilinearMap K V Y,
        (∀ d : ∀ i, V₀ i, M'' (fun i => (d i : V i)) = M d) → M'' = M' := by
  sorry

end AlternatingAnalyticChallenge.LemD_5
