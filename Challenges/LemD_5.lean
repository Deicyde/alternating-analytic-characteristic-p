import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Lemma D.5 (extension), p. 42

Paper statement: "Let K ∈ {K₁, K′} and let C ≥ 0.
(1) Let V₀ be a dense K-subspace of a normed K-space V, let Y be a K-Banach space and
T₀ : V₀ → Y a K-linear map with ‖T₀ x‖ ≤ C‖x‖. Then T₀ extends uniquely to a continuous map
T : V → Y, which is K-linear with ‖T x‖ ≤ C‖x‖.
(2) Let V₁, …, V_k be normed K′-spaces with dense subspaces V_i⁰, Y a K′-Banach space, and
M : ∏ᵢ V_i⁰ → Y a K′-multilinear map with ‖M(d)‖ ≤ C ∏ᵢ ‖dᵢ‖. Then M extends uniquely to a
continuous K′-multilinear map M : ∏ᵢ Vᵢ → Y with ‖M‖ ≤ C."

Formalization notes:
* The field is an arbitrary `NontriviallyNormedField K`, in both parts. The paper only needs
  `K ∈ {K₁, K′}` (fields satisfying (H1)/(H2) of §D.2), and part (2) only `K = K′`; the Lean
  statements are therefore more general (no completeness or ultrametric hypothesis on `K`).
* "Dense K-subspace" is a `Submodule K V` whose carrier is `Dense`; a "K-Banach space" is a
  normed space with `CompleteSpace`.
* (1): the extension `T` is returned as a continuous linear map `V →L[K] Y` agreeing with
  `T₀` on `V₀` and bounded by `C‖x‖`; uniqueness is among all continuous maps `V → Y`
  agreeing with `T₀` on `V₀`, as in the paper ("extends uniquely to a continuous map").
* (2): the index set `{1, …, k}` is `Fin k`; all `Vᵢ` lie in one universe. The extension is a
  `ContinuousMultilinearMap K V Y` with operator norm `≤ C`; uniqueness is among continuous
  multilinear maps agreeing with `M` on `∏ Vᵢ⁰`.
* Universes of `K`, the `Vᵢ` and `Y` are independent.
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.LemD_5

universe uK uV uY

/-- **Lemma D.5(1).** A linear map `T₀ : V₀ → Y` from a dense subspace into a Banach space with
`‖T₀ x‖ ≤ C ‖x‖` extends uniquely to a continuous map `T : V → Y`; this extension is linear and
satisfies `‖T x‖ ≤ C ‖x‖`. -/
theorem part1
    (K : Type uK) [NontriviallyNormedField K]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace K V]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    (V₀ : Submodule K V) (hV₀ : Dense (V₀ : Set V)) (C : ℝ) (hC : 0 ≤ C)
    (T₀ : V₀ →ₗ[K] Y) (hT₀ : ∀ x : V₀, ‖T₀ x‖ ≤ C * ‖(x : V)‖) :
    ∃ T : V →L[K] Y, (∀ x : V₀, T x = T₀ x) ∧ (∀ x : V, ‖T x‖ ≤ C * ‖x‖) ∧
      ∀ T' : V → Y, Continuous T' → (∀ x : V₀, T' x = T₀ x) → T' = T := by
  sorry

/-- **Lemma D.5(2).** A multilinear map `M : ∏ Vᵢ⁰ → Y` on dense subspaces, with
`‖M d‖ ≤ C ∏ ‖dᵢ‖`, extends uniquely to a continuous multilinear map `∏ Vᵢ → Y` of norm
at most `C`. -/
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
