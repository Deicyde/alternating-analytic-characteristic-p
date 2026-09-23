import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

/-! Shared vocabulary for the comparator challenge, defined entirely in Mathlib terms.
These definitions are independent of the proof library. -/

namespace AlternatingAnalyticChallenge

universe u v

/-- A complete normed `K`-vector space whose carrier lives in the same universe as `K`.
The norm need not be ultrametric, and `K` need not be complete. -/
structure BanachSpace (K : Type u) [NontriviallyNormedField K] : Type (u + 1) where
  /-- Bundle an existing complete normed space. -/
  of ::
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace K carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] BanachSpace.normedAddCommGroup BanachSpace.normedSpace
  BanachSpace.completeSpace

instance (K : Type u) [NontriviallyNormedField K] : CoeSort (BanachSpace K) (Type u) where
  coe E := E.carrier

/-- The precomposition map `Q`: it sends `f : E →L[K] E'` to the operator
`m ↦ m ∘ (f, …, f)` on continuous alternating forms indexed by `ι`. -/
noncomputable def precomposition (K : Type u) [NontriviallyNormedField K]
    (ι : Type v) [Fintype ι] (E E' F : BanachSpace K) :
    (E →L[K] E') → (E' [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM

/-- A bounded multilinear lift of `Q` is a continuous `card ι`-linear map whose
diagonal is `Q`. It takes values in operators between alternating-form spaces. -/
def HasBoundedLift (K : Type u) [NontriviallyNormedField K]
    (ι : Type v) [Fintype ι] (E E' F : BanachSpace K) : Prop :=
  ∃ P : ContinuousMultilinearMap K (fun _ : Fin (Fintype.card ι) => E →L[K] E')
      ((E' [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F)),
    ∀ f, P (fun _ => f) = precomposition K ι E E' F f

/-- An equivalent ultrametric norm is a `K`-seminorm satisfying the strong triangle
inequality and positive two-sided bounds against the given norm. The lower bound
makes it nondegenerate. -/
def HasEquivalentUltrametricNorm (K : Type u) [NontriviallyNormedField K]
    (F : BanachSpace K) : Prop :=
  ∃ q : Seminorm K F,
    (∀ x y, q (x + y) ≤ max (q x) (q y)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * q x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖)

end AlternatingAnalyticChallenge
