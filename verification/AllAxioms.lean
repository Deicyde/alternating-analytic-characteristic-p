import Lean
import solution
import AlternatingAnalytic
import AlternatingAnalytic.Algebra.ClusterCancellation
import AlternatingAnalytic.Algebra.ClusterDiagonal
import AlternatingAnalytic.Algebra.ClusterStaircase
import AlternatingAnalytic.Algebra.ClusterValues
import AlternatingAnalytic.Algebra.ClusterWeights
import AlternatingAnalytic.Algebra.DeterminantArray
import AlternatingAnalytic.Algebra.ExteriorBlocks
import AlternatingAnalytic.Algebra.ExteriorContraction
import AlternatingAnalytic.Algebra.ExteriorFlattening
import AlternatingAnalytic.Algebra.ExteriorSupport
import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import AlternatingAnalytic.Algebra.FiniteFieldObstruction
import AlternatingAnalytic.Algebra.FiniteFieldTheorem
import AlternatingAnalytic.Algebra.FiniteHomogeneousIdentity
import AlternatingAnalytic.Algebra.FullPolarization
import AlternatingAnalytic.Algebra.InfiniteRamsey
import AlternatingAnalytic.Algebra.MultiplierObstruction
import AlternatingAnalytic.Algebra.NormalizedMultiplierLift
import AlternatingAnalytic.Algebra.OperatorSymbol
import AlternatingAnalytic.Algebra.OrderPattern
import AlternatingAnalytic.Algebra.Polarization
import AlternatingAnalytic.Algebra.PolarizationCounterexamples
import AlternatingAnalytic.Algebra.PolynomialIdentity
import AlternatingAnalytic.Algebra.StaircaseRank
import AlternatingAnalytic.Algebra.SymmetricDiagonal
import AlternatingAnalytic.Algebra.TensorSupport
import AlternatingAnalytic.Analysis.BaseChangeAlternatingCriterion
import AlternatingAnalytic.Analysis.BaseChangeAlternatingForms
import AlternatingAnalytic.Analysis.BaseChangeLiftDescent
import AlternatingAnalytic.Analysis.BaseChangeOperators
import AlternatingAnalytic.Analysis.CompletedBaseChange
import AlternatingAnalytic.Analysis.DenseCoefficientExtension
import AlternatingAnalytic.Analysis.DenseIsometricExtension
import AlternatingAnalytic.Analysis.DenseMultilinearExtension
import AlternatingAnalytic.Analysis.DenseMultilinearFamilyExtension
import AlternatingAnalytic.Analysis.DenseScalarLiftTransport
import AlternatingAnalytic.Analysis.DenseScalarRestriction
import AlternatingAnalytic.Analysis.DiscreteNormRounding
import AlternatingAnalytic.Analysis.DiscreteSphericalCompleteness
import AlternatingAnalytic.Analysis.DiscreteSupNorm
import AlternatingAnalytic.Analysis.DiscreteTargetAnalytic
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.Analysis.ExteriorCoefficientGrowth
import AlternatingAnalytic.Analysis.FactorialClassification
import AlternatingAnalytic.Analysis.FactorialInvertible
import AlternatingAnalytic.Analysis.FiniteFieldNorm
import AlternatingAnalytic.Analysis.GeometricWeightBound
import AlternatingAnalytic.Analysis.Homogeneous
import AlternatingAnalytic.Analysis.LaurentAlgebraicCoefficient
import AlternatingAnalytic.Analysis.LaurentBlockNorms
import AlternatingAnalytic.Analysis.LaurentCoefficientTheorem
import AlternatingAnalytic.Analysis.LaurentCoefficients
import AlternatingAnalytic.Analysis.LaurentCompletedCoefficient
import AlternatingAnalytic.Analysis.LaurentEvaluation
import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.LaurentMultilinearStability
import AlternatingAnalytic.Analysis.LaurentMultipliers
import AlternatingAnalytic.Analysis.LaurentNorm
import AlternatingAnalytic.Analysis.LaurentPolynomials
import AlternatingAnalytic.Analysis.LaurentResidueLift
import AlternatingAnalytic.Analysis.LaurentResiduePolarization
import AlternatingAnalytic.Analysis.LaurentResidueTheorem
import AlternatingAnalytic.Analysis.LaurentSubfield
import AlternatingAnalytic.Analysis.LaurentSubfieldProperties
import AlternatingAnalytic.Analysis.LaurentTruncation
import AlternatingAnalytic.Analysis.LaurentWedgeCoefficient
import AlternatingAnalytic.Analysis.LiftCriterion
import AlternatingAnalytic.Analysis.NonUltrametricAnalyticExample
import AlternatingAnalytic.Analysis.NonsphericalSequence
import AlternatingAnalytic.Analysis.PolynomialEvaluationNorm
import AlternatingAnalytic.Analysis.PositiveCharacteristic
import AlternatingAnalytic.Analysis.PrescribedLaurentBase
import AlternatingAnalytic.Analysis.ProjectiveBaseChange
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Analysis.ScalarProjection
import AlternatingAnalytic.Analysis.SortedBasisAnalytic
import AlternatingAnalytic.Analysis.SortedBasisExpansion
import AlternatingAnalytic.Analysis.SortedBasisFormula
import AlternatingAnalytic.Analysis.SortedBasisLift
import AlternatingAnalytic.Analysis.SortedBasisRetraction
import AlternatingAnalytic.Analysis.SortedBasisSummability
import AlternatingAnalytic.Analysis.SphericalAnalytic
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Analysis.UnitSumGrowth
import AlternatingAnalytic.Analysis.WeightedDeterminantBound
import AlternatingAnalytic.Main
import AlternatingAnalytic.MainTheorem
import AlternatingAnalytic.Preflight
namespace AutoformVerify

open Lean

structure AxiomState where
  visited : NameSet := {}
  axioms : Array Name := #[]

abbrev AxiomM := ReaderT Environment (StateM AxiomState)

partial def collectAxiomsCompat (c : Name) : AxiomM Unit := do
  let collectExpr (e : Expr) : AxiomM Unit :=
    e.getUsedConstants.forM collectAxiomsCompat
  let state ← get
  unless state.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    match env.find? c with
    | some (ConstantInfo.axiomInfo _) =>
        modify fun s => { s with axioms := s.axioms.push c }
    | some (ConstantInfo.defnInfo v) => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.thmInfo v) => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.quotInfo _) => pure ()
    | some (ConstantInfo.ctorInfo v) => collectExpr v.type
    | some (ConstantInfo.recInfo v) => collectExpr v.type
    | some (ConstantInfo.inductInfo v) => collectExpr v.type *> v.ctors.forM collectAxiomsCompat
    | none => pure ()

def axiomsOf (env : Environment) (nm : Name) : Array Name :=
  let (_, state) := ((collectAxiomsCompat nm).run env).run {}
  state.axioms

end AutoformVerify

open Lean in
run_cmd do
  let env ← getEnv
  let mods : List Name := [`solution, `AlternatingAnalytic, `AlternatingAnalytic.Algebra.ClusterCancellation, `AlternatingAnalytic.Algebra.ClusterDiagonal, `AlternatingAnalytic.Algebra.ClusterStaircase, `AlternatingAnalytic.Algebra.ClusterValues, `AlternatingAnalytic.Algebra.ClusterWeights, `AlternatingAnalytic.Algebra.DeterminantArray, `AlternatingAnalytic.Algebra.ExteriorBlocks, `AlternatingAnalytic.Algebra.ExteriorContraction, `AlternatingAnalytic.Algebra.ExteriorFlattening, `AlternatingAnalytic.Algebra.ExteriorSupport, `AlternatingAnalytic.Algebra.ExteriorSupportDimension, `AlternatingAnalytic.Algebra.FiniteFieldObstruction, `AlternatingAnalytic.Algebra.FiniteFieldTheorem, `AlternatingAnalytic.Algebra.FiniteHomogeneousIdentity, `AlternatingAnalytic.Algebra.FullPolarization, `AlternatingAnalytic.Algebra.InfiniteRamsey, `AlternatingAnalytic.Algebra.MultiplierObstruction, `AlternatingAnalytic.Algebra.NormalizedMultiplierLift, `AlternatingAnalytic.Algebra.OperatorSymbol, `AlternatingAnalytic.Algebra.OrderPattern, `AlternatingAnalytic.Algebra.Polarization, `AlternatingAnalytic.Algebra.PolarizationCounterexamples, `AlternatingAnalytic.Algebra.PolynomialIdentity, `AlternatingAnalytic.Algebra.StaircaseRank, `AlternatingAnalytic.Algebra.SymmetricDiagonal, `AlternatingAnalytic.Algebra.TensorSupport, `AlternatingAnalytic.Analysis.BaseChangeAlternatingCriterion, `AlternatingAnalytic.Analysis.BaseChangeAlternatingForms, `AlternatingAnalytic.Analysis.BaseChangeLiftDescent, `AlternatingAnalytic.Analysis.BaseChangeOperators, `AlternatingAnalytic.Analysis.CompletedBaseChange, `AlternatingAnalytic.Analysis.DenseCoefficientExtension, `AlternatingAnalytic.Analysis.DenseIsometricExtension, `AlternatingAnalytic.Analysis.DenseMultilinearExtension, `AlternatingAnalytic.Analysis.DenseMultilinearFamilyExtension, `AlternatingAnalytic.Analysis.DenseScalarLiftTransport, `AlternatingAnalytic.Analysis.DenseScalarRestriction, `AlternatingAnalytic.Analysis.DiscreteNormRounding, `AlternatingAnalytic.Analysis.DiscreteSphericalCompleteness, `AlternatingAnalytic.Analysis.DiscreteSupNorm, `AlternatingAnalytic.Analysis.DiscreteTargetAnalytic, `AlternatingAnalytic.Analysis.EquivalentUltrametric, `AlternatingAnalytic.Analysis.ExteriorCoefficientGrowth, `AlternatingAnalytic.Analysis.FactorialClassification, `AlternatingAnalytic.Analysis.FactorialInvertible, `AlternatingAnalytic.Analysis.FiniteFieldNorm, `AlternatingAnalytic.Analysis.GeometricWeightBound, `AlternatingAnalytic.Analysis.Homogeneous, `AlternatingAnalytic.Analysis.LaurentAlgebraicCoefficient, `AlternatingAnalytic.Analysis.LaurentBlockNorms, `AlternatingAnalytic.Analysis.LaurentCoefficientTheorem, `AlternatingAnalytic.Analysis.LaurentCoefficients, `AlternatingAnalytic.Analysis.LaurentCompletedCoefficient, `AlternatingAnalytic.Analysis.LaurentEvaluation, `AlternatingAnalytic.Analysis.LaurentField, `AlternatingAnalytic.Analysis.LaurentMultilinearStability, `AlternatingAnalytic.Analysis.LaurentMultipliers, `AlternatingAnalytic.Analysis.LaurentNorm, `AlternatingAnalytic.Analysis.LaurentPolynomials, `AlternatingAnalytic.Analysis.LaurentResidueLift, `AlternatingAnalytic.Analysis.LaurentResiduePolarization, `AlternatingAnalytic.Analysis.LaurentResidueTheorem, `AlternatingAnalytic.Analysis.LaurentSubfield, `AlternatingAnalytic.Analysis.LaurentSubfieldProperties, `AlternatingAnalytic.Analysis.LaurentTruncation, `AlternatingAnalytic.Analysis.LaurentWedgeCoefficient, `AlternatingAnalytic.Analysis.LiftCriterion, `AlternatingAnalytic.Analysis.NonUltrametricAnalyticExample, `AlternatingAnalytic.Analysis.NonsphericalSequence, `AlternatingAnalytic.Analysis.PolynomialEvaluationNorm, `AlternatingAnalytic.Analysis.PositiveCharacteristic, `AlternatingAnalytic.Analysis.PrescribedLaurentBase, `AlternatingAnalytic.Analysis.ProjectiveBaseChange, `AlternatingAnalytic.Analysis.ProjectiveExterior, `AlternatingAnalytic.Analysis.ScalarProjection, `AlternatingAnalytic.Analysis.SortedBasisAnalytic, `AlternatingAnalytic.Analysis.SortedBasisExpansion, `AlternatingAnalytic.Analysis.SortedBasisFormula, `AlternatingAnalytic.Analysis.SortedBasisLift, `AlternatingAnalytic.Analysis.SortedBasisRetraction, `AlternatingAnalytic.Analysis.SortedBasisSummability, `AlternatingAnalytic.Analysis.SphericalAnalytic, `AlternatingAnalytic.Analysis.SphericalCompleteness, `AlternatingAnalytic.Analysis.UnitSumGrowth, `AlternatingAnalytic.Analysis.WeightedDeterminantBound, `AlternatingAnalytic.Main, `AlternatingAnalytic.MainTheorem, `AlternatingAnalytic.Preflight]
  let idxs := mods.filterMap env.getModuleIdx?
  unless idxs.length == mods.length do
    throwError "A library module is missing from the imported environment"
  let mut roots : Array Name := #[]
  for (nm, _ci) in env.constants.toList do
    if let some i := env.getModuleIdxFor? nm then
      if idxs.contains i then
        roots := roots.push nm
  let (_, state) := ((roots.forM AutoformVerify.collectAxiomsCompat).run env).run {}
  for nm in roots do
    logInfo m!"AUDITED_DECL {nm}"
  logInfo m!"AXIOMS_OF_ALL_DECLARATIONS {state.axioms.toList}"
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  unless state.axioms.all (fun nm => allowed.contains nm) do
    throwError "Nonstandard axiom found in the library's transitive dependency closure"
  unless roots.size > 0 do
    throwError "No owned declarations were selected"
  logInfo m!"ALL_DECLARATIONS_PROBE_OK decls={roots.size}"
