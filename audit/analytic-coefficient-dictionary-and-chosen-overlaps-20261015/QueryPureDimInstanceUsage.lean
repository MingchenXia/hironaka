import TranscendentalNakamaye.Pending.AnalyticDimensionBasics
import Hironaka.Analytic.GeometricPureDimension
import Hironaka.Analytic.AnalyticSubsetOpens
import TranscendentalNakamaye.Pending.AnalyticSubsetOpens
open Lean
run_cmd do
  for n in #[``TranscendentalNakamaye.Pending.AnalyticDimensionBasics.IsPureDim,
      ``Hironaka.AnalyticDimensionBasics.IsPureDim,
      ``TranscendentalNakamaye.Pending.AnalyticSubsetOpens.instIsComplexManifoldOpens,
      ``Hironaka.AnalyticSubsetOpens.instIsComplexManifoldOpens] do
    let ci ← getConstInfo n
    let used := ci.type.getUsedConstants
    logInfo m!"{n} type: CSTAR={used.contains `instCommCStarAlgebraComplex}; FIELD={used.contains `Complex.instNormedField}"
set_option pp.all true in
#print Hironaka.AnalyticDimensionBasics.IsPureDim
set_option pp.all true in
#print TranscendentalNakamaye.Pending.AnalyticDimensionBasics.IsPureDim
