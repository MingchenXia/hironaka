import TranscendentalNakamaye.FirstPass.ComplexAnalyticSubvarieties
import Hironaka.Analytic.ComplexAnalyticSubvarieties
open Lean
run_cmd do
  for n in #[``TranscendentalNakamaye.FirstPass.ComplexAnalyticPresentationAt,
      ``Hironaka.ComplexAnalyticPresentationAt,
      ``TranscendentalNakamaye.FirstPass.IsComplexManifold,
      ``Hironaka.IsComplexManifold,
      ``TranscendentalNakamaye.FirstPass.instIsComplexManifoldComplexModel,
      ``Hironaka.instIsComplexManifoldComplexModel] do
    let ci ← getConstInfo n
    let used := ci.type.getUsedConstants
    logInfo m!"{n} type: CSTAR={used.contains `instCommCStarAlgebraComplex}; FIELD={used.contains `Complex.instNormedField}"
