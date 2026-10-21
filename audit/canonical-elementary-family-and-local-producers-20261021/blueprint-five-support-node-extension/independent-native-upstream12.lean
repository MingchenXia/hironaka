import TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents
import TranscendentalNakamaye.Pending.EmbeddedFromResolution
import TranscendentalNakamaye.Pending.StepOneWellFounded

open Lean
set_option pp.all true
run_cmd do
  let env ← getEnv
  let pairs : Array (Name × Name) := #[(`TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents.exists_subvariety_univ, `TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents), (`TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents.eq_of_regularAtDim_univ, `TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents), (`TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents.dim_eq_of_carrier_eq_univ, `TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents), (`TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents.eq_univ_of_isClosedConnectedSubmanifold_self, `TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents), (`TranscendentalNakamaye.Pending.EmbeddedFromResolution.mem_regularOpen_iff, `TranscendentalNakamaye.Pending.EmbeddedFromResolution), (`TranscendentalNakamaye.Pending.EmbeddedFromResolution.strictTransform_eq_connectedComponentIn, `TranscendentalNakamaye.Pending.EmbeddedFromResolution), (`TranscendentalNakamaye.Pending.EmbeddedFromResolution.strictTransform_eq_connectedComponentIn_maxLocus, `TranscendentalNakamaye.Pending.EmbeddedFromResolution), (`TranscendentalNakamaye.Pending.StepOneWellFounded.stepDrop_of_resolutionInvariant, `TranscendentalNakamaye.Pending.StepOneWellFounded), (`TranscendentalNakamaye.Pending.StepOneWellFounded.exists_isGeoResolution_of_wellFoundedLT, `TranscendentalNakamaye.Pending.StepOneWellFounded), (`TranscendentalNakamaye.Pending.StepOneWellFounded.stepOneInvM_lt_of_isCanonical_append, `TranscendentalNakamaye.Pending.StepOneWellFounded), (`TranscendentalNakamaye.Pending.StepOneWellFounded.isAdmissibleCentre_maxLocus_stepOneInvM, `TranscendentalNakamaye.Pending.StepOneWellFounded), (`TranscendentalNakamaye.Pending.StepOneWellFounded.exists_isGeoResolution_stepOneInvM, `TranscendentalNakamaye.Pending.StepOneWellFounded)]
  let mut total : Nat := 0
  for (decl, target) in pairs do
    let some idx := env.header.moduleNames.findIdx? (· == target)
      | throwError "Missing actual module {target}"
    unless env.header.moduleData[idx]!.constants.any (fun ci => ci.name == decl) do
      throwError "Declaration {decl} is not an actual metadata root of {target}"
    let some ci := env.find? decl
      | throwError "Missing original actual constant {decl}"
    let axs ← collectAxioms decl
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Nonstandard axiom {ax} in {decl}"
    logInfo m!"UPSTREAM_WITNESS {decl} OWNER {target} AXIOMS {axs}"
    logInfo m!"UPSTREAM_TYPE {decl} : {ci.type}"
    total := total + 1
  logInfo m!"UPSTREAM_WITNESSES {total} actual owned constants; standard axioms only"
