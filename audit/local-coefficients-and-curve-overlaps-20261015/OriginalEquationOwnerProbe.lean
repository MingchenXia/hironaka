import TranscendentalNakamaye.Pending.HironakaOriginalInvariantEmptyInsertion
import Hironaka.Resolution.HironakaOriginalInvariantEmptyInsertion
open Lean
run_cmd do
  let env ← getEnv
  for n in #[`TranscendentalNakamaye.Pending.MarkedIdealOperationsTransform.MarkedIdeal.add.eq_1,
      `Hironaka.MarkedIdealOperationsTransform.MarkedIdeal.add.eq_1] do
    let some ci := env.find? n | throwError "Missing actual equation theorem {n}"
    let some idx := env.getModuleIdxFor? n | throwError "Missing owner {n}"
    logInfo m!"ACTUAL_OWNER {n}: {env.header.moduleNames[idx.toNat]!}; kind {ci.name}"
