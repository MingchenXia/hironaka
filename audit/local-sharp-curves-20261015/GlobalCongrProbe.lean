import Hironaka.Resolution.HironakaSmoothSubmersionNormalCrossings
open Lean
#check LinearEquiv.toContinuousLinearEquiv.congr_simp
run_cmd do
 let env ← getEnv
 let n := `LinearEquiv.toContinuousLinearEquiv.congr_simp
 match env.getModuleIdxFor? n with
 | some idx => logInfo m!"ACTUAL_GLOBAL_HELPER_OWNER {env.header.moduleNames[idx.toNat]!}"
 | none => throwError "missing global helper"
