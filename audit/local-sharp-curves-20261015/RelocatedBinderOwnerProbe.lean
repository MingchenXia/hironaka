import Hironaka.Blowup.BlowupDerivativeMaximalOrder
import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.Support.ControlledOriginalContextExact
import Hironaka.Support.FiniteSpanRangeExact
import Hironaka.Support.NonmonomialOrderTailExact
import Hironaka.Support.SharpGeometryExact
import Hironaka.Support.StepOneDropExact
open Lean Elab Command
partial def contextNames (e : Expr) : Array Name :=
  match e with
  | .lam n t b _ | .forallE n t b _ => #[n] ++ contextNames t ++ contextNames b
  | .letE n t v b _ => #[n] ++ contextNames t ++ contextNames v ++ contextNames b
  | .app f a => contextNames f ++ contextNames a
  | .mdata _ b | .proj _ _ b => contextNames b
  | _ => #[]
run_cmd do
  let env ← getEnv
  for (m, scope) in #[(`Hironaka.Support.FiniteSpanRangeExact,1599403507),
      (`Hironaka.Support.NonmonomialOrderTailExact,723325965),
      (`Hironaka.Support.NonmonomialOrderTailExact,1599678574),
      (`Hironaka.Support.ControlledOriginalContextExact,3899023525),
      (`Hironaka.Support.StepOneDropExact,1711675205),
      (`Hironaka.Blowup.BlowupDerivativeMaximalOrder,632439324),
      (`Hironaka.Blowup.BlowupDerivativeMaximalOrder,2991156678),
      (`Hironaka.Support.SharpGeometryExact,927828394),
      (`Hironaka.MarkedIdeal.GermIdealOrderValue,3638836085)] do
    let some idx := env.header.moduleNames.findIdx? (· == m) | throwError "owner missing {m}"
    let mut count := 0
    for ci in env.header.moduleData[idx]!.constants do
      let names := contextNames ci.type ++ ((ci.value? (allowOpaque := true)).map contextNames).getD #[]
      for name in names do
        if (name.toString.splitOn s!"{m}.{scope}._hygCtx").length > 1 then
          logInfo m!"ACTUAL_IMPORTED_OWNER {m}; scope {scope}; declaration {ci.name}; exact binder {name}"
          count := count + 1
    if count == 0 then throwError "No actual imported binder context witness {m}/{scope}"
