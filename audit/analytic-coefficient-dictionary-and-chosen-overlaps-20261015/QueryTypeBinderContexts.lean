import TranscendentalNakamaye.Pending.RemmertSteinFlat
import Hironaka.Analytic.RemmertSteinFlat
open Lean
partial def reportBinder (e : Expr) : Elab.Command.CommandElabM Unit := do
  match e with
  | .forallE n ty body _ =>
    let used := ty.getUsedConstants
    logInfo m!"{n}: CSTAR={used.contains `instCommCStarAlgebraComplex}; FIELD={used.contains `Complex.instNormedField}"
    reportBinder body
  | _ =>
    let used := e.getUsedConstants
    logInfo m!"RESULT: CSTAR={used.contains `instCommCStarAlgebraComplex}; FIELD={used.contains `Complex.instNormedField}"
run_cmd do
  for n in #[``TranscendentalNakamaye.Pending.RemmertSteinFlat.remmertStein_flat_pure,
      ``Hironaka.RemmertSteinFlat.remmertStein_flat_pure] do
    logInfo m!"DECL {n}"
    reportBinder (← getConstInfo n).type
