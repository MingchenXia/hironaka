import DeJongAlterations.StableModification.DeJong.BaseStep
import DeJongAlterations.StableModification.DeJong.Fibration
import DeJongAlterations.StableModification.DeJong.Induction
import DeJongAlterations.StableModification.Perfection.Global
import DeJongAlterations.StableModification.Flattening.Main
import DeJongAlterations.StableModification.Resolution.GlobalResolution

/-!
# De Jong's Theorem 4.1 over algebraically closed fields: what remains

The base step `baseStep : BaseStep k` (de Jong 4.22 with Temkin) is proved unconditionally, so the
conditional induction `deJongAlterationTheorem_of_producers` reduces `DeJongAlterationTheorem k`
for algebraically closed `k` to the remaining producer propositions of `Interface.lean`
(and, in characteristic `p`, `Fibration.lean`):

* `PurelyInseparableSmoothing k` (now proved: `Perfection.purelyInseparableSmoothing`),
* `FlatteningAfterGEAlteration k` (weak de Jong 2.19; now proved: `Flattening.flatteningAfterGEAlteration`),
* `TemkinStableModification k` (Temkin's Theorems 1.1 and 1.5, consumed form),
* `SemistableResolution k` (de Jong 4.23–4.28 with 3.1–3.5 and the 2.4 strictification; now proved:
  `Resolution.Global.semistableResolution`).

These are `def … : Prop` statements, not axioms; the theorems below take them as explicit hypotheses.
`deJongAlterationTheorem_of_flattening_stableModification_resolution` uses the proved smoothing, and
`deJongAlterationTheorem_of_stableModification_resolution` also the proved flattening, and
`deJongAlterationTheorem_of_stableModification` also the proved resolution, so only
`TemkinStableModification k` remains.
-/

namespace DeJongAlterations.StableModification.DeJong

universe u

variable {k : Type u} [Field k]

/-- De Jong 4.1 over an algebraically closed field from the four remaining producers. -/
theorem deJongAlterationTheorem_of_remaining [IsAlgClosed k]
    (hPL : PurelyInseparableSmoothing k) (hFLAT : FlatteningAfterGEAlteration k)
    (hTSM : TemkinStableModification k) (hEND : SemistableResolution k) :
    DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_producers (temkinReadyFibration_of_purelyInseparableSmoothing hPL)
    hFLAT hTSM hEND baseStep

/-- De Jong 4.1 over an algebraically closed field of characteristic zero from the three
remaining producers. -/
theorem deJongAlterationTheorem_of_remaining_charZero [IsAlgClosed k] [CharZero k]
    (hFLAT : FlatteningAfterGEAlteration k) (hTSM : TemkinStableModification k)
    (hEND : SemistableResolution k) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_producers temkinReadyFibration_of_charZero hFLAT hTSM hEND baseStep

/-- De Jong 4.1 over an algebraically closed field from the three remaining producers; the purely
inseparable smoothing is `Perfection.purelyInseparableSmoothing`. -/
theorem deJongAlterationTheorem_of_flattening_stableModification_resolution [IsAlgClosed k]
    (hFLAT : FlatteningAfterGEAlteration k) (hTSM : TemkinStableModification k)
    (hEND : SemistableResolution k) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_producers (Perfection.temkinReadyFibration k) hFLAT hTSM hEND baseStep

/-- De Jong 4.1 over an algebraically closed field from Temkin's stable modification and the
semistable resolution; the smoothing and the flattening are proved. -/
theorem deJongAlterationTheorem_of_stableModification_resolution [IsAlgClosed k]
    (hTSM : TemkinStableModification k) (hEND : SemistableResolution k) :
    DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_flattening_stableModification_resolution
    (Flattening.flatteningAfterGEAlteration k) hTSM hEND

/-- De Jong 4.1 over an algebraically closed field from Temkin's stable modification alone; the
smoothing, the flattening and the semistable resolution are proved. -/
theorem deJongAlterationTheorem_of_stableModification [IsAlgClosed k]
    (hTSM : TemkinStableModification k) : DeJongAlterationTheorem k :=
  deJongAlterationTheorem_of_stableModification_resolution hTSM
    (Resolution.Global.semistableResolution k)

end DeJongAlterations.StableModification.DeJong
