import Hironaka.Analytic.Unibranch.HironakaG11PresReduction
import Hironaka.Resolution.HironakaG11PresLineStable

/-!
# G11 along the native Hilbert–Samuel window records, with native line stability proved (goal G11)

The G11 reduction `HironakaG11PresReduction.compactSingularCentreResolution_of_nativeLineStability` had two named inputs.
The first, `HironakaG11PresLineState.NativeLineStability` (step (3a-lines), BM97 Thm 9.4 test (ii)), is now a theorem
(`Hironaka.HironakaG11PresLineStable.nativeLineStability`). So `g11:general` follows from the single
named input `ClassFunctorialInvariants` (class-functorial resolution invariants, BM08 Thm 7.1, lane G11B's target (B')):

* **`compactSingularCentreResolution_of_classFunctorialInvariants`**: `ClassFunctorialInvariants →
  CompactSingularCentreResolution` (the full endpoint then follows by
  `HironakaG11SingularCentreModification.HasSingularCentreResolution.exists_endpoint`).

Blueprint: `hironaka-g11-pres-reduction.tex`.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG11PresLineReduction

open HironakaG11PresReduction HironakaG11SingularCentreModification

/-- **G11 from class-functorial resolution invariants alone** (native line stability is proved). -/
theorem compactSingularCentreResolution_of_classFunctorialInvariants (hB : ClassFunctorialInvariants) :
    CompactSingularCentreResolution :=
  compactSingularCentreResolution_of_nativeLineStability
    Hironaka.HironakaG11PresLineStable.nativeLineStability hB

end Hironaka.Analytic.Unibranch.HironakaG11PresLineReduction
