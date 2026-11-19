import Hironaka.Analytic.Unibranch.HironakaG10EpNativeDim
import Hironaka.Analytic.Unibranch.HironakaG10RdPermRun

/-!
# D3: the native dimension bound passes to strict transforms (G10-03-14.c)

Run 0081 lane G10EP.  Blueprint: `hironaka-g10ep-native-dimension.tex`.

For a stage `s` and an admissible centre `c`, the strict transform `strictSet s c B` of a closed (in
particular analytic) set `B` keeps every native dimension bound of `B` (`nativeDimLE_strictSet`), in the
shape consumed by the relative `II_n ⇐ I_n` theorem of lane G10RD.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10EpNativeDimStrict

open SourceReducedComplexSpace HironakaG10EpNativeDim HironakaG10RdPermRun
  HironakaG10ChowFlatteningDriver HironakaG10ChowCentreMachine HironakaG10ChowOneStepStrictTransform
  EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- The blowup map of one step is an isomorphism off the nonunit locus of the centre. -/
theorem stepσ_isIsoOver (s : Stage) (c : AdmissibleCentre s.f) :
    IsIsoOver (stepσ s c) (nonunitLocus c.B c.b)ᶜ := by
  let := c.finiteType
  exact stepProj_isIsoOver c.B c.b c.dense

/-- **D3 for closed sets.**  The strict transform of a closed set keeps its native dimension bound. -/
theorem nativeDimLE_strictSet_of_isClosed (s : Stage) (c : AdmissibleCentre s.f)
    {B : Set s.X.obj.left} (hB : IsClosed B) {n : ℕ} (h : NativeDimLE s.X B n) :
    NativeDimLE (nextWith s c).X (strictSet s c B) n :=
  nativeDimLE_closure_preimage (stepσ s c) (stepσ_isIsoOver s c) hB h

/-- **D3** (the shape consumed by the double induction): the strict transform of an analytic set keeps
its native dimension bound. -/
theorem nativeDimLE_strictSet (s : Stage) (c : AdmissibleCentre s.f) {B : Set s.X.obj.left}
    (hB : s.X.IsAnalyticSubset B) {n : ℕ} (h : NativeDimLE s.X B n) :
    NativeDimLE (nextWith s c).X (strictSet s c B) n :=
  nativeDimLE_strictSet_of_isClosed s c hB.isClosed h

end

end Hironaka.Analytic.Unibranch.HironakaG10EpNativeDimStrict
