import Hironaka.Analytic.Unibranch.HironakaG10EpNativeDimStrict
import Hironaka.Analytic.Unibranch.HironakaG10EpZeroLocus
import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticPreimage

/-!
# Strict transforms of analytic sets are analytic (G10-03-09.a)

Run 0081 lane G10EP.  Blueprint: `hironaka-g10ep-zero-locus.tex`.

For a stage `s` and an admissible centre `c`, the strict transform `strictSet s c B = closure (σ⁻¹ (B \ D))`
of an analytic set `B` is analytic (`isAnalyticSubset_strictSet`): `D` is the nonunit locus of the
finite-type centre ideal, analytic by `HironakaG10EpZeroLocus.isAnalyticSubset_nonunitLocus`, inverse
images of analytic sets are analytic, and so is the closure of a difference of analytic sets.  With
`HironakaG10EpNativeDimStrict.nativeDimLE_strictSet` this gives the stability of the predicate
`IsAnalyticSubset ∧ NativeDimLE` under strict transforms (`analytic_nativeDimLE_strictSet`).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10EpStrictAnalytic

open SourceReducedComplexSpace HironakaG10EpNativeDim HironakaG10EpNativeDimStrict HironakaG10RdPermRun
  HironakaG10ChowFlatteningDriver HironakaG10ChowCentreMachine EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- The nonunit locus of an admissible centre is analytic. -/
theorem isAnalyticSubset_centre_nonunitLocus {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}
    (c : AdmissibleCentre f) : X.IsAnalyticSubset (nonunitLocus c.B c.b) := by
  let := c.finiteType
  exact HironakaG10EpZeroLocus.isAnalyticSubset_nonunitLocus c.B c.b

/-- **G10-03-09.a.**  The strict transform of an analytic set is analytic. -/
theorem isAnalyticSubset_strictSet (s : Stage) (c : AdmissibleCentre s.f) {B : Set s.X.obj.left}
    (hB : s.X.IsAnalyticSubset B) : (nextWith s c).X.IsAnalyticSubset (strictSet s c B) := by
  have h := HironakaG10NativeAnalyticClosureDifference.isAnalyticSubset_closure_diff
    (SourceReducedComplexSpace.IsAnalyticSubset.preimage hB (stepσ s c))
    (SourceReducedComplexSpace.IsAnalyticSubset.preimage (isAnalyticSubset_centre_nonunitLocus c)
      (stepσ s c))
  unfold strictSet
  rw [preimage_sdiff]
  exact h

/-- **The predicate of the double induction is stable under strict transforms**:
`IsAnalyticSubset B ∧ NativeDimLE B n` passes from `B` to `strictSet s c B`. -/
theorem analytic_nativeDimLE_strictSet (s : Stage) (c : AdmissibleCentre s.f)
    {B : Set s.X.obj.left} {n : ℕ} (h : s.X.IsAnalyticSubset B ∧ NativeDimLE s.X B n) :
    (nextWith s c).X.IsAnalyticSubset (strictSet s c B) ∧
      NativeDimLE (nextWith s c).X (strictSet s c B) n :=
  ⟨isAnalyticSubset_strictSet s c h.1, nativeDimLE_strictSet s c h.1 h.2⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10EpStrictAnalytic
