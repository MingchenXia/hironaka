import Hironaka.Analytic.Unibranch.HironakaG1NativeFiniteCleanupRestriction

/-! # Real finite original-window readout of the SAME strong composite

The earlier initial restriction's REAL IsModification witness is explicit.
Properness derives the cleanup source window; the actual cleanup finite
theorem and full literal restriction identity preserve the SAME map.
No initial canonical factory or all-future finite-family packet is assumed.
Blueprint first.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeStrongFiniteReadout

open Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification

noncomputable section

variable {X Y Z : SourceReducedComplexSpace}

/-- FULL literal restriction of a genuine native composite, with its actual raw source. -/
theorem restrictionProjection_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    (hp : IsProperMap p.hom.left.base) (hq : IsProperMap q.hom.left.base)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    OriginalRelativelyCompactRestriction.restrictionProjection
        (OriginalRelativelyCompactRestriction.preimageOpen U p) q
        (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U p hU hp) hq ≫
      OriginalRelativelyCompactRestriction.restrictionProjection U p hU hp =
    OriginalRelativelyCompactRestriction.restrictionProjection U (q ≫ p) hU (hp.comp hq) := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  have hl := OriginalRelativelyCompactRestriction.restrictionProjection_base U p hU hp
    ((OriginalRelativelyCompactRestriction.restrictionProjection
      (OriginalRelativelyCompactRestriction.preimageOpen U p) q
      (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U p hU hp) hq).hom.left.base z)
  have hm := OriginalRelativelyCompactRestriction.restrictionProjection_base
    (OriginalRelativelyCompactRestriction.preimageOpen U p) q
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U p hU hp) hq z
  have hr := OriginalRelativelyCompactRestriction.restrictionProjection_base U (q ≫ p) hU (hp.comp hq) z
  exact hl.trans ((congrArg p.hom.left.base hm).trans hr.symm)

/-- A REAL earlier initial finite window yields a REAL finite window of the SAME strong map. -/
theorem strongMorphism_restriction_isModification (p : Y ⟶ X) (hp : IsResolution p)
    (hReg : IsIsoOver p (intrinsicRegularLocus X.obj)) (U : Opens X.obj.left)
    (hU : IsCompact (closure (U : Set X.obj.left)))
    (hInitial : IsModification (OriginalRelativelyCompactRestriction.restrictionProjection U p hU hp.2.1)) :
    IsModification (OriginalRelativelyCompactRestriction.restrictionProjection U
      (HironakaG1NativeStrongCleanup.strongMorphism p hp) hU
      (HironakaG1NativeStrongCleanup.strong_geometry p hp hReg).2.2.2.1) := by
  let V := OriginalRelativelyCompactRestriction.preimageOpen U p
  have hV : IsCompact (closure (V : Set Y.obj.left)) :=
    OriginalRelativelyCompactRestriction.isCompact_closure_preimage U p hU hp.2.1
  have hcleanup := HironakaG1NativeFiniteCleanupRestriction.strongRefinement_restriction_isModification
    p hp hReg V hV
  have hfinite := hcleanup.comp hInitial
  have hs := restrictionProjection_comp p (HironakaG1NativeStrongCleanup.strongRefinement p hp) hp.2.1
    (HironakaG1NativeStrongCleanup.strong_geometry p hp hReg).2.1 U hU
  rw [hs] at hfinite
  exact hfinite

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeStrongFiniteReadout
