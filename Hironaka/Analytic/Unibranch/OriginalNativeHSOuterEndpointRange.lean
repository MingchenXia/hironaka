import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterSuccessor

/-! Exact actual factory endpoint range of the SAME computed outer successor.
Blueprint FIRST: original-native-hs-outer-endpoint-range.tex.
No new phase, history, neighbourhood or comparison packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEndpointRange
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction
  Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus

variable {B Y : SourceReducedComplexSpace} (h : PhysicalHistory B Y) (K : Set B.obj.left)
  (hK : IsCompact K)
  (hne : (intrinsicSingularLocus Y.obj ∩ OriginalNativeHSOuterSuccessor.shadow h K).Nonempty)

include hne in
private theorem phaseNonempty :
    (OriginalNativeHSOuterSuccessor.shadow h K ∩ intrinsicSingularLocus Y.obj).Nonempty := by
  simpa only [inter_comm] using hne

private abbrev phaseBase := OriginalNativeHSShadowPhaseFactory.base Y
  (OriginalNativeHSOuterSuccessor.shadow h K) (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK)
  (phaseNonempty h K hne)
private abbrev phaseSource := OriginalNativeHSShadowPhaseFactory.source Y
  (OriginalNativeHSOuterSuccessor.shadow h K) (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK)
  (phaseNonempty h K hne)
private abbrev phaseHistory : PhysicalHistory (phaseBase h K hK hne) (phaseSource h K hK hne) :=
  OriginalNativeHSShadowPhaseFactory.history Y (OriginalNativeHSOuterSuccessor.shadow h K)
    (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK) (phaseNonempty h K hne)
private abbrev phaseInclusion := OriginalNativeHSShadowPhaseFactory.baseInclusion Y
  (OriginalNativeHSOuterSuccessor.shadow h K) (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK)
  (phaseNonempty h K hne)
private theorem phaseInclusion_open :
    LocallyRingedSpace.IsOpenImmersion (phaseInclusion h K hK hne).hom.left :=
  OriginalNativeHSShadowPhaseFactory.baseInclusion_isOpenImmersion Y
    (OriginalNativeHSOuterSuccessor.shadow h K) (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK)
    (phaseNonempty h K hne)
private theorem phaseCover : h.projection.hom.left.base ⁻¹' K ⊆
    range (phaseInclusion h K hK hne).hom.left.base :=
  OriginalNativeHSShadowPhaseFactory.compact_retained Y (OriginalNativeHSOuterSuccessor.shadow h K)
    (OriginalNativeHSOuterSuccessor.shadow_isCompact h K hK) (phaseNonempty h K hne)

/-- The LITERAL computed next source inclusion into the SAME factory source. -/
def endpointInclusion : OriginalNativeHSOuterSuccessor.source h K hK hne ⟶ phaseSource h K hK hne :=
  OriginalNativePhysicalHistoryResaturation.sourceInclusion h (phaseInclusion h K hK hne)
    (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne) (phaseHistory h K hK hne)

theorem endpointInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (endpointInclusion h K hK hne).hom.left :=
  inclusion_isOpenImmersion _ _ _

theorem oldInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (OriginalNativeHSOuterSuccessor.oldInclusion h K hK hne).hom.left :=
  inclusion_isOpenImmersion _ _ _

/-- FULL original arrow square, retaining the computed actual sourceMap. -/
theorem endpoint_square : endpointInclusion h K hK hne ≫ (phaseHistory h K hK hne).projection ≫
    phaseInclusion h K hK hne = OriginalNativeHSOuterSuccessor.sourceMap h K hK hne := rfl

/-- EVERY factory endpoint point satisfies the exact same inverse-open dictionary. -/
theorem endpoint_range : range (endpointInclusion h K hK hne).hom.left.base =
    ((phaseHistory h K hK hne).projection ≫ phaseInclusion h K hK hne).hom.left.base ⁻¹'
      range (OriginalNativeHSOuterSuccessor.oldInclusion h K hK hne).hom.left.base := by
  change range (Subtype.val : preimageOpen
      (OriginalNativePhysicalHistoryResaturation.phaseOpen h (phaseInclusion h K hK hne)
        (phaseInclusion_open h K hK hne) K hK (phaseCover h K hK hne))
      (phaseHistory h K hK hne).projection → (phaseSource h K hK hne).obj.left) =
    ((phaseHistory h K hK hne).projection ≫ phaseInclusion h K hK hne).hom.left.base ⁻¹'
      range (Subtype.val : preimageOpen (OriginalNativeHSOuterSuccessor.neighbourhood h K hK hne).openSet
        h.projection → Y.obj.left)
  rw [Subtype.range_coe, Subtype.range_coe]
  rfl

/-- The original complex structure-unit square of that SAME native inclusion. -/
theorem endpoint_scalar : (endpointInclusion h K hK hne).hom.left ≫
    (phaseSource h K hK hne).obj.hom = (OriginalNativeHSOuterSuccessor.source h K hK hne).obj.hom :=
  Over.w (endpointInclusion h K hK hne).hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEndpointRange
