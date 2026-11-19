import Hironaka.Resolution.HironakaActualGeneratedCurrentValues
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

/-! A genuinely compact admissible centre inside an actual open extends by
its literal image. Compactness makes the image globally closed; smoothness,
cosupport and entire-boundary normal crossings descend from the actual open.
No global smoothification or desired extension certificate is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCompactCentreImage
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen AnalyticSubsetOpens
open HironakaSharpOriginalAllBoundaryCentre RelativePrincipalizationSpan NormalCrossings
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}

/-- Literal image extension of a compact locally admissible centre. The
normal crossings assertion retains the entire original boundary list. -/
theorem compact_admissible_centre_image
 (M : MarkedIdeal n X) (hM : ∀x g,M.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens X) (C : Set U) (hK : IsCompact C)
 (hC : (MarkedIdeal.pullback (Subtype.val : U → X) M).IsAdmissibleCentre C) :
 IsCompact ((Subtype.val : U → X) '' C) ∧
 M.IsAdmissibleCentre ((Subtype.val : U → X) '' C) ∧
 (Subtype.val : U → X) ⁻¹' ((Subtype.val : U → X) '' C)=C := by
 have hTr : (Subtype.val : U → X) ⁻¹' ((Subtype.val : U → X) '' C)=C :=
   Subtype.val_injective.preimage_image C
 have hComp := hK.image continuous_subtype_val
 refine ⟨hComp,⟨⟨hComp.isClosed,?_⟩,?_,?_⟩,hTr⟩
 · rintro x ⟨c,hc,rfl⟩
   obtain ⟨k,hk⟩ := hC.1.2 c hc
   exact ⟨k,regularAtDim_image_val_iff.mpr hk⟩
 · rintro x ⟨c,hc,rfl⟩
   have hx := hC.2.1 hc
   rw [cosupp_pullback_val M hM U] at hx
   exact hx
 · rintro x ⟨c,hc,rfl⟩
   have hlocal : HasNormalCrossings n C (M.E.map ((Subtype.val : U → X) ⁻¹' ·)) := hC.2.2
   apply normalCrossingsAt_preimage_val_iff.mp
   rw [hTr]
   exact hlocal c hc

/-- Empty interior also descends under the literal open inclusion. -/
theorem interior_image_val_eq_empty (U : Opens X) (C : Set U)
 (hC : interior C=∅) : interior ((Subtype.val : U → X) '' C)=∅ := by
 have hp : (Subtype.val : U → X) ⁻¹' interior ((Subtype.val : U → X) '' C)=∅ := by
   have hf : IsOpenMap (Subtype.val : U → X) := U.isOpen.isOpenMap_subtype_val
   have he := hf.preimage_interior_eq_interior_preimage continuous_subtype_val
     ((Subtype.val : U → X) '' C)
   exact he.trans ((congrArg interior (Subtype.val_injective.preimage_image C)).trans hC)
 apply eq_empty_iff_forall_notMem.mpr
 intro x hx
 obtain ⟨c,_hc,rfl⟩ := interior_subset hx
 exact Set.eq_empty_iff_forall_notMem.mp hp c hx

end
end Hironaka.HironakaActualCompactCentreImage
