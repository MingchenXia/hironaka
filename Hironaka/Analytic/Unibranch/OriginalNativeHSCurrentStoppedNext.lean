import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSSkippedCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedSuccessor
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement

/-! Actual STOP-vs-NEXT update for an honest PAST current overlap.
Blueprint FIRST: original-native-hs-current-stopped-next.tex.
No future comparison/threshold-absence packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentStoppedNext
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeHSCurrentOverlap

variable {X : SourceReducedComplexSpace} {K₁ K₂ L : Set X.obj.left}
  (S : State X K₁) (T : State X K₂) (c : Context S T L)
  (hK₂ : IsCompact K₂) (hn : (singularShadow T).Nonempty)
  (hL : IsCompact L) (hL₁ : L ⊆ K₁) (hL₂ : L ⊆ K₂) (he : singularShadow S = ∅)

def nextCompact : Set (OriginalNativeHSShadowOuterRun.next T hK₂ hn).base.obj.left :=
  (OriginalNativeHSShadowOuterRun.next T hK₂ hn).inclusion.hom.left.base ⁻¹' L

include hL hL₂ in
theorem nextCompact_isCompact : IsCompact (nextCompact T hK₂ hn (L := L)) :=
  (OriginalNativeHSShadowOuterRun.next T hK₂ hn).inclusion_isOpenImmersion.base_open.isEmbedding.isInducing.isCompact_preimage'
    hL (hL₂.trans (OriginalNativeHSShadowOuterRun.next T hK₂ hn).contains)

include c hL₁ he in
theorem absence :
    OriginalNativeHSAbsentOuterSuccessor.oldFibre T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn (nextCompact T hK₂ hn (L := L)) ∩
      OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold
        (OriginalNativeHSOuterSuccessor.oldSource T.history (baseShadow T) (baseShadow_compact T hK₂) hn)
        (OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hK₂) hn) = ∅ := by
  apply OriginalNativeHSStoppedSuccessor.old_threshold_empty
    (S := S) (T := T) (a := c.leftMap) (ha := c.leftMap_isOpenImmersion)
    (b := c.rightMap) (hb := c.rightMap_isOpenImmersion)
    (hsq := c.left_square.symm.trans c.right_square) (C := L) (hC := hL₁)
    (hCover := c.right_fibre_covered) (hStop := he)
    (hK₂ := hK₂) (hn := hn) (L := nextCompact T hK₂ hn (L := L))
  rintro _ ⟨b,hb,rfl⟩
  exact hb


private def composeRestricted (d : Context (OriginalNativeHSShadowOuterRun.next T hK₂ hn) T L)
    (hsub : d.openSet ≤ c.openSet) : Context S (OriginalNativeHSShadowOuterRun.next T hK₂ hn) L := by
  let hLeft := (closure_mono hsub).trans c.leftRange
  let β : endpoint S d.openSet d.compactClosure hLeft ≅ endpoint T d.openSet d.compactClosure d.rightRange :=
    OriginalNativePrescribedHistoryRefinement.restrictedIso
    S.inclusion S.inclusion_isOpenImmersion c.openSet c.compactClosure c.leftRange S.history
    d.openSet d.compactClosure hsub T.inclusion T.inclusion_isOpenImmersion c.rightRange T.history
    c.comparison c.square
  have hβ : β.hom ≫ (history T d.openSet d.compactClosure d.rightRange).projection =
      (history S d.openSet d.compactClosure hLeft).projection :=
    OriginalNativePrescribedHistoryRefinement.restrictedIso_projection
      S.inclusion S.inclusion_isOpenImmersion c.openSet c.compactClosure c.leftRange S.history
      d.openSet d.compactClosure hsub T.inclusion T.inclusion_isOpenImmersion c.rightRange T.history
      c.comparison c.square
  have hd : d.comparison.inv ≫
      (history (OriginalNativeHSShadowOuterRun.next T hK₂ hn) d.openSet d.compactClosure d.leftRange).projection =
      (history T d.openSet d.compactClosure d.rightRange).projection := by
    rw [← d.square,← Category.assoc,d.comparison.inv_hom_id,Category.id_comp]
  refine ⟨d.openSet,d.compactClosure,d.contains,hLeft,d.leftRange,β.trans d.comparison.symm,?_⟩
  change (β.hom ≫ d.comparison.inv) ≫ _ = _
  rw [Category.assoc,hd]
  exact hβ


/-- The ACTUAL right next is internally absent; restrict and compose the PAST iso. -/
def refinement : {d : Context S (OriginalNativeHSShadowOuterRun.next T hK₂ hn) L // d.openSet ≤ c.openSet} := by
  let result := OriginalNativeHSSkippedCurrentOverlap.exists_context T hK₂ hn hL hL₂ c.openSet c.contains
    (absence S T c hK₂ hn hL₁ he)
  let d := result.choose
  exact ⟨composeRestricted S T c hK₂ hn d result.choose_spec,result.choose_spec⟩

def context : Context S (OriginalNativeHSShadowOuterRun.next T hK₂ hn) L :=
  (refinement S T c hK₂ hn hL hL₁ hL₂ he).val

theorem context_open_subset : (context S T c hK₂ hn hL hL₁ hL₂ he).openSet ≤ c.openSet :=
  (refinement S T c hK₂ hn hL hL₁ hL₂ he).property

private def reverseContext {K₃ K₄ C : Set X.obj.left} {A : State X K₃} {B : State X K₄}
    (d : Context A B C) : Context B A C where
  openSet := d.openSet
  compactClosure := d.compactClosure
  contains := d.contains
  leftRange := d.rightRange
  rightRange := d.leftRange
  comparison := d.comparison.symm
  square := by
    change d.comparison.inv ≫ (history A d.openSet d.compactClosure d.leftRange).projection =
      (history B d.openSet d.compactClosure d.rightRange).projection
    rw [← d.square,← Category.assoc,d.comparison.inv_hom_id,Category.id_comp]

/-- Symmetric actual NEXT-vs-STOP case, by the same proved ordinary producer. -/
def nextStopped (hK₁ : IsCompact K₁) (hnS : (singularShadow S).Nonempty) (heT : singularShadow T = ∅) :
    Context (OriginalNativeHSShadowOuterRun.next S hK₁ hnS) T L :=
  reverseContext (context T S (reverseContext c) hK₁ hnS hL hL₂ hL₁ heT)

theorem nextStopped_open_subset (hK₁ : IsCompact K₁) (hnS : (singularShadow S).Nonempty)
    (heT : singularShadow T = ∅) : (nextStopped S T c hL hL₁ hL₂ hK₁ hnS heT).openSet ≤ c.openSet :=
  context_open_subset T S (reverseContext c) hK₁ hnS hL hL₂ hL₁ heT

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentStoppedNext
