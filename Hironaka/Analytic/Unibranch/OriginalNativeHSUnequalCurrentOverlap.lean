import Hironaka.Analytic.Unibranch.OriginalNativeHSSkippedCurrentOverlap

/-! The actual unequal-head Run update, using the derived whole absence
and the genuine common-original-base skip. Blueprint FIRST:
original-native-hs-unequal-current-overlap.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSUnequalCurrentOverlap
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeHSCurrentOverlap

variable {X : SourceReducedComplexSpace} {K₁ K₂ L : Set X.obj.left}
  (S : State X K₁) (T : State X K₂) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
  (hn₁ : (singularShadow S).Nonempty) (hn₂ : (singularShadow T).Nonempty)
  (c : Context S T L) (hL : IsCompact L) (hL₁ : L ⊆ K₁) (hL₂ : L ⊆ K₂)
  (higher : toLex (OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T)
    (baseShadow_compact T hK₂) hn₂) < toLex (OriginalNativeHSOuterInitialBound.profile S.history
      (baseShadow S) (baseShadow_compact S hK₁) hn₁))

include hL hL₁ hL₂ higher in
/-- Consume the actual HIGHER left constructor; keep the right current Run unchanged. -/
theorem exists_context : ∃ d : Context (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁) T L,
    d.openSet ≤ c.openSet := by
  have he := OriginalNativeHSUnequalSuccessor.higher_threshold_empty (S := S) (T := T)
    (hK₁ := hK₁) (hK₂ := hK₂) (hn₁ := hn₁) (hn₂ := hn₂)
    (U := c.openSet) (hU := c.compactClosure) (hRS := c.leftRange) (hRT := c.rightRange)
    (α := c.comparison) (hPast := c.square) (L := L) (hLU := c.contains) (hLK₂ := hL₂)
    (higher := higher)
  obtain ⟨d,hd⟩ := OriginalNativeHSSkippedCurrentOverlap.exists_context S hK₁ hn₁ hL hL₁
    c.openSet c.contains he
  let β := OriginalNativePrescribedHistoryRefinement.restrictedIso S.inclusion S.inclusion_isOpenImmersion
    c.openSet c.compactClosure c.leftRange S.history d.openSet d.compactClosure hd
    T.inclusion T.inclusion_isOpenImmersion c.rightRange T.history c.comparison c.square
  have hβ := OriginalNativePrescribedHistoryRefinement.restrictedIso_projection S.inclusion
    S.inclusion_isOpenImmersion c.openSet c.compactClosure c.leftRange S.history d.openSet d.compactClosure hd
    T.inclusion T.inclusion_isOpenImmersion c.rightRange T.history c.comparison c.square
  let hRT := OriginalNativePrescribedHistoryRefinement.smallerRange T.inclusion c.openSet c.rightRange d.openSet hd
  have hs : (d.comparison.trans β).hom ≫ (history T d.openSet d.compactClosure hRT).projection =
      (history (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁) d.openSet d.compactClosure d.leftRange).projection :=
    (Category.assoc _ _ _).trans ((congrArg (fun p => d.comparison.hom ≫ p) hβ).trans d.square)
  exact ⟨⟨d.openSet,d.compactClosure,d.contains,d.leftRange,hRT,d.comparison.trans β,hs⟩,hd⟩

private def reverse {A B : Set X.obj.left} {S : State X A} {T : State X B}
    (c : Context S T L) : Context T S L where
  openSet := c.openSet
  compactClosure := c.compactClosure
  contains := c.contains
  leftRange := c.rightRange
  rightRange := c.leftRange
  comparison := c.comparison.symm
  square := by
    change c.comparison.inv ≫ (history S c.openSet c.compactClosure c.leftRange).projection =
      (history T c.openSet c.compactClosure c.rightRange).projection
    rw [← c.square,← Category.assoc,c.comparison.inv_hom_id,Category.id_comp]

include hL hL₁ hL₂ in
/-- Consume the actual HIGHER right constructor, by the genuine inverse PAST square. -/
theorem exists_right_context
    (higherRight : toLex (OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁) < toLex (OriginalNativeHSOuterInitialBound.profile T.history
        (baseShadow T) (baseShadow_compact T hK₂) hn₂)) :
    ∃ d : Context S (OriginalNativeHSShadowOuterRun.next T hK₂ hn₂) L,
      d.openSet ≤ c.openSet := by
  obtain ⟨d,hd⟩ := exists_context T S hK₂ hK₁ hn₂ hn₁ (reverse c) hL hL₂ hL₁ higherRight
  exact ⟨reverse d,hd⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSUnequalCurrentOverlap
