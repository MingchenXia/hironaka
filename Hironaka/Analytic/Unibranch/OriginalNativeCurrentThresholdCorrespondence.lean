import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseSpans

/-! Threshold correspondence from an actual past smooth context and source
native phase-window coverage, without a global target-profile bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeCurrentThresholdCorrespondence
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothSingularLocus
  OriginalNativeHSCurrentSmoothContext HironakaG1NativeFiniteProductState
  HironakaG11VanishingWindows HironakaG11PresWindows HironakaG11PresReduction HironakaG11PresLineState
  HironakaG11PresTowerState BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left}
  {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T)

/-- Actual source native phase records and threshold coverage give exact
threshold correspondence for the same current smooth context. -/
theorem threshold_preimage_of_source_phase_records
    (H : ℕ → ℕ) {Ns : ℕ} {κ : Type}
    (wS : κ → DimEmbedding (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen
      c.sourceCompactClosure c.sourceRange) Ns)
    (rawS : ∀ i, MarkedIdeal Ns (CMfd.of (n := Ns) (wS i).ambient))
    (hrecS : ∀ i, IsNativeWindowRecord (wS i) (rawS i) (finiteProductHS r H))
    (hcover : originalSingularHSThreshold
      (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange)
      (finiteProductHS r H) ⊆ ⋃ i, range (wS i).toLocalEmbedding.toPoint) :
    c.map.hom.left.base ⁻¹' originalSingularHSThreshold
      (OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen c.targetCompactClosure c.targetRange) H =
    originalSingularHSThreshold
      (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange)
      (finiteProductHS r H) := by
  ext z
  have hSing := smoothAt_singular_iff c.map z (c.smooth z)
  constructor
  · rintro ⟨htSing,htLow⟩
    refine ⟨hSing.mpr htSing,?_⟩
    change ∀ l, H l ≤ originalStalkHS
      (OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen c.targetCompactClosure c.targetRange)
        (c.map.hom.left.base z) l at htLow
    change ∀ l, finiteProductHS r H l ≤ originalStalkHS
      (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange) z l
    rw [c.point_profile z]
    exact finiteProductHS_mono r htLow
  · intro hz
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover hz)
    obtain ⟨w,hw⟩ := hi
    have hs := (hrecS i).2.2.hsTowerState (BlowupTower.refl (X := CMfd.of (n := Ns) (wS i).ambient)) trivial
    have heq : originalStalkHS
        (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange) z =
          finiteProductHS r H := by
      funext l
      apply le_antisymm
      · rw [←hw, originalStalkHS_localEmbedding_eq]
        exact hs.2.2.1 w.val l
      · exact hz.2 l
    have htEq := (finiteProductHS_injective r) ((c.point_profile z).symm.trans heq)
    exact ⟨hSing.mp hz.1, fun l => (congrFun htEq l).ge⟩
end
end Hironaka.Analytic.Unibranch.OriginalNativeCurrentThresholdCorrespondence
