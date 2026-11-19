import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentPhaseRestriction
import Hironaka.Analytic.Unibranch.OriginalNativeCurrentSmoothRestriction

/-! Actual simultaneous phase windows and the same restricted past smooth context. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualPhaseContext
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeHSCurrentSmoothContext
  OriginalNativeCurrentSmoothRestriction

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T) (hKS : IsCompact KS) (hKT : IsCompact KT)
  (hnS : (singularShadow S).Nonempty) (hnT : (singularShadow T).Nonempty)

private theorem targetExtra : KT ⊆ (⊤ : Opens Y.obj.left) := by simp

/-- Actual target phase window, selected before the source window. -/
def targetOpen : Opens Y.obj.left :=
  OriginalNativeHSCurrentPhaseRestriction.openSet T c.targetOpen c.targetCompactClosure c.targetRange
    c.targetContains hKT hnT ⊤ targetExtra

private theorem target_contains : KT ⊆ targetOpen c hKT hnT :=
  OriginalNativeHSCurrentPhaseRestriction.contains T c.targetOpen c.targetCompactClosure c.targetRange
    c.targetContains hKT hnT ⊤ targetExtra

/-- The source's ordinary extra open is the inverse image of the actual target window. -/
def sourceExtra : Opens X.obj.left :=
  ⟨f.hom.left.base ⁻¹' (targetOpen c hKT hnT : Set Y.obj.left),
    (targetOpen c hKT hnT).isOpen.preimage f.hom.left.base.hom.continuous⟩

private theorem sourceExtra_contains : KS ⊆ sourceExtra c hKT hnT := by
  intro x hx
  exact target_contains c hKT hnT (c.compactImage ⟨x,hx,rfl⟩)

/-- Actual source phase window, contained in the inverse target window. -/
def sourceOpen : Opens X.obj.left :=
  OriginalNativeHSCurrentPhaseRestriction.openSet S c.sourceOpen c.sourceCompactClosure c.sourceRange
    c.sourceContains hKS hnS (sourceExtra c hKT hnT) (sourceExtra_contains c hKT hnT)

/-- The original current smooth arrow restricted to the two actual phase windows. -/
def pastContext : Context f e0 r O a ha hChart S T := by
  let hS := OriginalNativeHSCurrentPhaseRestriction.compactClosure S c.sourceOpen c.sourceCompactClosure c.sourceRange
    c.sourceContains hKS hnS (sourceExtra c hKT hnT) (sourceExtra_contains c hKT hnT)
  let hT := OriginalNativeHSCurrentPhaseRestriction.compactClosure T c.targetOpen c.targetCompactClosure c.targetRange
    c.targetContains hKT hnT ⊤ targetExtra
  have hContainS : KS ⊆ sourceOpen c hKS hKT hnS hnT :=
    OriginalNativeHSCurrentPhaseRestriction.contains S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS hnS (sourceExtra c hKT hnT) (sourceExtra_contains c hKT hnT)
  have hContainT : KT ⊆ targetOpen c hKT hnT := target_contains c hKT hnT
  have hCloseS : closure (sourceOpen c hKS hKT hnS hnT : Set X.obj.left) ⊆ c.sourceOpen :=
    OriginalNativeHSCurrentPhaseRestriction.closure_subset_old S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS hnS (sourceExtra c hKT hnT) (sourceExtra_contains c hKT hnT)
  have hCloseT : closure (targetOpen c hKT hnT : Set Y.obj.left) ⊆ c.targetOpen :=
    OriginalNativeHSCurrentPhaseRestriction.closure_subset_old T c.targetOpen c.targetCompactClosure c.targetRange
      c.targetContains hKT hnT ⊤ targetExtra
  have hImage : f.hom.left.base '' closure (sourceOpen c hKS hKT hnS hnT : Set X.obj.left) ⊆
      (targetOpen c hKT hnT : Set Y.obj.left) := by
    rintro _ ⟨x,hx,rfl⟩
    exact OriginalNativeHSCurrentPhaseRestriction.closure_subset_extra S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS hnS (sourceExtra c hKT hnT) (sourceExtra_contains c hKT hnT) hx
  exact restrictContext c (sourceOpen c hKS hKT hnS hnT) (targetOpen c hKT hnT)
    hS hT hContainS hContainT hCloseS hCloseT hImage
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualPhaseContext
