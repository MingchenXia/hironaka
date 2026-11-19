import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothStoppedComparison
import Hironaka.Analytic.Unibranch.OriginalNativeHSInitialSmoothContext
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothLeadingProfiles
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothTargetSkip
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualNext

/-! Actual TARGET-Run structural induction, using concrete ordinary native
STOP/targetskip/equal-next producers. Blueprint FIRST:
original-native-hs-smooth-outer-run-comparison.tex. No future case supplier. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSSmoothOuterRunComparison
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalNativeHSShadowOuterState
  OriginalNativeHSShadowOuterRun OriginalNativeProductWindow OriginalNativeHSCurrentSmoothContext
  HironakaG1NativeFiniteProductState

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left}

/-- Every recursive call consumes the ACTUAL target tail; source clocks stay independent. -/
theorem exists_context (hKS : IsCompact KS) (hKT : IsCompact KT)
    {S : State X KS} {T : State Y KT} (ρ : Run hKS S) (τ : Run hKT T)
    (c : Context f e0 r O a ha hChart S T) :
    ∃ d : Context f e0 r O a ha hChart ρ.finalState τ.finalState,
      d.sourceOpen ≤ c.sourceOpen ∧ d.targetOpen ≤ c.targetOpen := by
  classical
  revert S ρ c
  induction τ with
  | stop T heT =>
    intro S ρ c
    cases ρ with
    | stop S heS =>
      exact OriginalNativeHSCurrentSmoothStoppedComparison.exists_context c hKS hKT heS heT
    | next S hnS tailS =>
      exact False.elim ((OriginalNativeHSCurrentSmoothStopLoci.target_not_stopped_of_source_next c hnS) heT)
  | next T hnT tailT ih =>
    intro S ρ c
    cases ρ with
    | stop S heS =>
      have hAvoid := OriginalNativeHSCurrentSmoothStopLoci.source_stop_avoids_threshold c heS
        (OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hKT) hnT)
      obtain ⟨c₁,hS₁,hT₁⟩ := OriginalNativeHSCurrentSmoothTargetSkip.exists_context c hKS hKT hnT hAvoid
      obtain ⟨d,hS,hT⟩ := ih (Run.stop S heS) c₁
      exact ⟨d,hS.trans hS₁,hT.trans hT₁⟩
    | next S hnS tailS =>
      have hBound := OriginalNativeHSCurrentSmoothLeadingProfiles.leading_profile_le c hKS hKT hnS hnT
      rcases lt_or_eq_of_le hBound with hlt | heq
      · obtain ⟨c₁,hS₁,hT₁⟩ := OriginalNativeHSCurrentSmoothTargetSkip.exists_context_of_higher_target c hKS hKT hnS hnT hlt
        obtain ⟨d,hS,hT⟩ := ih (Run.next S hnS tailS) c₁
        exact ⟨d,hS.trans hS₁,hT.trans hT₁⟩
      · have hProfile : OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S)
            (baseShadow_compact S hKS) hnS = finiteProductHS r
              (OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hKT) hnT) :=
          congrArg ofLex heq
        obtain ⟨c₁,hS₁,hT₁⟩ := OriginalNativeHSCurrentEqualNext.exists_context c hKS hKT hnS hnT hProfile
        obtain ⟨d,hS,hT⟩ := ih tailS c₁
        exact ⟨d,hS.trans hS₁,hT.trans hT₁⟩

/-- Ordinary data only: initial context and TWO actual saved Runs are constructed internally. -/
theorem exists_near_compact_context (f : X ⟶ Y) (e0 : LocalEmbedding Y) (r : ℕ)
    (O : Opens (productAmbient e0 r)) (a : windowSpace e0 r O ⟶ X)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left) (hChart : a ≫ f = windowFirst e0 r O)
    (KS : Set X.obj.left) (KT : Set Y.obj.left) (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hRange : KS ⊆ range a.hom.left.base) (hImage : f.hom.left.base '' KS ⊆ KT) :
    Nonempty (Context f e0 r O a ha hChart (nearCompactState X KS hKS) (nearCompactState Y KT hKT)) := by
  let c := OriginalNativeHSInitialSmoothContext.context f e0 r O a ha hChart KS KT hKS hKT hRange hImage
  obtain ⟨d,_,_⟩ := exists_context hKS hKT (run (initial X KS) hKS) (run (initial Y KT) hKT) c
  exact ⟨d⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSSmoothOuterRunComparison
