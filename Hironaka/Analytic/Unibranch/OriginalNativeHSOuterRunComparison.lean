import Hironaka.Analytic.Unibranch.OriginalNativeHSUnequalCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentStoppedNext
import Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSEqualOuterSuccessor
import Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness

/-! TWO actual finite outer Runs compare by their genuine constructor cases.
Blueprint FIRST: original-native-hs-outer-run-comparison.tex.
No future-case supplier or common physical clock. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOuterRunComparison
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeHSCurrentOverlap
  OriginalNativeHSShadowOuterRun

private def nextCount {X : SourceReducedComplexSpace} {K : Set X.obj.left} {hK : IsCompact K} :
    {S : State X K} → Run hK S → ℕ
  | _, .stop _ _ => 0
  | _, .next _ _ tail => nextCount tail + 1

variable {X : SourceReducedComplexSpace} {K₁ K₂ L : Set X.obj.left}

/-- Real finite Run induction; every constructor update is internally constructed. -/
theorem exists_context (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hL : IsCompact L)
    (hL₁ : L ⊆ K₁) (hL₂ : L ⊆ K₂) {S : State X K₁} {T : State X K₂}
    (r : Run hK₁ S) (s : Run hK₂ T) (c : Context S T L) :
    ∃ d : Context r.finalState s.finalState L, d.openSet ≤ c.openSet := by
  classical
  cases hr : r with
  | stop S heS =>
    cases hs : s with
    | stop T heT =>
      exact OriginalNativeHSStoppedCurrentOverlap.exists_context S T hK₁ hK₂ heS heT c hL hL₁ hL₂
    | next T hnT tailT =>
      let c₁ := OriginalNativeHSCurrentStoppedNext.context S T c hK₂ hnT hL hL₁ hL₂ heS
      obtain ⟨d,hd⟩ := exists_context hK₁ hK₂ hL hL₁ hL₂ (Run.stop S heS) tailT c₁
      exact ⟨d,hd.trans (OriginalNativeHSCurrentStoppedNext.context_open_subset S T c hK₂ hnT hL hL₁ hL₂ heS)⟩
  | next S hnS tailS =>
    cases hs : s with
    | stop T heT =>
      let c₁ := OriginalNativeHSCurrentStoppedNext.nextStopped S T c hL hL₁ hL₂ hK₁ hnS heT
      obtain ⟨d,hd⟩ := exists_context hK₁ hK₂ hL hL₁ hL₂ tailS (Run.stop T heT) c₁
      exact ⟨d,hd.trans (OriginalNativeHSCurrentStoppedNext.nextStopped_open_subset S T c hL hL₁ hL₂ hK₁ hnS heT)⟩
    | next T hnT tailT =>
      let HS := OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S) (baseShadow_compact S hK₁) hnS
      let HT := OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hK₂) hnT
      rcases lt_trichotomy (toLex HS) (toLex HT) with hST | hEq | hTS
      · obtain ⟨c₁,hc₁⟩ := OriginalNativeHSUnequalCurrentOverlap.exists_right_context
          S T hK₁ hK₂ hnS hnT c hL hL₁ hL₂ hST
        obtain ⟨d,hd⟩ := exists_context hK₁ hK₂ hL hL₁ hL₂ (Run.next S hnS tailS) tailT c₁
        exact ⟨d,hd.trans hc₁⟩
      · have hProfile : HS = HT := congrArg ofLex hEq
        obtain ⟨c₁,hc₁⟩ := OriginalNativeHSEqualOuterSuccessor.exists_context
          c hK₁ hK₂ hL hL₁ hL₂ hnS hnT hProfile
        obtain ⟨d,hd⟩ := exists_context hK₁ hK₂ hL hL₁ hL₂ tailS tailT c₁
        exact ⟨d,hd.trans hc₁⟩
      · obtain ⟨c₁,hc₁⟩ := OriginalNativeHSUnequalCurrentOverlap.exists_context
          S T hK₁ hK₂ hnS hnT c hL hL₁ hL₂ hTS
        obtain ⟨d,hd⟩ := exists_context hK₁ hK₂ hL hL₁ hL₂ tailS (Run.next T hnT tailT) c₁
        exact ⟨d,hd.trans hc₁⟩
termination_by nextCount r + nextCount s
decreasing_by all_goals (simp_all only [nextCount]; omega)

/-- ANY full native final maps over the SAME literal original base coincide. -/
theorem maps_eq_over_base (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {S : State X K₁} {T : State X K₂} (r : Run hK₁ S) (s : Run hK₂ T)
    (W : Opens X.obj.left) (hW : IsCompact (closure (W : Set X.obj.left)))
    (hRS : closure (W : Set X.obj.left) ⊆ range r.finalState.inclusion.hom.left.base)
    (hRT : closure (W : Set X.obj.left) ⊆ range s.finalState.inclusion.hom.left.base)
    (a b : endpoint r.finalState W hW hRS ⟶ endpoint s.finalState W hW hRT)
    (ha : a ≫ (history s.finalState W hW hRT).projection = (history r.finalState W hW hRS).projection)
    (hb : b ≫ (history s.finalState W hW hRT).projection = (history r.finalState W hW hRS).projection) : a = b := by
  have hbase : ∀ z, (history s.finalState W hW hRT).projection.hom.left.base (a.hom.left.base z) =
      (history s.finalState W hW hRT).projection.hom.left.base (b.hom.left.base z) := fun z =>
    (congrArg (fun p => p.hom.left.base z) ha).trans (congrArg (fun p => p.hom.left.base z) hb).symm
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq a b
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    (history s.finalState W hW hRT).singularModification.isIsoOver_intrinsicRegularLocus
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hbase
    (history r.finalState W hW hRS).singularModification.dense_preimage_intrinsicRegularLocus
    (fun u hu => (congrArg (fun p => p.hom.left.base u) ha).symm ▸ hu)) z

/-- Triple coherence for actual full maps on an HONEST common original restriction. -/
theorem cocycle {K₃ : Set X.obj.left} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hK₃ : IsCompact K₃)
    {S : State X K₁} {T : State X K₂} {P : State X K₃}
    (r : Run hK₁ S) (s : Run hK₂ T) (t : Run hK₃ P)
    (W : Opens X.obj.left) (hW : IsCompact (closure (W : Set X.obj.left)))
    (hRS : closure (W : Set X.obj.left) ⊆ range r.finalState.inclusion.hom.left.base)
    (hRT : closure (W : Set X.obj.left) ⊆ range s.finalState.inclusion.hom.left.base)
    (hRP : closure (W : Set X.obj.left) ⊆ range t.finalState.inclusion.hom.left.base)
    (a : endpoint r.finalState W hW hRS ⟶ endpoint s.finalState W hW hRT)
    (b : endpoint s.finalState W hW hRT ⟶ endpoint t.finalState W hW hRP)
    (c : endpoint r.finalState W hW hRS ⟶ endpoint t.finalState W hW hRP)
    (ha : a ≫ (history s.finalState W hW hRT).projection = (history r.finalState W hW hRS).projection)
    (hb : b ≫ (history t.finalState W hW hRP).projection = (history s.finalState W hW hRT).projection)
    (hc : c ≫ (history t.finalState W hW hRP).projection = (history r.finalState W hW hRS).projection) :
    a ≫ b = c :=
  maps_eq_over_base hK₁ hK₃ r t W hW hRS hRP (a ≫ b) c
    ((Category.assoc _ _ _).trans ((congrArg (fun p => a ≫ p) hb).trans ha)) hc

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOuterRunComparison
