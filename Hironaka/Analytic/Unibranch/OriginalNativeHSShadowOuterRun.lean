import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterState
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterSuccessor

/-! ACTUAL compact-shadow native outer run, using ONLY the genuine
frozen original-family resaturated successor and its derived rank_drop.
Blueprint FIRST: original-native-hs-shadow-outer-run.tex.
No phaseSupplier, terminal supplier, Lex-WF or global finite schedule. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalNativeHSOuterHistory
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalNativeHSShadowOuterState

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}

/-- Actual computed phase/resaturation, with no successor or rank packet input. -/
def next (S : State X K) (hK : IsCompact K) (hne : (singularShadow S).Nonempty) : State X K where
  base := OriginalNativeHSOuterSuccessor.base S.history (baseShadow S) (baseShadow_compact S hK) hne
  source := OriginalNativeHSOuterSuccessor.source S.history (baseShadow S) (baseShadow_compact S hK) hne
  history := OriginalNativeHSOuterSuccessor.history S.history (baseShadow S) (baseShadow_compact S hK) hne
  inclusion := (OriginalNativeHSOuterSuccessor.neighbourhood S.history (baseShadow S)
    (baseShadow_compact S hK) hne).inclusion ≫ S.inclusion
  inclusion_isOpenImmersion := @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (OriginalNativeHSOuterSuccessor.neighbourhood S.history (baseShadow S)
      (baseShadow_compact S hK) hne).inclusion.hom.left
    (OriginalNativeHSOuterSuccessor.neighbourhood S.history (baseShadow S)
      (baseShadow_compact S hK) hne).inclusion_isOpenImmersion
    S.inclusion.hom.left S.inclusion_isOpenImmersion
  contains := by
    intro x hx
    obtain ⟨b, hb⟩ := S.contains hx
    have hbK : b ∈ baseShadow S := by
      change S.inclusion.hom.left.base b ∈ K
      exact hb ▸ hx
    exact ⟨⟨b, (OriginalNativeHSOuterSuccessor.neighbourhood S.history (baseShadow S)
      (baseShadow_compact S hK) hne).contains hbK⟩, hb⟩

def next_sourceMap (S : State X K) (hK : IsCompact K) (hne : (singularShadow S).Nonempty) :
    (next S hK hne).source ⟶ S.source :=
  OriginalNativeHSOuterSuccessor.sourceMap S.history (baseShadow S) (baseShadow_compact S hK) hne

theorem next_projection_square (S : State X K) (hK : IsCompact K) (hne : (singularShadow S).Nonempty) :
    (next S hK hne).history.projection ≫ (next S hK hne).inclusion =
      next_sourceMap S hK hne ≫ S.history.projection ≫ S.inclusion :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun p => p ≫ S.inclusion) (OriginalNativeHSOuterSuccessor.projection_square
      S.history (baseShadow S) (baseShadow_compact S hK) hne)).trans (Category.assoc _ _ _))

theorem next_rank_drop (S : State X K) (hK : IsCompact K) (hne : (singularShadow S).Nonempty) :
    rankRelation hK (next S hK hne) S :=
  OriginalNativeHSOuterSuccessor.rank_drop S.history (baseShadow S) (baseShadow_compact S hK) hne

/-- Finite data of ACTUAL original-family phases, with their real surviving/empty decisions. -/
inductive Run (hK : IsCompact K) : State X K → Type 1
  | stop (S : State X K) (he : singularShadow S = ∅) : Run hK S
  | next (S : State X K) (hne : (singularShadow S).Nonempty)
      (tail : Run hK (OriginalNativeHSShadowOuterRun.next S hK hne)) : Run hK S

theorem exists_run (S : State X K) (hK : IsCompact K) : Nonempty (Run hK S) := by
  classical
  apply (rankRelation_wellFounded (X := X) (K := K) hK).induction S
  intro T ih
  rcases (singularShadow T).eq_empty_or_nonempty with he | hne
  · exact ⟨Run.stop T he⟩
  · obtain ⟨r⟩ := ih (next T hK hne) (next_rank_drop T hK hne)
    exact ⟨Run.next T hne r⟩

def run (S : State X K) (hK : IsCompact K) : Run hK S := (exists_run S hK).some

namespace Run
variable {hK : IsCompact K}

def finalState : {S : State X K} → Run hK S → State X K
  | S, .stop _ he => stopped S hK he
  | _, .next _ _ tail => finalState tail

def sourceMap : {S : State X K} → (r : Run hK S) → (finalState r).source ⟶ S.source
  | S, .stop _ he => OriginalNativeHSOuterEmptyStop.sourceInclusion S.history (baseShadow S)
      (baseShadow_compact S hK) he
  | S, .next _ hne tail => sourceMap tail ≫ next_sourceMap S hK hne

private theorem paste_after {A B C D E F : SourceReducedComplexSpace}
    (a : A ⟶ B) (p : B ⟶ C) (j : C ⟶ F) (b : B ⟶ D) (q : D ⟶ E) (i : E ⟶ F)
    (hs : p ≫ j = b ≫ q ≫ i) : a ≫ p ≫ j = (a ≫ b) ≫ q ≫ i :=
  (congrArg (fun f => a ≫ f) hs).trans (by simp only [Category.assoc])

theorem projection_square : {S : State X K} → (r : Run hK S) →
    (finalState r).history.projection ≫ (finalState r).inclusion =
      sourceMap r ≫ S.history.projection ≫ S.inclusion
  | S, .stop _ he => stopped_projection_square S hK he
  | S, .next _ hne tail =>
    (projection_square tail).trans (paste_after (sourceMap tail)
      (OriginalNativeHSShadowOuterRun.next S hK hne).history.projection (OriginalNativeHSShadowOuterRun.next S hK hne).inclusion
      (next_sourceMap S hK hne) S.history.projection S.inclusion (next_projection_square S hK hne))

theorem smooth : {S : State X K} → (r : Run hK S) → (finalState r).source.IsSmooth
  | S, .stop _ he => stopped_smooth S hK he
  | _, .next _ _ tail => smooth tail

theorem resolution {S : State X K} (r : Run hK S) : IsResolution (finalState r).history.projection :=
  (finalState r).history.singularModification.isResolution (smooth r)

theorem proper {S : State X K} (r : Run hK S) : IsProperMap (finalState r).history.projection.hom.left.base :=
  (finalState r).history.singularModification.isProperMap

theorem originalReg {S : State X K} (r : Run hK S) : IsIsoOver (finalState r).history.projection
    (intrinsicRegularLocus (finalState r).base.obj) :=
  (finalState r).history.singularModification.isIsoOver_intrinsicRegularLocus

theorem scalar {S : State X K} (r : Run hK S) : (finalState r).history.projection.hom.left ≫
    (finalState r).base.obj.hom = (finalState r).source.obj.hom :=
  Over.w (finalState r).history.projection.hom

end Run

/-- Ordinary X/K only: the actual finite native recipe is internally constructed. -/
def nearCompactState (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K) : State X K :=
  (run (initial X K) hK).finalState

theorem nearCompact_smooth (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K) :
    (nearCompactState X K hK).source.IsSmooth := Run.smooth (run (initial X K) hK)

theorem nearCompact_resolution (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K) :
    IsResolution (nearCompactState X K hK).history.projection := Run.resolution (run (initial X K) hK)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun
