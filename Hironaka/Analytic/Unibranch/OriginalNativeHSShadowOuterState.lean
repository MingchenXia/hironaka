import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEmptyStop
import Hironaka.Analytic.Unibranch.OriginalNativeCompactShadowRank

/-! Ordinary actual native history/base-OI states for the compact-shadow OUTER run.
Rank uses realized HSValue/Bennett DM, never Lex-WF/global compactness.
Blueprint FIRST: original-native-hs-shadow-outer-state.tex.
No selected phase, next endpoint, rank-drop certificate or future oracle field. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterState
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalNativeHSOuterHistory
  HironakaIntrinsicComplexAnalyticRegularLocus

/-- ONLY ordinary PRESENT geometry and one actual finite chronological history. -/
structure State (X : SourceReducedComplexSpace) (K : Set X.obj.left) where
  base : SourceReducedComplexSpace
  source : SourceReducedComplexSpace
  history : PhysicalHistory base source
  inclusion : base ⟶ X
  inclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion inclusion.hom.left
  contains : K ⊆ range inclusion.hom.left.base

def initial (X : SourceReducedComplexSpace) (K : Set X.obj.left) : State X K where
  base := X
  source := X
  history := .nil X
  inclusion := 𝟙 X
  inclusion_isOpenImmersion := by
    change LocallyRingedSpace.IsOpenImmersion (𝟙 X.obj.left)
    infer_instance
  contains := fun x _ => ⟨x, rfl⟩

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left} (S : State X K)

def baseShadow : Set S.base.obj.left := S.inclusion.hom.left.base ⁻¹' K

theorem baseShadow_compact (hK : IsCompact K) : IsCompact (baseShadow S) :=
  S.inclusion_isOpenImmersion.base_open.isEmbedding.isInducing.isCompact_preimage' hK S.contains

def shadow : Set S.source.obj.left := S.history.projection.hom.left.base ⁻¹' baseShadow S

theorem shadow_compact (hK : IsCompact K) : IsCompact (shadow S) :=
  S.history.singularModification.isProperMap.isCompact_preimage (baseShadow_compact S hK)

def singularShadow : Set S.source.obj.left := intrinsicSingularLocus S.source.obj ∩ shadow S

def rank (hK : IsCompact K) : Multiset HironakaG11HSPhaseInduction.HSValue :=
  OriginalNativeCompactShadowRank.rank S.source (shadow S) (shadow_compact S hK)

def rankRelation (hK : IsCompact K) (T S : State X K) : Prop :=
  Multiset.IsDershowitzMannaLT (rank T hK) (rank S hK)

theorem rankRelation_wellFounded (hK : IsCompact K) :
    WellFounded (rankRelation (X := X) (K := K) hK) :=
  InvImage.wf (fun S : State X K => rank S hK) OriginalNativeCompactShadowRank.rank_order_wellFounded

/-- The ACTUAL outer empty-shadow stop, retaining all original K through the base OI. -/
def stopped (hK : IsCompact K) (he : singularShadow S = ∅) : State X K where
  base := (OriginalNativeHSOuterEmptyStop.neighbourhood S.history (baseShadow S)
    (baseShadow_compact S hK) he).source
  source := OriginalNativeHSOuterEmptyStop.source S.history (baseShadow S) (baseShadow_compact S hK) he
  history := OriginalNativeHSOuterEmptyStop.physicalHistory S.history (baseShadow S) (baseShadow_compact S hK) he
  inclusion := (OriginalNativeHSOuterEmptyStop.neighbourhood S.history (baseShadow S)
    (baseShadow_compact S hK) he).inclusion ≫ S.inclusion
  inclusion_isOpenImmersion := @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (OriginalNativeHSOuterEmptyStop.neighbourhood S.history (baseShadow S)
      (baseShadow_compact S hK) he).inclusion.hom.left
    (OriginalNativeHSOuterEmptyStop.neighbourhood S.history (baseShadow S)
      (baseShadow_compact S hK) he).inclusion_isOpenImmersion
    S.inclusion.hom.left S.inclusion_isOpenImmersion
  contains := by
    intro x hx
    obtain ⟨b, hb⟩ := S.contains hx
    have hbK : b ∈ baseShadow S := by
      change S.inclusion.hom.left.base b ∈ K
      exact hb ▸ hx
    exact ⟨⟨b, (OriginalNativeHSOuterEmptyStop.neighbourhood S.history (baseShadow S)
      (baseShadow_compact S hK) he).contains hbK⟩, hb⟩

theorem stopped_smooth (hK : IsCompact K) (he : singularShadow S = ∅) :
    (stopped S hK he).source.IsSmooth :=
  OriginalNativeHSOuterEmptyStop.smooth S.history (baseShadow S) (baseShadow_compact S hK) he

theorem stopped_resolution (hK : IsCompact K) (he : singularShadow S = ∅) :
    IsResolution (stopped S hK he).history.projection :=
  OriginalNativeHSOuterEmptyStop.resolution S.history (baseShadow S) (baseShadow_compact S hK) he

theorem stopped_length (hK : IsCompact K) (he : singularShadow S = ∅) :
    (stopped S hK he).history.length = S.history.length :=
  OriginalNativeHSOuterEmptyStop.physical_length S.history (baseShadow S) (baseShadow_compact S hK) he

theorem stopped_projection_square (hK : IsCompact K) (he : singularShadow S = ∅) :
    (stopped S hK he).history.projection ≫ (stopped S hK he).inclusion =
      OriginalNativeHSOuterEmptyStop.sourceInclusion S.history (baseShadow S)
        (baseShadow_compact S hK) he ≫ S.history.projection ≫ S.inclusion :=
  OriginalNativeHSOuterEmptyStop.projection_comp S.history (baseShadow S)
    (baseShadow_compact S hK) he S.inclusion

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterState
