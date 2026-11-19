import Hironaka.Analytic.Unibranch.OriginalNativeShadowInvariantCentre
import Hironaka.Analytic.Unibranch.OriginalNativeHSCompactShadowBarrier
import Hironaka.Analytic.Unibranch.OriginalNativeCentreOpenPullback

/-! ONE genuine original native invariant-centre blowup near a compact
shadow. All levels, centres, target opens and blowup geometry are derived
from ordinary source data. Blueprint FIRST:
original-native-shadow-first-blowup.tex.
No dynamic shrinking phase or finite noncompact factory is asserted. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstBlowup
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11CompatibleAnalyticCover
  HironakaG11SingularCentreModification OriginalNativeHSCompactShadowWindows

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)

/-- The actual precompact target is derived from full local compatibility. -/
def target :=
  OriginalNativeCentreLocalClosedness.target
    (OriginalNativeShadowInvariantCentre.centres M hK) M.threshold M.threshold_closed K hK
    (OriginalNativeShadowInvariantCentre.shadow_covered M hK)

/-- SAME labelled centres, with actual native open-window/centre maps. -/
def centres : LocalSmoothCentres (target M hK).source (M.windows hK).ι :=
  OriginalNativeCentreOpenPullback.family
    (OriginalNativeShadowInvariantCentre.centres M hK)
    (target M hK).inclusion (target M hK).inclusion_isOpenImmersion

theorem centres_compatible : (centres M hK).Compatible :=
  OriginalNativeCentreOpenPullback.compatible _ _ _
    (OriginalNativeShadowInvariantCentre.centres_compatible M hK)

theorem centres_closed : IsClosed (centres M hK).support := by
  have he := OriginalNativeCentreOpenPullback.support_eq_preimage
    (OriginalNativeShadowInvariantCentre.centres M hK)
    (target M hK).inclusion (target M hK).inclusion_isOpenImmersion
  exact he.symm ▸ OriginalNativeCentreLocalClosedness.target_centre_closed
    (OriginalNativeShadowInvariantCentre.centres M hK) M.threshold M.threshold_closed
    (OriginalNativeShadowInvariantCentre.centres_compatible M hK)
    (OriginalNativeShadowInvariantCentre.support_threshold M hK) K hK
    (OriginalNativeShadowInvariantCentre.shadow_covered M hK)

theorem centres_singular : (centres M hK).support ⊆
    intrinsicSingularLocus (target M hK).source.obj :=
  OriginalNativeCentreOpenPullback.support_subset_intrinsicSingularLocus _ _ _
    (OriginalNativeShadowInvariantCentre.support_singular M hK)

theorem centre_meets_shadow :
    ((target M hK).inclusion.hom.left.base ⁻¹' K ∩ (centres M hK).support).Nonempty := by
  obtain ⟨x, hxK, hxC⟩ := OriginalNativeShadowInvariantCentre.centre_meets_shadow M hK
  let y : (target M hK).source.obj.left := ⟨x, (target M hK).contains hxK⟩
  refine ⟨y, hxK, ?_⟩
  have he := OriginalNativeCentreOpenPullback.support_eq_preimage
    (OriginalNativeShadowInvariantCentre.centres M hK)
    (target M hK).inclusion (target M hK).inclusion_isOpenImmersion
  exact (Set.ext_iff.mp he y).mpr hxC

/-- Output data of ONE actual native blowup, with its literal whole scheme centre. -/
structure Step where
  centre_analytic : (target M hK).source.IsAnalyticSubset (centres M hK).support
  source : SourceReducedComplexSpace
  projection : source ⟶ (target M hK).source
  blowup : SmoothCentreModification.IsSmoothCentreBlowup projection
    (OriginalAnalyticClosedSubspace.inclusion (target M hK).source
      (centres M hK).support centre_analytic)
  singular : IsSingularCentreStep projection
  surjective : Function.Surjective projection.hom.left.base
  isoOver : IsIsoOver projection (centres M hK).supportᶜ

theorem exists_step : Nonempty (Step M hK) := by
  obtain ⟨hS, Y, p, hb, hs, -, hsurj, hi⟩ :=
    (centres M hK).exists_singularCentreBlowup (centres_compatible M hK)
      (centres_closed M hK) (centres_singular M hK)
  exact ⟨⟨hS, Y, p, hb, hs, hsurj, hi⟩⟩

def step : Step M hK := (exists_step M hK).some

namespace Step
variable {M hK} (s : Step M hK)

theorem modification : IsSingularCentreModification s.projection :=
  s.singular.isSingularCentreModification

theorem proper : IsProperMap s.projection.hom.left.base := s.modification.isProperMap

theorem regular : IsIsoOver s.projection (intrinsicRegularLocus (target M hK).source.obj) :=
  s.modification.isIsoOver_intrinsicRegularLocus

theorem shadow_compact : IsCompact
    (s.projection.hom.left.base ⁻¹' ((target M hK).inclusion.hom.left.base ⁻¹' K)) :=
  s.proper.isCompact_preimage ((target M hK).shadow_compact hK)

theorem scalar : s.projection.hom.left ≫ (target M hK).source.obj.hom = s.source.obj.hom :=
  Over.w s.projection.hom

end Step

/-- The actual compact shadow in the TRUE native HS barrier. -/
def barrierShadow : Set (OriginalNativeHSCompactShadowBarrier.nativeSource M hK).obj.left :=
  (OriginalNativeHSCompactShadowBarrier.nativeInclusion M hK).hom.left.base ⁻¹' K

theorem barrierShadow_compact : IsCompact (barrierShadow M hK) :=
  OriginalNativeHSCompactShadowBarrier.native_shadow_compact M hK

/-- Use the SAME attained point and derived global singular bound. -/
def barrierMaximum : Maximum
    (OriginalNativeHSCompactShadowBarrier.nativeSource M hK) (barrierShadow M hK) where
  point := OriginalNativeHSCompactShadowBarrier.nativePoint M hK
  in_compact := M.in_compact
  singular := OriginalNativeHSCompactShadowBarrier.nativePoint_singular M hK
  maximal y _ hy := OriginalNativeHSCompactShadowBarrier.native_maximal M hK y hy

/-- Full original native inclusion of the actual first-step target. -/
def originalTargetInclusion :
    (target (barrierMaximum M hK) (barrierShadow_compact M hK)).source ⟶ X :=
  (target (barrierMaximum M hK) (barrierShadow_compact M hK)).inclusion ≫
    OriginalNativeHSCompactShadowBarrier.nativeInclusion M hK

instance originalTarget_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (originalTargetInclusion M hK).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    ((target (barrierMaximum M hK) (barrierShadow_compact M hK)).inclusion.hom.left ≫
      (OriginalNativeHSCompactShadowBarrier.nativeInclusion M hK).hom.left)
  infer_instance

theorem originalTarget_contains_shadow : K ⊆ range (originalTargetInclusion M hK).hom.left.base := by
  intro x hx
  obtain ⟨y, hy⟩ := OriginalNativeHSCompactShadowBarrier.compact_subset_native_range M hK hx
  have hyK : y ∈ barrierShadow M hK := by
    change (OriginalNativeHSCompactShadowBarrier.nativeInclusion M hK).hom.left.base y ∈ K
    rw [hy]
    exact hx
  let N := target (barrierMaximum M hK) (barrierShadow_compact M hK)
  let z : N.source.obj.left := ⟨y, N.contains hyK⟩
  exact ⟨z, hy⟩

/-- Only ordinary X,K, compactness and a singular shadow point are inputs. -/
def originalStep (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K)
    (hne : (K ∩ intrinsicSingularLocus X.obj).Nonempty) :
    Step (barrierMaximum (maximum X K hK hne) hK)
      (barrierShadow_compact (maximum X K hK hne) hK) :=
  step (barrierMaximum (maximum X K hK hne) hK)
    (barrierShadow_compact (maximum X K hK hne) hK)

variable (s : Step (barrierMaximum M hK) (barrierShadow_compact M hK))

def originalProjection : s.source ⟶ X := s.projection ≫ originalTargetInclusion M hK

theorem originalProjection_scalar :
    (originalProjection M hK s).hom.left ≫ X.obj.hom = s.source.obj.hom :=
  Over.w (originalProjection M hK s).hom

theorem original_shadow_compact :
    IsCompact ((originalProjection M hK s).hom.left.base ⁻¹' K) :=
  s.shadow_compact

theorem original_regular_protection : IsIsoOver s.projection
    ((originalTargetInclusion M hK).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
  let N := target (barrierMaximum M hK) (barrierShadow_compact M hK)
  have h0 := (OriginalNativeHSCompactShadowBarrier.nativeNeighbourhood M hK).preimage_regular
  have h1 : (originalTargetInclusion M hK).hom.left.base ⁻¹' intrinsicRegularLocus X.obj =
      intrinsicRegularLocus N.source.obj :=
    (congrArg (fun A => N.inclusion.hom.left.base ⁻¹' A) h0).trans N.preimage_regular
  exact h1.symm ▸ s.regular

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstBlowup
