import Hironaka.Analytic.Unibranch.OriginalNativeShadowRestrictedState

/-! Genuine base-open restriction of SAME partial canonical HS histories,
with entire records/ordered boundary and actual native quotient squares.
Blueprint FIRST: original-native-hs-open-prefix.tex. No smooth terminal
space, resolution, future centre or completed phase is an input. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOpenPrefix
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace
  HironakaG11PresLineState HironakaG11PresTowerState HironakaG11PresWindows
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism.MarkedIdeal HironakaActualPowerBoundaryExponents
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.HomogenizedGlueingTower (strictAlong)

/-- Ordinary genuine raw-record data, with no algorithmic output fields. -/
structure Input (n : ℕ) where
  ambient : CMfd.{0} n
  raw : MarkedIdeal n ambient
  originalCarrier : Set ambient
  profile : ℕ → ℕ
  domain : IsInvDomain n raw
  native : NativeHSState raw originalCarrier profile
  exponent : ℕ
  positive : 1 ≤ exponent

variable {n : ℕ} (P : Input n)
private abbrev invariant (n : ℕ) := (OriginalNativeHSPhaseHistory.originalInvariant n).toResolutionInvariant

def chosenRecord : MarkedIdeal n P.ambient := powerMarked P.raw P.exponent

theorem chosen_domain : IsInvDomain n (chosenRecord P) := powerMarked_isInvDomain _ P.domain P.positive

theorem chosen_state : HSTowerState (chosenRecord P) P.originalCarrier P.profile :=
  HSTowerState.of_wEquiv (HironakaG11InvCommonMark.wEquiv_powerMarked P.raw P.domain P.positive) P.native.hsTowerState

variable {Y : CMfd.{0} n} (T : BlowupTower P.ambient Y)
  (hT : IsCanonical (chosenRecord P) ((invariant n).inv (chosenRecord P)) T) (U : Opens P.ambient)

def restrictedRawRecord : MarkedIdeal n (CMfd.of (n := n) U) := pullback Subtype.val P.raw

theorem restricted_native : NativeHSState (restrictedRawRecord P U)
    ((Subtype.val : U → P.ambient) ⁻¹' P.originalCarrier) P.profile := P.native.restrict U

def restrictedRecord : MarkedIdeal n (CMfd.of (n := n) U) := pullback Subtype.val (chosenRecord P)

theorem restricted_power : restrictedRecord P U = powerMarked (restrictedRawRecord P U) P.exponent :=
  HironakaG11PresClassTransport.pullback_powerMarked contMDiff_subtype_val P.raw P.domain.isWellFormed.isCoherent P.exponent

include hT in
theorem restricted_canonical :
    IsCanonical (restrictedRecord P U) ((invariant n).inv (restrictedRecord P U)) (restrict U T) :=
  Seq.ResolutionInvariantExt.isCanonical_restrict (invariant n) (chosen_domain P) U T hT

include hT in
theorem restricted_transform : geoTransformAlong (restrictedRecord P U) (restrict U T) =
    pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong (chosenRecord P) T) :=
  MarkedIdealRestrictOpen.geoTransformAlong_restrict U (chosen_domain P).isWellFormed.isClosedSubmanifold_N
    (chosen_domain P).isWellFormed.isCoherent T
    ((invariant n).isInvValue.isGeoTestTower_of_isCanonical (chosen_domain P) T hT)

include hT in
theorem restricted_boundary : (geoTransformAlong (restrictedRecord P U) (restrict U T)).E =
    (geoTransformAlong (chosenRecord P) T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) :=
  congrArg MarkedIdeal.E (restricted_transform P T hT U)

include hT in
theorem restricted_value (z : openPreimage T U) (hz : z.val ∈ (geoTransformAlong (chosenRecord P) T).cosupp) :
    (invariant n).inv (restrictedRecord P U) (restrict U T) z = (invariant n).inv (chosenRecord P) T z.val :=
  (invariant n).isInvValue.restrictOpen _ (chosen_domain P) U T hT z hz

def carrier : Set Y := strictAlong T P.originalCarrier

include hT in
theorem carrier_analytic : IsComplexAnalyticSubset (n := n) (carrier P T) :=
  (chosen_state P T ((invariant n).isInvValue.isGeoTestTower_of_isCanonical (chosen_domain P) T hT)).1

theorem carrier_projection : carrier P T ⊆ T.proj ⁻¹' P.originalCarrier :=
  MemberInterTowerAlong.strictAlong_subset_preimage T P.native.2.1.isClosed

def restrictedCarrier : Set (openPreimage T U) :=
  strictAlong (restrict U T) ((Subtype.val : U → P.ambient) ⁻¹' P.originalCarrier)

theorem restrictedCarrier_eq : restrictedCarrier P T U =
    (Subtype.val : openPreimage T U → Y) ⁻¹' carrier P T :=
  HironakaG11StrictTransformTowers.strictAlong_restrict U T P.originalCarrier

def baseSpace : SourceReducedComplexSpace := ofClosedAnalytic P.originalCarrier P.native.2.1

def sourceSpace : SourceReducedComplexSpace := ofClosedAnalytic (carrier P T) (carrier_analytic P T hT)

def projection : sourceSpace P T hT ⟶ baseSpace P :=
  ObjectProperty.homMk (Over.homMk (actualSubspaceMap T.contMDiff_proj (carrier_projection P T))
    (actualSubspaceMap_point T.contMDiff_proj (carrier_projection P T)))

def restrictedBase : SourceReducedComplexSpace :=
  ofClosedAnalytic ((Subtype.val : U → P.ambient) ⁻¹' P.originalCarrier)
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val P.native.2.1 U)

/-- The actual terminal-open trace; restrictedCarrier_eq identifies the WHOLE canonical strict carrier. -/
def restrictedSource : SourceReducedComplexSpace :=
  ofClosedAnalytic ((Subtype.val : openPreimage T U → Y) ⁻¹' carrier P T)
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val (carrier_analytic P T hT) (openPreimage T U))

def baseInclusion : restrictedBase P U ⟶ baseSpace P :=
  ObjectProperty.homMk (Over.homMk (actualOpenSubspaceMap (n := n) P.originalCarrier U)
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)))

instance baseInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (baseInclusion P U).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (actualOpenSubspaceMap (n := n) P.originalCarrier U)
  infer_instance

def sourceInclusion : restrictedSource P T hT U ⟶ sourceSpace P T hT :=
  ObjectProperty.homMk (Over.homMk (actualOpenSubspaceMap (n := n) (carrier P T) (openPreimage T U))
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)))

instance sourceInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion P T hT U).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (actualOpenSubspaceMap (n := n) (carrier P T) (openPreimage T U))
  infer_instance

private theorem restricted_projection_mem (z : (restrictedSource P T hT U).obj.left) :
    ((restrict U T).proj z.val).val ∈ P.originalCarrier := by
  rw [proj_restrict U T z.val]
  exact carrier_projection P T z.property

def restrictedProjection : restrictedSource P T hT U ⟶ restrictedBase P U :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (restrict U T).contMDiff_proj (fun z hz => restricted_projection_mem P T hT U ⟨z, hz⟩))
    (actualSubspaceMap_point (restrict U T).contMDiff_proj (fun z hz => restricted_projection_mem P T hT U ⟨z, hz⟩)))

theorem projection_square :
    restrictedProjection P T hT U ≫ baseInclusion P U = sourceInclusion P T hT U ≫ projection P T hT := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  exact proj_restrict U T z.val

theorem sourceInclusion_range : range (sourceInclusion P T hT U).hom.left.base =
    (projection P T hT).hom.left.base ⁻¹' range (baseInclusion P U).hom.left.base := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨(restrict U T).proj y.val, restricted_projection_mem P T hT U y⟩,
      Subtype.ext (proj_restrict U T y.val)⟩
  · rintro ⟨x, hx⟩
    have hz : z.val ∈ openPreimage T U := by
      change T.proj z.val ∈ U
      have h : x.val.val = T.proj z.val := congrArg Subtype.val hx
      exact h ▸ x.val.property
    exact ⟨⟨⟨z.val, hz⟩, z.property⟩, rfl⟩

theorem restrictedProjection_scalar :
    (restrictedProjection P T hT U).hom.left ≫ (restrictedBase P U).obj.hom =
      (restrictedSource P T hT U).obj.hom := Over.w (restrictedProjection P T hT U).hom

/-- Concrete consumer of the ACTUALLY derived compact-shadow native records. -/
def ofShadow {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    (M : OriginalNativeHSCompactShadowWindows.Maximum X K) (hK : IsCompact K) (i : (M.windows hK).ι) :
    Input (OriginalLocalEmbeddingStalkHS.originalStalkHS X M.point 1 - 1) where
  ambient := (OriginalNativeShadowFirstPrefix.manifoldCentres M hK).ambient i
  raw := OriginalNativeShadowRestrictedState.rawRecord M hK i
  originalCarrier := (OriginalNativeShadowFirstBlowup.centres M hK).windowCarrier i
  profile := OriginalLocalEmbeddingStalkHS.originalStalkHS X M.point
  domain := OriginalNativeShadowRestrictedState.raw_domain M hK i
  native := OriginalNativeShadowRestrictedState.raw_native M hK i
  exponent := OriginalNativeShadowInvariantCentre.exponent M hK i
  positive := OriginalNativeShadowInvariantCentre.exponent_pos M hK i

theorem ofShadow_chosen {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    (M : OriginalNativeHSCompactShadowWindows.Maximum X K) (hK : IsCompact K) (i : (M.windows hK).ι) :
    chosenRecord (ofShadow M hK i) = OriginalNativeShadowFirstPrefix.record M hK i :=
  (OriginalNativeShadowRestrictedState.chosen_eq_power M hK i).symm

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOpenPrefix
