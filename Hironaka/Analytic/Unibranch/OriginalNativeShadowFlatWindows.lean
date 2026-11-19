import Hironaka.Analytic.Unibranch.OriginalNativeHSTowerIsoRestriction
import Hironaka.Analytic.Unibranch.HironakaG1NativeWindowInitialClass

/-! Flatten the SAME INITIAL nested native windows into actual fixed-dim
coordinate embeddings, retaining true raw state/common powers and whole
canonical histories. Blueprint FIRST: original-native-shadow-flat-windows.tex.
CURRENT transformed records with born E are never reset as initial records. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowFlatWindows
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  OriginalNativeHSCompactShadowWindows HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11PresLineState HironakaG11PresReduction HironakaG11CompatibleCanonicalTowers
  HironakaG11StrictTransformTowers HironakaG1CanonicalStageCentreIdeal
  BlowupTowers BlowupTowerIsomorphism MarkedIdealTowerTransport MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism.MarkedIdeal HironakaActualPowerBoundaryExponents
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

private def flatOpen {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (O : Opens e.ambient) :
    Opens (ComplexModel e.dim) :=
  ⟨(Subtype.val : e.ambient → ComplexModel e.dim) '' O,
    e.ambient.isOpen.isOpenMap_subtype_val _ O.isOpen⟩

private theorem flatOpen_subset {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (O : Opens e.ambient) :
    flatOpen e O ≤ e.ambient := by
  rintro _ ⟨z, -, rfl⟩
  exact z.property

private theorem flat_dictionary {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (O : Opens e.ambient)
    (z : e.ambient) : z ∈ O ↔ z.val ∈ flatOpen e O := by
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨y, hy, heq⟩
    exact (Subtype.ext heq : y = z) ▸ hy

private def flatEquiv {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (O : Opens e.ambient) :
    CMfd.of (n := e.dim) (flatOpen e O) ≃ₘ⟮𝓘(ℂ, ComplexModel e.dim), 𝓘(ℂ, ComplexModel e.dim)⟯ CMfd.of (n := e.dim) O :=
  (MaxLocusLocal.nestedDiffeo e.ambient O (flatOpen e O) (flat_dictionary e O) (flatOpen_subset e O)).symm

private def flatWindow {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (O : Opens e.ambient) :
    DimEmbedding Y e.dim :=
  DimEmbedding.ofLocalEmbedding
    (e.restrictWith (flatOpen e O) (flatOpen_subset e O)
      ((flatEquiv e O) ⁻¹' ((Subtype.val : O → e.ambient) ⁻¹' e.carrier)) (fun _ => Iff.rfl))

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
private abbrev dimension := originalStalkHS X M.point 1 - 1
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F" => OriginalNativeShadowFirstBlowup.centres M hK

private abbrev oldAmbient (i : (M.windows hK).ι) : CMfd.{0} (dimension M) :=
  (OriginalNativeShadowFirstPrefix.manifoldCentres M hK).ambient i

def coordinateOpen (i : (M.windows hK).ι) : Opens (ComplexModel (dimension M)) :=
  flatOpen ((F).emb i) ((F).window i)

theorem coordinateOpen_subset (i : (M.windows hK).ι) : coordinateOpen M hK i ≤ ((F).emb i).ambient :=
  flatOpen_subset ((F).emb i) ((F).window i)

theorem coordinate_dictionary (i : (M.windows hK).ι) (z : ((F).emb i).ambient) :
    z ∈ (F).window i ↔ z.val ∈ coordinateOpen M hK i :=
  flat_dictionary ((F).emb i) ((F).window i) z

/-- Actual coordinate equivalence, with its literal inverse point formulas. -/
def ambientEquiv (i : (M.windows hK).ι) :
    CMfd.of (n := (dimension M)) (coordinateOpen M hK i) ≃ₘ⟮𝓘(ℂ, ComplexModel (dimension M)), 𝓘(ℂ, ComplexModel (dimension M))⟯ oldAmbient M hK i :=
  flatEquiv ((F).emb i) ((F).window i)

/-- WHOLE original initial window, with the coordinate flattening constructed internally. -/
def window (i : (M.windows hK).ι) : DimEmbedding (N).source (dimension M) :=
  flatWindow ((F).emb i) ((F).window i)

def baseMap (i : (M.windows hK).ι) :
    ofClosedAnalytic (window M hK i).carrier (window M hK i).analytic ⟶ (F).windowSpace i :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (ambientEquiv M hK i).contMDiff (fun _ hx => hx))
    (actualSubspaceMap_point (ambientEquiv M hK i).contMDiff (fun _ hx => hx)))

theorem base_square (i : (M.windows hK).ι) :
    baseMap M hK i ≫ (F).windowMap i =
      EmbeddedBlowupOverlap.chartMorphism (window M hK i).toLocalEmbedding := by
  apply morphism_eq_of_pointwise_eq
  intro z
  rfl

theorem range_dictionary (i : (M.windows hK).ι) :
    range (window M hK i).toLocalEmbedding.toPoint = range ((F).windowMap i).hom.left.base := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(baseMap M hK i).hom.left.base z,
      congrArg (fun f => f.hom.left.base z) (base_square M hK i)⟩
  · rintro ⟨z, rfl⟩
    let y : (window M hK i).carrier :=
      ⟨(ambientEquiv M hK i).symm z.val, by
        change ambientEquiv M hK i ((ambientEquiv M hK i).symm z.val) ∈ (F).windowCarrier i
        exact (ambientEquiv M hK i).apply_symm_apply z.val |>.symm ▸ z.property⟩
    have hy : (baseMap M hK i).hom.left.base y = z :=
      Subtype.ext ((ambientEquiv M hK i).apply_symm_apply z.val)
    exact ⟨y, (congrArg (fun f => f.hom.left.base y) (base_square M hK i)).symm.trans
      (congrArg ((F).windowMap i).hom.left.base hy)⟩

private def pullbackOld (i : (M.windows hK).ι) (Q : MarkedIdeal (dimension M) (oldAmbient M hK i)) :
    MarkedIdeal (dimension M) (Amb (window M hK) i) :=
  @pullback (dimension M) (oldAmbient M hK i).carrier
    (oldAmbient M hK i).topologicalSpace (oldAmbient M hK i).chartedSpace
    (Amb (window M hK) i).carrier (Amb (window M hK) i).topologicalSpace
    (Amb (window M hK) i).chartedSpace (ambientEquiv M hK i) Q

def rawRecord (i : (M.windows hK).ι) : MarkedIdeal (dimension M) (Amb (window M hK) i) :=
  pullbackOld M hK i (OriginalNativeShadowRestrictedState.rawRecord M hK i)

theorem raw_domain (i : (M.windows hK).ι) : IsInvDomain (dimension M) (rawRecord M hK i) :=
  InvDomainTowerAlong.isInvDomain_pullback (ambientEquiv M hK i)
    (OriginalNativeShadowRestrictedState.raw_domain M hK i)

theorem raw_native (i : (M.windows hK).ι) :
    NativeHSState (rawRecord M hK i) (window M hK i).carrier (originalStalkHS X M.point) :=
  NativeHSState.pullback (ambientEquiv M hK i) (OriginalNativeShadowRestrictedState.raw_native M hK i)

theorem raw_boundary (i : (M.windows hK).ι) : (rawRecord M hK i).E = [] := by
  change (OriginalNativeShadowRestrictedState.rawRecord M hK i).E.map _ = []
  rw [OriginalNativeShadowRestrictedState.raw_boundary M hK i, List.map_nil]

theorem native_record (i : (M.windows hK).ι) :
    IsNativeWindowRecord (window M hK i) (rawRecord M hK i) (originalStalkHS X M.point) :=
  ⟨raw_domain M hK i, raw_boundary M hK i, raw_native M hK i⟩

def record (i : (M.windows hK).ι) : MarkedIdeal (dimension M) (Amb (window M hK) i) :=
  powerMarked (rawRecord M hK i) (OriginalNativeShadowInvariantCentre.exponent M hK i)

theorem record_eq_pullback (i : (M.windows hK).ι) : record M hK i =
    pullbackOld M hK i (OriginalNativeShadowFirstPrefix.record M hK i) := by
  rw [OriginalNativeShadowRestrictedState.chosen_eq_power M hK i]
  exact (HironakaG11PresClassTransport.pullback_powerMarked
    (M := oldAmbient M hK i) (M' := Amb (window M hK) i) (ambientEquiv M hK i).contMDiff _
    (OriginalNativeShadowRestrictedState.raw_domain M hK i).isWellFormed.isCoherent _).symm

theorem record_mark (i : (M.windows hK).ι) :
    (record M hK i).d = OriginalNativeShadowInvariantCentre.commonMark M hK :=
  (congrArg MarkedIdeal.d (record_eq_pullback M hK i)).trans (OriginalNativeShadowFirstPrefix.record_mark M hK i)

theorem initialClass : InitialClassData (window M hK) (record M hK) :=
  HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers (window M hK) (rawRecord M hK) _
    (native_record M hK) (OriginalNativeShadowInvariantCentre.exponent M hK)
    (OriginalNativeShadowInvariantCentre.exponent_pos M hK)
    (fun i j => (record_mark M hK i).trans (record_mark M hK j).symm)

variable (i : (M.windows hK).ι) {Y : CMfd.{0} (dimension M)}
  (T : BlowupTower (oldAmbient M hK i) Y)

/-- Genuine physical transport of the SAME old prefix through the actual flat base. -/
def transport : TowerTransport (Amb (window M hK) i) Y :=
  MarkedIdealTowerTransport.transport (ambientEquiv M hK i) T

theorem transport_isTowerIso : IsTowerIso (ambientEquiv M hK i) (transport M hK i T).tower T (transport M hK i T).back :=
  BlowupTowerIsomorphism.transport_isTowerIso (ambientEquiv M hK i) T

private abbrev invariant := (OriginalNativeShadowInvariantCentre.invariant M).toResolutionInvariant

variable (hT : IsCanonical (OriginalNativeShadowFirstPrefix.record M hK i)
  ((invariant M).inv (OriginalNativeShadowFirstPrefix.record M hK i)) T)

include hT in
theorem transport_canonical : IsCanonical (record M hK i) ((invariant M).inv (record M hK i))
    (transport M hK i T).tower := by
  rw [record_eq_pullback M hK i]
  exact Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (invariant M)
    (OriginalNativeShadowFirstPrefix.domain M hK i) (ambientEquiv M hK i) (transport_isTowerIso M hK i T) hT

theorem transport_length : (transport M hK i T).tower.length = T.length :=
  (transport_isTowerIso M hK i T).length_eq

include hT in
theorem transport_record : geoTransformAlong (record M hK i) (transport M hK i T).tower =
    pullback (transport M hK i T).back (geoTransformAlong (OriginalNativeShadowFirstPrefix.record M hK i) T) := by
  rw [record_eq_pullback M hK i]
  exact BlowupTowerIsomorphism.IsTowerIso.geoTransformAlong_eq (ambientEquiv M hK i)
    (OriginalNativeShadowFirstPrefix.domain M hK i).isWellFormed.isClosedSubmanifold_N
    (OriginalNativeShadowFirstPrefix.domain M hK i).isWellFormed.isCoherent
    (transport_isTowerIso M hK i T)
    ((invariant M).isInvValue.isGeoTestTower_of_isCanonical (OriginalNativeShadowFirstPrefix.domain M hK i) T hT)

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowFlatWindows
