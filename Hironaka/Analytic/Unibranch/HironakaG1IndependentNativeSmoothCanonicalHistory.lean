import Hironaka.Analytic.Unibranch.OriginalNativeProductSelectedState
import Hironaka.Analytic.Unibranch.OriginalNativeProductHSMinimalDimension
import Hironaka.Resolution.HironakaG1NativeProductCanonicalComparison
import Hironaka.Resolution.HironakaOriginalSourceChoiceCartesian

/-! Actual chosen native inputs produce their local smooth CAN history.
Blueprint FIRST: hironaka-g1-independent-native-smooth-canonical-history.tex.
No desired product-state, future-history or source-CAN packet is input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.HironakaG1IndependentNativeSmoothCanonicalHistory
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaReducedComplexAnalyticSpaces
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HironakaG11PresLineState HironakaG11VanishingWindows
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionOriginalGlobalFinite
  OriginalNativeProductWindow OriginalNativeSmoothGivenTargetWindow
  OriginalNativeProductIndependentRecord OriginalNativeProductSelectedState OriginalNativeProductHSMinimalDimension
  OriginalLocalEmbeddingStalkHS HironakaG1NativeFiniteProductState
  HironakaG1NativeProductCanonicalComparison HironakaActualPowerBoundaryExponents
  HironakaG8LocalPower HironakaG8LocalHistory HironakaG1OriginalUnequalMarkCanonical
  MarkedIdealTowerTransport BlowupTowerIsomorphism HironakaG11PresClassTransport

open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

def targetInclusion (e : LocalEmbedding Y) (B : Opens (ComplexModel e.dim)) (hB : B≤e.ambient) :
    B → e.ambient := Opens.inclusion hB

def targetRecord (e : LocalEmbedding Y)
    (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient))
    (B : Opens (ComplexModel e.dim)) (hB : B≤e.ambient) :
    MarkedIdeal e.dim (CMfd.of (n := e.dim) B) := markedPullback (targetInclusion e B hB) Q

private theorem target_inclusion_submersion (e : LocalEmbedding Y)
    (B : Opens (ComplexModel e.dim)) (hB : B≤e.ambient) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel e.dim) ∞
      (targetInclusion e B hB) := by
  let Φ:=opensWithinDiffeo e.ambient B hB
  change Manifold.IsSubmersion 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel e.dim) ∞
    ((Subtype.val : opensWithin e.ambient B → e.ambient) ∘ Φ)
  exact isSubmersion_composition (X := CMfd.of (n := e.dim) e.ambient)
    (Y := CMfd.of (n := e.dim) (opensWithin e.ambient B)) (Z := CMfd.of (n := e.dim) B)
    (isSubmersion_val (A := CMfd.of (n := e.dim) e.ambient) (opensWithin e.ambient B))
    (isSubmersion_biholomorphism
      (D := CMfd.of (n := e.dim) B) (C := CMfd.of (n := e.dim) (opensWithin e.ambient B)) Φ)

private theorem target_initial_native_data (e : LocalEmbedding Y)
    (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient))
    (hQ : IsInvDomain e.dim Q) (hE : Q.E=[]) {H : ℕ → ℕ}
    (hState : NativeHSState Q e.carrier H)
    (B : Opens (ComplexModel e.dim)) (hB : B≤e.ambient) :
    IsInvDomain e.dim (targetRecord e Q B hB) ∧ (targetRecord e Q B hB).E=[] ∧
      NativeHSState (targetRecord e Q B hB) (e.restrict B hB).carrier H := by
  let Φ:=opensWithinDiffeo e.ambient B hB
  have heq : targetRecord e Q B hB=
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback
        (Subtype.val : opensWithin e.ambient B → e.ambient) Q) := by
    change markedPullback ((Subtype.val : opensWithin e.ambient B → e.ambient) ∘ Φ) Q=_
    exact whole_markedPullback_comp contMDiff_subtype_val Φ.contMDiff Q hQ.isWellFormed.isCoherent
  have hNative : NativeHSState (targetRecord e Q B hB) (e.restrict B hB).carrier H := by
    rw [heq]
    exact NativeHSState.pullback (X' := CMfd.of (n := e.dim) B) Φ
      (hState.restrict (opensWithin e.ambient B))
  have hf:=target_inclusion_submersion e B hB
  have hD:=original_ambient_domain_pullback (X := CMfd.of (n := e.dim) e.ambient)
    (Y := CMfd.of (n := e.dim) B) hf Q hQ
  have hEmpty : (targetRecord e Q B hB).E=[]:=by
    change Q.E.map ((targetInclusion e B hB) ⁻¹' ·)=[]
    rw [hE];rfl
  exact ⟨hD,hEmpty,hNative⟩

/-- The target's actual native restriction AND its genuine restricted
Cartesian canonical tower are constructed from the ORIGINAL given T. -/
theorem target_native_restriction (e : LocalEmbedding Y)
    (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient))
    (hQ : IsInvDomain e.dim Q) (hE : Q.E=[]) {H : ℕ → ℕ}
    (hState : NativeHSState Q e.carrier H)
    (B : Opens (ComplexModel e.dim)) (hB : B≤e.ambient)
    {D : CMfd.{0} e.dim} (T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D)
    (hCan : IsCanonical Q ((canonicalInvariant e.dim).inv Q) T) :
    ∃(D0 : CMfd.{0} e.dim)(T0 : BlowupTower (CMfd.of (n := e.dim) B) D0)(g0 : D0 → D),
      IsActualTowerPullback (targetInclusion e B hB) T0 T g0 ∧
      IsInvDomain e.dim (targetRecord e Q B hB) ∧ (targetRecord e Q B hB).E=[] ∧
      NativeHSState (targetRecord e Q B hB) (e.restrict B hB).carrier H ∧
      IsCanonical (targetRecord e Q B hB)
        ((canonicalInvariant e.dim).inv (targetRecord e Q B hB)) T0 := by
  obtain ⟨hD,hEmpty,hNative⟩:=target_initial_native_data e Q hQ hE hState B hB
  have hf:=target_inclusion_submersion e B hB
  obtain ⟨D0,T0,g0,hp⟩:=exists_actual_tower (X := CMfd.of (n := e.dim) e.ambient)
    (Y := CMfd.of (n := e.dim) B) hf T
  exact ⟨D0,T0,g0,hp,hD,hEmpty,hNative,
    HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical hp Q hQ hCan⟩

/-- ONLY transport along an actual equality of ambient dimensions. -/
def castWindowPoint {N L : ℕ} (h : N=L) (d : DimEmbedding X N) (c : d.carrier) :
    (d.cast h).carrier := by cases h;exact c

def castWindowRecord {N L : ℕ} (h : N=L) (d : DimEmbedding X N)
    (J : MarkedIdeal N (CMfd.of (n := N) d.ambient)) :
    MarkedIdeal L (CMfd.of (n := L) (d.cast h).ambient) := by cases h;exact J

/-- Ordinary anchored minimal inputs DERIVE matching dimension/profile
and the actual independent product state; none is a caller packet. -/
theorem exists_independent_native_product_data {f : X ⟶ Y} {x : X.obj.left}
    {e : LocalEmbedding Y} {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
    (Q : MarkedIdeal w.target.dim (CMfd.of (n := w.target.dim) w.target.ambient))
    {H : ℕ → ℕ} (hState : NativeHSState Q w.target.carrier H) (hE : Q.E=[])
    (hBase : originalStalkHS Y (f.hom.left.base x)=H) (he : e.dim=H 1-1)
    {N : ℕ} (d : DimEmbedding X N) (c : d.carrier) (hc : d.toLocalEmbedding.toPoint c=x)
    (J : MarkedIdeal N (CMfd.of (n := N) d.ambient))
    {Hs : ℕ → ℕ} (hJ : IsInvDomain N J) (hJE : J.E=[])
    (hJState : NativeHSState J d.carrier Hs) (hJc : c.val∈J.cosupp) (hd : N=Hs 1-1) :
    ∃ hDim : N=e.dim+w.rank,
      ∃ M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open
        w.sourcePoint (d.cast hDim) (castWindowPoint hDim d c),
        IsInvDomain (e.dim+w.rank) (ProductRecordModel.rawRecord M (castWindowRecord hDim d J)) ∧
        (ProductRecordModel.rawRecord M (castWindowRecord hDim d J)).E=[] ∧
        NativeHSState (ProductRecordModel.rawRecord M (castWindowRecord hDim d J))
          (windowCarrier w.target w.rank (ProductRecordModel.rawOpen M)) (finiteProductHS w.rank H) := by
  have hSource : originalStalkHS X x=Hs:=by
    have hCut:=(Set.ext_iff.mp hJState.cosupp_eq c.val).mp hJc
    funext l
    have hAt:=originalStalkHS_localEmbedding_eq X d.toLocalEmbedding c l
    rw [hc] at hAt
    exact hAt.trans (hCut l)
  have hProd:=given_target_source_profile w Q hState hE hBase
  have hDimProd:=given_target_source_minimal_dimension w Q hState hE hBase he
  rw [hSource] at hDimProd
  have hDim : N=e.dim+w.rank:=hd.trans hDimProd.symm
  clear hd
  subst N
  refine ⟨rfl,?_⟩
  have hPoint : w.sourceMap.hom.left.base w.sourcePoint=d.toLocalEmbedding.toPoint c:=w.point.trans hc.symm
  obtain ⟨M,hD,hEmpty,hNative⟩:=exists_selected_product_state w.target w.rank w.window
    w.sourceMap w.source_open w.sourcePoint d c hPoint J hJ hJE hJState
  have hProfile : Hs=finiteProductHS w.rank H:=hSource.symm.trans hProd
  rw [hProfile] at hNative
  exact ⟨M,hD,hEmpty,hNative⟩

section Output
variable {f : X ⟶ Y} {x : X.obj.left} {e : LocalEmbedding Y} {V : Opens X.obj.left}
  (w : GivenTargetWindow f x e V) {d : DimEmbedding X (e.dim+w.rank)} {c : d.carrier}
  (M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint d c)

def ownRestrictedRecord (J : MarkedIdeal (e.dim+w.rank) (CMfd.of (n := e.dim+w.rank) d.ambient)) :
    MarkedIdeal (w.target.dim+w.rank) (CMfd.of (n := w.target.dim+w.rank) M.targetOpen) :=
  MarkedIdeal.pullback (Opens.inclusion M.target_subset) J

def ownRawEquiv : (ProductRecordModel.rawOpen M) ≃ₘ⟮𝓘(ℂ,ComplexModel (w.target.dim+w.rank)),
    𝓘(ℂ,ComplexModel (w.target.dim+w.rank))⟯ M.targetOpen :=
  (ProductRecordModel.rawDiffeomorph M).symm.trans M.phi

def ownBaseMap : M.targetOpen → e.ambient :=
  targetInclusion e w.targetOpen w.targetOpen_subset ∘
    (windowProjection (CMfd.of (n := w.target.dim) w.target.ambient) w.rank
      (ProductRecordModel.rawOpen M) ∘ (ownRawEquiv w M).symm)

private theorem raw_record_equiv
    (J : MarkedIdeal (e.dim+w.rank) (CMfd.of (n := e.dim+w.rank) d.ambient))
    (hJ : J.ideal.IsCoherent) :
    ProductRecordModel.rawRecord M J=MarkedIdeal.pullback (ownRawEquiv w M) (ownRestrictedRecord w M J) := by
  have hCoherent : (ownRestrictedRecord w M J).ideal.IsCoherent:=
    GermIdealPullbackCalculus.isCoherent_pullback (contMDiff_inclusion M.target_subset) hJ
  change MarkedIdeal.pullback (ProductRecordModel.rawDiffeomorph M).symm
    (MarkedIdeal.pullback M.phi (ownRestrictedRecord w M J))=_
  exact (whole_markedPullback_comp M.phi.contMDiff
    (ProductRecordModel.rawDiffeomorph M).symm.contMDiff (ownRestrictedRecord w M J) hCoherent).symm

private theorem inverse_raw_record
    (J : MarkedIdeal (e.dim+w.rank) (CMfd.of (n := e.dim+w.rank) d.ambient))
    (hJ : IsInvDomain (e.dim+w.rank) J) :
    MarkedIdeal.pullback (ownRawEquiv w M).symm (ProductRecordModel.rawRecord M J)=ownRestrictedRecord w M J := by
  have hCoherent : (ownRestrictedRecord w M J).ideal.IsCoherent:=
    GermIdealPullbackCalculus.isCoherent_pullback (contMDiff_inclusion M.target_subset) hJ.isWellFormed.isCoherent
  rw [raw_record_equiv w M J hJ.isWellFormed.isCoherent]
  change markedPullback (ownRawEquiv w M).symm
    (markedPullback (ownRawEquiv w M) (ownRestrictedRecord w M J))=_
  rw [←whole_markedPullback_comp (ownRawEquiv w M).contMDiff
    (ownRawEquiv w M).symm.contMDiff (ownRestrictedRecord w M J) hCoherent]
  have he : (ownRawEquiv w M) ∘ (ownRawEquiv w M).symm=id:=
    funext (ownRawEquiv w M).apply_symm_apply
  rw [he]
  exact ContactCanonicalAlong.pullback_id _ hCoherent

/-- Actual OUTPUT history, retaining the independently selected source
record. The public producer constructs every field from ordinary inputs. -/
structure IndependentCanonicalHistory
    (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient))
    (J : MarkedIdeal (e.dim+w.rank) (CMfd.of (n := e.dim+w.rank) d.ambient))
    {D : CMfd.{0} e.dim} (T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D) where
  endpoint : CMfd.{0} (w.target.dim+w.rank)
  tower : BlowupTower (CMfd.of (n := w.target.dim+w.rank) M.targetOpen) endpoint
  lift : endpoint → D
  cartesian : IsActualTowerPullback (ownBaseMap w M) tower T lift
  domain : IsInvDomain (w.target.dim+w.rank) (ownRestrictedRecord w M J)
  canonical : IsCanonical (ownRestrictedRecord w M J)
    ((canonicalInvariant (w.target.dim+w.rank)).inv (ownRestrictedRecord w M J)) tower
  cosupp : (geoTransformAlong (ownRestrictedRecord w M J) tower).cosupp=
    lift ⁻¹' (geoTransformAlong Q T).cosupp
  normalized_value : ∀z,lift z∈(geoTransformAlong Q T).cosupp →
    (canonicalInvariant (w.target.dim+w.rank)).inv (HironakaActualPowerBoundaryExponents.powerMarked
      (ownRestrictedRecord w M J) Q.d) tower z=
      ambientDimensionMap (Nat.le_add_right e.dim w.rank)
        ((canonicalInvariant e.dim).inv (HironakaActualPowerBoundaryExponents.powerMarked Q J.d) T (lift z))
  visible_maximum : lift ⁻¹' ResolutionDriver.maxLocus ((canonicalInvariant e.dim).inv Q T)
      (geoTransformAlong Q T).cosupp=∅ ∨
    lift ⁻¹' ResolutionDriver.maxLocus ((canonicalInvariant e.dim).inv Q T)
      (geoTransformAlong Q T).cosupp=ResolutionDriver.maxLocus
        ((canonicalInvariant (w.target.dim+w.rank)).inv (ownRestrictedRecord w M J) tower)
        (geoTransformAlong (ownRestrictedRecord w M J) tower).cosupp

end Output

private theorem matching_history {f : X ⟶ Y} {x : X.obj.left}
    {e : LocalEmbedding Y} {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
    (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient))
    (hQ : IsInvDomain e.dim Q) (hE : Q.E=[]) {H : ℕ → ℕ} (hState : NativeHSState Q e.carrier H)
    {D : CMfd.{0} e.dim} (T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D)
    (hCan : IsCanonical Q ((canonicalInvariant e.dim).inv Q) T)
    {d : DimEmbedding X (e.dim+w.rank)} {c : d.carrier}
    (J : MarkedIdeal (e.dim+w.rank) (CMfd.of (n := e.dim+w.rank) d.ambient))
    (hJ : IsInvDomain (e.dim+w.rank) J)
    (M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint d c)
    (hRawD : IsInvDomain (e.dim+w.rank) (ProductRecordModel.rawRecord M J))
    (hRawE : (ProductRecordModel.rawRecord M J).E=[])
    (hRawState : NativeHSState (ProductRecordModel.rawRecord M J)
      (windowCarrier w.target w.rank (ProductRecordModel.rawOpen M)) (finiteProductHS w.rank H)) :
    Nonempty (IndependentCanonicalHistory w M Q J T) := by
  let Q0 : MarkedIdeal w.target.dim (CMfd.of (n := w.target.dim) w.target.ambient):=
    targetRecord e Q w.targetOpen w.targetOpen_subset
  obtain ⟨D0,T0,g0,h0,hQ0,hE0,hState0,hCan0⟩:=target_native_restriction e Q hQ hE hState
    w.targetOpen w.targetOpen_subset T hCan
  change IsInvDomain w.target.dim Q0 at hQ0
  change Q0.E=[] at hE0
  change NativeHSState Q0 w.target.carrier H at hState0
  change IsCanonical Q0 ((canonicalInvariant w.target.dim).inv Q0) T0 at hCan0
  let rawJ:=ProductRecordModel.rawRecord M J
  let O:=ProductRecordModel.rawOpen M
  let p:=windowProjection (CMfd.of (n := w.target.dim) w.target.ambient) w.rank O
  obtain ⟨E,S,g,hS,hLen,hProj,hUniv,hRawCan,hRawCos,hPulled,hNorm,hMaxRaw⟩:=
    exists_window_native_canonical_history Q0 hQ0 hE0 hState0 O rawJ hRawD hRawE hRawState T0 hCan0
  let Ψ:=ownRawEquiv w M
  let A:=transport (X' := CMfd.of (n := w.target.dim+w.rank) M.targetOpen) Ψ.symm S
  have hIso:=transport_isTowerIso (X' := CMfd.of (n := w.target.dim+w.rank) M.targetOpen) Ψ.symm S
  have hInverse:=inverse_raw_record w M J hJ
  have hOwnD:=InvDomainTowerAlong.isInvDomain_pullback Ψ.symm hRawD
  rw [hInverse] at hOwnD
  have hOwnCan:=Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
    (X' := CMfd.of (n := w.target.dim+w.rank) M.targetOpen)
    (canonicalInvariant (w.target.dim+w.rank)) hRawD Ψ.symm hIso hRawCan
  rw [hInverse] at hOwnCan
  have hRawTest:=(canonicalInvariant (w.target.dim+w.rank)).isInvValue.isGeoTestTower_of_isCanonical
    hRawD S hRawCan
  have hT:=(canonicalInvariant e.dim).isInvValue.isGeoTestTower_of_isCanonical hQ T hCan
  have hT0:=(canonicalInvariant w.target.dim).isInvValue.isGeoTestTower_of_isCanonical hQ0 T0 hCan0
  have hOwnCos0:=IsTowerIso.cosupp_geoTransformAlong
    (X' := CMfd.of (n := w.target.dim+w.rank) M.targetOpen) Ψ.symm
    hRawD.isWellFormed.isClosedSubmanifold_N hRawD.isWellFormed.isCoherent hIso hRawTest
  rw [hInverse] at hOwnCos0
  have hQ0Cos : (geoTransformAlong Q0 T0).cosupp=g0 ⁻¹' (geoTransformAlong Q T).cosupp:=
    HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary h0 Q hQ.isWellFormed hT
  have hComp:=HironakaSmoothSubmersionCartesianTowerComposition.IsActualTowerPullback.comp h0 hS
  have hCart : IsActualTowerPullback (ownBaseMap w M) A.tower T ((g0 ∘ g) ∘ A.back):=
    HironakaOriginalSourceChoiceCartesian.IsActualTowerPullback.source_isomorphism hComp hIso
  have hCos : (geoTransformAlong (ownRestrictedRecord w M J) A.tower).cosupp=
      ((g0 ∘ g) ∘ A.back) ⁻¹' (geoTransformAlong Q T).cosupp:=by
    rw [hOwnCos0,hRawCos,hQ0Cos]
    rfl
  have hValue : ∀z,((g0 ∘ g) ∘ A.back) z∈(geoTransformAlong Q T).cosupp →
      (canonicalInvariant (w.target.dim+w.rank)).inv (powerMarked (ownRestrictedRecord w M J) Q.d) A.tower z=
        ambientDimensionMap (Nat.le_add_right e.dim w.rank)
          ((canonicalInvariant e.dim).inv (powerMarked Q J.d) T (((g0 ∘ g) ∘ A.back) z)):=by
    intro z hz
    have hz0 : g (A.back z)∈(geoTransformAlong Q0 T0).cosupp:=by
      rw [hQ0Cos]
      exact hz
    have hzRaw : A.back z∈(geoTransformAlong rawJ S).cosupp:=by
      rw [hRawCos]
      exact hz0
    have hQPow:=powerMarked_isInvDomain Q hQ hJ.one_le_d
    have hQPowCan:=(canonicalInvariant_isCanonical_power_iff Q hQ J.d hJ.one_le_d T).mp hCan
    have hQPowerCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hJ.one_le_d).wEquiv.2 T).2 hT
    have hzQPow : ((g0 ∘ g) ∘ A.back) z∈(geoTransformAlong (powerMarked Q J.d) T).cosupp:=hQPowerCos ▸ hz
    have hQ0Pow:=powerMarked_isInvDomain Q0 hQ0 hJ.one_le_d
    have hQ0PowCan:=(canonicalInvariant_isCanonical_power_iff Q0 hQ0 J.d hJ.one_le_d T0).mp hCan0
    have hQ0PowerCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl Q0 hQ0 hJ.one_le_d).wEquiv.2 T0).2 hT0
    have hz0Pow : g (A.back z)∈(geoTransformAlong (powerMarked Q0 J.d) T0).cosupp:=hQ0PowerCos ▸ hz0
    have hRawPow:=powerMarked_isInvDomain rawJ hRawD hQ.one_le_d
    have hRawPowCan:=(canonicalInvariant_isCanonical_power_iff rawJ hRawD Q.d hQ.one_le_d S).mp hRawCan
    have hRawPowCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl rawJ hRawD hQ.one_le_d).wEquiv.2 S).2 hRawTest
    have hzRawPow : A.back z∈(geoTransformAlong (powerMarked rawJ Q.d) S).cosupp:=hRawPowCos ▸ hzRaw
    have hIsoValue:=(canonicalInvariant (w.target.dim+w.rank)).isInvValue.towerIso Ψ.symm
      (powerMarked rawJ Q.d) hRawPow A.tower S A.back hIso hRawPowCan z hzRawPow
    have hInvPow : MarkedIdeal.pullback Ψ.symm (powerMarked rawJ Q.d)=
        powerMarked (ownRestrictedRecord w M J) Q.d:=by
      exact (HironakaG11PresClassTransport.pullback_powerMarked
        (M := CMfd.of (n := w.target.dim+w.rank) O)
        (M' := CMfd.of (n := w.target.dim+w.rank) M.targetOpen)
        Ψ.symm.contMDiff rawJ hRawD.isWellFormed.isCoherent Q.d).trans
          (congrArg (fun K => powerMarked K Q.d) hInverse)
    rw [hInvPow] at hIsoValue
    have hSmoothS:=HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_value
      hS (powerMarked Q0 J.d) hQ0Pow hQ0PowCan (A.back z) hz0Pow
    have hSmoothOriginal:=HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_value
      hComp (powerMarked Q J.d) hQPow hQPowCan (A.back z) hzQPow
    have hTargetPow : markedPullback (m := e.dim)
        (Y := CMfd.of (n := e.dim) w.targetOpen) (targetInclusion e w.targetOpen w.targetOpen_subset) (powerMarked Q J.d)=
        powerMarked Q0 J.d:=by
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · rfl
      · rfl
      · exact pullback_idealPow (target_inclusion_submersion e w.targetOpen w.targetOpen_subset).contMDiff
          hQ.isWellFormed.isCoherent J.d
      · rfl
    have hWhole : markedPullback (m := w.target.dim+w.rank)
        ((targetInclusion e w.targetOpen w.targetOpen_subset) ∘ p) (powerMarked Q J.d)=
        markedPullback (m := w.target.dim+w.rank) p (powerMarked Q0 J.d):=by
      rw [whole_markedPullback_comp
        (target_inclusion_submersion e w.targetOpen w.targetOpen_subset).contMDiff
        (window_isSubmersion (CMfd.of (n := w.target.dim) w.target.ambient) w.rank O).contMDiff
        (powerMarked Q J.d) hQPow.isWellFormed.isCoherent,hTargetPow]
    rw [hWhole] at hSmoothOriginal
    have hProductValue:=hNorm (A.back z) hz0
    exact hIsoValue.trans ((hProductValue.trans hSmoothS.symm).trans hSmoothOriginal)
  have hOwnTest:=(canonicalInvariant (w.target.dim+w.rank)).isInvValue.isGeoTestTower_of_isCanonical
    hOwnD A.tower hOwnCan
  have hQPowerCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hJ.one_le_d).wEquiv.2 T).2 hT
  have hOwnPowerCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl (ownRestrictedRecord w M J) hOwnD
    hQ.one_le_d).wEquiv.2 A.tower).2 hOwnTest
  have hNormCos : (geoTransformAlong (powerMarked (ownRestrictedRecord w M J) Q.d) A.tower).cosupp=
      ((g0 ∘ g) ∘ A.back) ⁻¹' (geoTransformAlong (powerMarked Q J.d) T).cosupp:=by
    rw [←hQPowerCos,←hOwnPowerCos]
    exact hCos
  have hMax:=MaxLocusLocal.preimage_maxLocus_eq_or_of_eq
    (f := ambientDimensionMap (Nat.le_add_right e.dim w.rank) ∘ (canonicalInvariant e.dim).inv (powerMarked Q J.d) T)
    (g := (canonicalInvariant (w.target.dim+w.rank)).inv (powerMarked (ownRestrictedRecord w M J) Q.d) A.tower)
    (s := (geoTransformAlong (powerMarked Q J.d) T).cosupp) ((g0 ∘ g) ∘ A.back) (by
      intro z hz
      exact (hValue z (hQPowerCos.symm ▸ hz)).symm)
  rw [MaxLocusLocal.maxLocus_comp_strictMono (strictMono_ambientDimensionMap (Nat.le_add_right e.dim w.rank)),
    ←hNormCos,←canonicalInvariant_maxLocus_power Q hQ J.d hJ.one_le_d T hCan,
    ←canonicalInvariant_maxLocus_power (ownRestrictedRecord w M J) hOwnD Q.d hQ.one_le_d A.tower hOwnCan] at hMax
  exact ⟨⟨A.target,A.tower,((g0 ∘ g) ∘ A.back),hCart,hOwnD,hOwnCan,hCos,hValue,hMax⟩⟩

/-- Ordinary smoothness, ACTUAL anchored independent minimal native inputs,
and a GIVEN target CAN tower construct the entire own-source history. -/
theorem exists_independent_native_smooth_canonical_history
    (f : X ⟶ Y) (x : X.obj.left) (hsm : OriginalNativeSmoothLocalProduct.IsSmoothAt f x)
    (e : LocalEmbedding Y) (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient))
    (hQ : IsInvDomain e.dim Q) (hE : Q.E=[]) {H : ℕ → ℕ} (hState : NativeHSState Q e.carrier H)
    (he : e.dim=H 1-1) (a : e.carrier) (ha : e.toPoint a=f.hom.left.base x) (haQ : a.val∈Q.cosupp)
    (V : Opens X.obj.left) (hxV : x∈V)
    {N : ℕ} (d : DimEmbedding X N) (c : d.carrier) (hc : d.toLocalEmbedding.toPoint c=x)
    (J : MarkedIdeal N (CMfd.of (n := N) d.ambient))
    {Hs : ℕ → ℕ} (hJ : IsInvDomain N J) (hJE : J.E=[])
    (hJState : NativeHSState J d.carrier Hs) (hJc : c.val∈J.cosupp) (hd : N=Hs 1-1)
    {D : CMfd.{0} e.dim} (T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D)
    (hCan : IsCanonical Q ((canonicalInvariant e.dim).inv Q) T) :
    ∃ w : GivenTargetWindow f x e V,∃ hDim : N=e.dim+w.rank,
      ∃ M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint
          (d.cast hDim) (castWindowPoint hDim d c),
        Nonempty (IndependentCanonicalHistory w M Q (castWindowRecord hDim d J) T) ∧
        (ProductRecordModel.rawIso M).hom ≫
            chartInclusion ((d.cast hDim).toLocalEmbedding.restrict M.targetOpen M.target_subset)=
          refinement w.target w.rank (ProductRecordModel.rawOpen_subset M) ≫ w.sourceMap ∧
        (ProductRecordModel.rawIso M).hom.hom.left ≫
            (chartSpace ((d.cast hDim).toLocalEmbedding.restrict M.targetOpen M.target_subset)).obj.hom=
          (windowSpace w.target w.rank (ProductRecordModel.rawOpen M)).obj.hom ∧
        (refinement w.target w.rank (ProductRecordModel.rawOpen_subset M) ≫ w.sourceMap).hom.left.base
            (ProductRecordModel.rawPoint M)=x := by
  have hRange : f.hom.left.base x∈range e.toPoint:=⟨a,ha⟩
  obtain ⟨w⟩:=exists_given_target_window f x hsm e hRange V hxV
  let Q0 : MarkedIdeal w.target.dim (CMfd.of (n := w.target.dim) w.target.ambient):=
    targetRecord e Q w.targetOpen w.targetOpen_subset
  obtain ⟨hQ0,hE0,hState0⟩:=target_initial_native_data e Q hQ hE hState
    w.targetOpen w.targetOpen_subset
  change NativeHSState Q0 w.target.carrier H at hState0
  change Q0.E=[] at hE0
  have hBase : originalStalkHS Y (f.hom.left.base x)=H:=by
    have hCut:=(Set.ext_iff.mp hState.cosupp_eq a.val).mp haQ
    funext l
    have hAt:=originalStalkHS_localEmbedding_eq Y e a l
    rw [ha] at hAt
    exact hAt.trans (hCut l)
  obtain ⟨hDim,M,hRawD,hRawE,hRawState⟩:=exists_independent_native_product_data
    w Q0 hState0 hE0 hBase he d c hc J hJ hJE hJState hJc hd
  have hCastD : IsInvDomain (e.dim+w.rank) (castWindowRecord hDim d J):=by
    cases hDim
    exact hJ
  have hHistory:=matching_history w Q hQ hE hState T hCan
    (castWindowRecord hDim d J) hCastD M hRawD hRawE hRawState
  refine ⟨w,hDim,M,hHistory,ProductRecordModel.raw_native_square M,?_,?_⟩
  · exact Over.w (ProductRecordModel.rawIso M).hom.hom
  · change w.sourceMap.hom.left.base
      ((refinement w.target w.rank (ProductRecordModel.rawOpen_subset M)).hom.left.base
        (ProductRecordModel.rawPoint M))=x
    rw [ProductRecordModel.rawPoint_refinement,w.point]

namespace IndependentCanonicalHistory
variable {f : X ⟶ Y} {x : X.obj.left} {e : LocalEmbedding Y} {V : Opens X.obj.left}
  {w : GivenTargetWindow f x e V} {d : DimEmbedding X (e.dim+w.rank)} {c : d.carrier}
  {M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint d c}
  {Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient)}
  {J : MarkedIdeal (e.dim+w.rank) (CMfd.of (n := e.dim+w.rank) d.ambient)}
  {D : CMfd.{0} e.dim} {T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D}
  (A : IndependentCanonicalHistory w M Q J T)

theorem same_length : A.tower.length=T.length:=A.cartesian.length_eq

theorem original_projection_square : ∀z,T.proj (A.lift z)=ownBaseMap w M (A.tower.proj z):=
  A.cartesian.proj_comm

theorem full_universal_square : HironakaSmoothSubmersionOrderedChoiceBaseChange.HolomorphicSquarePullback
    (ownBaseMap w M) A.lift A.tower.proj T.proj:=A.cartesian.universal

/-- WHOLE identity is for the LITERAL pulled Q, never for independent J. -/
theorem whole_pulled_record (hQ : IsInvDomain e.dim Q)
    (hCan : IsCanonical Q ((canonicalInvariant e.dim).inv Q) T) :
    geoTransformAlong (markedPullback (ownBaseMap w M) Q) A.tower=
      markedPullback A.lift (geoTransformAlong Q T) :=
  (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    A.cartesian Q hQ.isWellFormed
    ((canonicalInvariant e.dim).isInvValue.isGeoTestTower_of_isCanonical hQ T hCan)).2

end IndependentCanonicalHistory

end
end Hironaka.Analytic.Unibranch.HironakaG1IndependentNativeSmoothCanonicalHistory
