import Hironaka.Analytic.Unibranch.HironakaG1IndependentNativeSmoothCanonicalHistory
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothAmbientConverse
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalContactHistory

/-! Actual full native smooth lift on D34's SAME independently selected towers.
Blueprint FIRST: original-native-independent-strict-smooth-lift.tex.
No global surjectivity, independent-marked-ideal pullback or next endpoint packet. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeIndependentStrictSmoothLift
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaHolomorphicJetChartInvariance HironakaIntrinsicComplexAnalyticRegularLocus
  OriginalNativeProductWindow OriginalNativeProductIndependentRecord OriginalNativeProductSelectedState
  OriginalNativeSmoothGivenTargetWindow OriginalNativeSmoothAmbientConverse
  HironakaG1IndependentNativeSmoothCanonicalHistory HironakaG11VanishingWindows
  HironakaG11PresLineState HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOriginalContactHistory BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres ResolutionInvariantSpec
open HomogenizedGlueingTower (strictAlong)
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace} {f : X⟶Y} {x : X.obj.left}
  {e : LocalEmbedding Y} {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
  {d : DimEmbedding X (e.dim+w.rank)} {c : d.carrier}
  (M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint d c)
  {Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient)}
  {J : MarkedIdeal (e.dim+w.rank) (CMfd.of (n := e.dim+w.rank) d.ambient)}
  {D : CMfd.{0} e.dim} {T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D}

/-- EXACT independent initial carrier, internally obtained from the actual product frame. -/
theorem initial_carrier_preimage :
    M.targetCarrier=(ownBaseMap w M) ⁻¹' e.carrier := by
  ext q
  have hm:=M.carrier_eq (M.phi.symm q)
  rw [M.phi.apply_symm_apply] at hm
  have hr:=Set.ext_iff.mp (ProductRecordModel.rawCarrier_eq M)
    (ProductRecordModel.rawDiffeomorph M (M.phi.symm q))
  change (ProductRecordModel.rawDiffeomorph M).toEquiv.symm
    ((ProductRecordModel.rawDiffeomorph M).toEquiv (M.phi.symm q))∈M.sourceCarrier ↔ _ at hr
  rw [(ProductRecordModel.rawDiffeomorph M).toEquiv.symm_apply_apply] at hr
  exact hm.symm.trans hr

def sourceInitialSpace : SourceReducedComplexSpace :=
  chartSpace (d.toLocalEmbedding.restrict M.targetOpen M.target_subset)

variable (A : IndependentCanonicalHistory w M Q J T)

private theorem cartesian_base_submersion {n m : ℕ} {B D : CMfd.{0} n} {C E : CMfd.{0} m}
    {b : C→B} {g : E→D} {S : BlowupTower C E} {U : BlowupTower B D}
    (h : IsActualTowerPullback b S U g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b := by
  induction h with
  | refl hf=>exact hf
  | step _ _ _ _ ih=>exact ih

include A in
private theorem base_submersion :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (w.target.dim+w.rank))
      𝓘(ℂ,ComplexModel e.dim) ∞ (ownBaseMap w M) := by
  exact cartesian_base_submersion A.cartesian

def initialMap : sourceInitialSpace w M ⟶ chartSpace e :=
  subspaceMorphism (base_submersion w M A)
    (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic e.analytic
    (initial_carrier_preimage w M)

theorem initial_original_square :
    initialMap w M A ≫ chartInclusion e=
      chartInclusion (d.toLocalEmbedding.restrict M.targetOpen M.target_subset) ≫ f := by
  apply (cancel_epi (ProductRecordModel.rawIso M).hom).mp
  have hRaw : (ProductRecordModel.rawIso M).hom ≫ initialMap w M A ≫ chartInclusion e=
      refinement w.target w.rank (ProductRecordModel.rawOpen_subset M) ≫
        windowFirst w.target w.rank w.window := by
    apply morphism_eq_of_pointwise_eq
    intro p
    have hBase : ownBaseMap w M ((ProductRecordModel.rawIso M).hom.hom.left.base p).val=
        targetInclusion e w.targetOpen w.targetOpen_subset p.val.val.1 := by
      change targetInclusion e w.targetOpen w.targetOpen_subset
        (((ownRawEquiv w M).toEquiv.symm ((ownRawEquiv w M).toEquiv p.val)).val.1)=_
      rw [(ownRawEquiv w M).toEquiv.symm_apply_apply]
    let src := (ProductRecordModel.rawIso M).hom.hom.left.base p
    have hmem : ownBaseMap w M src.val ∈ e.carrier :=
      (Set.ext_iff.mp (initial_carrier_preimage w M) src.val).mp src.property
    let qL : e.carrier := ⟨ownBaseMap w M src.val,hmem⟩
    let qR : e.carrier :=
      ⟨targetInclusion e w.targetOpen w.targetOpen_subset p.val.val.1,p.property⟩
    have hq : qL=qR := Subtype.ext hBase
    change e.toPoint qL=w.target.toPoint ⟨p.val.val.1,p.property⟩
    exact (congrArg e.toPoint hq).trans
      (e.restrict_toPoint w.targetOpen w.targetOpen_subset ⟨p.val.val.1,p.property⟩).symm
  calc
    _=(ProductRecordModel.rawIso M).hom ≫ initialMap w M A ≫ chartInclusion e :=
      (Category.assoc _ _ _).symm
    _=refinement w.target w.rank (ProductRecordModel.rawOpen_subset M) ≫
        windowFirst w.target w.rank w.window := hRaw
    _=refinement w.target w.rank (ProductRecordModel.rawOpen_subset M) ≫ (w.sourceMap ≫ f) :=
      congrArg (fun k=>refinement w.target w.rank (ProductRecordModel.rawOpen_subset M) ≫ k) w.square.symm
    _=(refinement w.target w.rank (ProductRecordModel.rawOpen_subset M) ≫ w.sourceMap) ≫ f :=
      (Category.assoc _ _ _).symm
    _=((ProductRecordModel.rawIso M).hom ≫
        chartInclusion (d.toLocalEmbedding.restrict M.targetOpen M.target_subset)) ≫ f :=
      congrArg (fun k=>k ≫ f) (ProductRecordModel.raw_native_square M).symm
    _=_:=Category.assoc _ _ _

theorem strict_carrier_preimage :
    strictAlong A.tower M.targetCarrier=A.lift ⁻¹' strictAlong T e.carrier := by
  rw [initial_carrier_preimage w M]
  exact HironakaSmoothSubmersionOriginalContactHistory.IsActualTowerPullback.strictAlong_preimage
    A.cartesian e.carrier

variable (hQ : IsInvDomain e.dim Q) {H : ℕ→ℕ} (hState : NativeHSState Q e.carrier H)
  (hCan : IsCanonical Q ((canonicalInvariant e.dim).inv Q) T)

include hQ hState hCan in
private theorem target_analytic : IsComplexAnalyticSubset (n := e.dim) (strictAlong T e.carrier) :=
  (hState.hsTowerState T
    ((canonicalInvariant e.dim).isInvValue.isGeoTestTower_of_isCanonical hQ T hCan)).1

include hQ hState hCan in
private theorem source_analytic : IsComplexAnalyticSubset (n := w.target.dim+w.rank)
    (strictAlong A.tower M.targetCarrier) := by
  rw [strict_carrier_preimage w M A]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage A.cartesian.isSubmersion.contMDiff
    (target_analytic hQ hState hCan)

def targetStrictSpace : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictAlong T e.carrier) (target_analytic hQ hState hCan)

def sourceStrictSpace : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictAlong A.tower M.targetCarrier) (source_analytic w M A hQ hState hCan)

def nativeLift : sourceStrictSpace w M A hQ hState hCan ⟶ targetStrictSpace hQ hState hCan :=
  subspaceMorphism A.cartesian.isSubmersion (source_analytic w M A hQ hState hCan)
    (target_analytic hQ hState hCan) (strict_carrier_preimage w M A)

theorem nativeLift_isSmooth :
    OriginalNativeSmoothLocalProduct.IsSmoothMorphism (nativeLift w M A hQ hState hCan) :=
  isSmoothMorphism_subspaceMorphism A.cartesian.isSubmersion
    (source_analytic w M A hQ hState hCan) (target_analytic hQ hState hCan)
    (strict_carrier_preimage w M A)

theorem nativeLift_range : range (nativeLift w M A hQ hState hCan).hom.left.base=
    (Subtype.val : (targetStrictSpace hQ hState hCan).obj.left→D) ⁻¹' range A.lift := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p.val,rfl⟩
  · rintro ⟨p,hp⟩
    have hmem : p∈strictAlong A.tower M.targetCarrier := by
      rw [strict_carrier_preimage w M A]
      change A.lift p∈strictAlong T e.carrier
      rw [hp]
      exact q.property
    exact ⟨⟨p,hmem⟩,Subtype.ext hp⟩

theorem nativeLift_whole_ideal :
    GermIdeal.pullback (m := w.target.dim+w.rank) A.lift
      (vanishingIdeal (n := e.dim) (strictAlong T e.carrier))=
      vanishingIdeal (n := w.target.dim+w.rank) (strictAlong A.tower M.targetCarrier) :=
  subspace_whole_ideal A.cartesian.isSubmersion (strict_carrier_preimage w M A)

def sourceProjection : sourceStrictSpace w M A hQ hState hCan ⟶ sourceInitialSpace w M :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap A.tower.contMDiff_proj
      (MemberInterTowerAlong.strictAlong_subset_preimage A.tower
        (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic.isClosed))
    (actualSubspaceMap_point A.tower.contMDiff_proj
      (MemberInterTowerAlong.strictAlong_subset_preimage A.tower
        (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic.isClosed)))

def targetProjection : targetStrictSpace hQ hState hCan ⟶ chartSpace e :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap T.contMDiff_proj (MemberInterTowerAlong.strictAlong_subset_preimage T e.analytic.isClosed))
    (actualSubspaceMap_point T.contMDiff_proj
      (MemberInterTowerAlong.strictAlong_subset_preimage T e.analytic.isClosed)))

theorem native_projection_square :
    nativeLift w M A hQ hState hCan ≫ targetProjection hQ hState hCan=
      sourceProjection w M A hQ hState hCan ≫ initialMap w M A := by
  apply morphism_eq_of_pointwise_eq
  intro p
  apply Subtype.ext
  exact A.cartesian.proj_comm p.val

theorem original_square :
    nativeLift w M A hQ hState hCan ≫ targetProjection hQ hState hCan ≫ chartInclusion e=
      sourceProjection w M A hQ hState hCan ≫
        chartInclusion (d.toLocalEmbedding.restrict M.targetOpen M.target_subset) ≫ f := by
  rw [← Category.assoc,native_projection_square,Category.assoc,initial_original_square]

theorem native_scalar : (nativeLift w M A hQ hState hCan).hom.left ≫
    (targetStrictSpace hQ hState hCan).obj.hom=(sourceStrictSpace w M A hQ hState hCan).obj.hom :=
  Over.w (nativeLift w M A hQ hState hCan).hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeIndependentStrictSmoothLift
