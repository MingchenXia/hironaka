import Hironaka.Analytic.Unibranch.OriginalNativeCurrentThresholdCorrespondence
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseGluing

/-! Actual terminal phase arrow over the same past smooth context. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeCurrentTerminalSmoothPhaseMap
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaHolomorphicJetChartInvariance
  HironakaG11VanishingWindows HironakaG11PresWindows HironakaG11PresReduction HironakaG11PresLineState
  HironakaG11PresTowerState HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal CanonicalCentres HironakaActualPowerBoundaryExponents
  ResolutionInvariantSpec OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  OriginalNativeSmoothOpenLocality OriginalNativeSmoothTerminalWindowSpan
  OriginalNativeSmoothBarrierThreshold HironakaG10GenDisjointModification HironakaG1NativeFiniteProductState
  OriginalNativeSmoothProductPhaseSpans OriginalNativeSmoothSingularLocus
  OriginalNativeHSShadowOuterState OriginalNativeHSCurrentSmoothContext
  OriginalNativeCurrentThresholdCorrespondence
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a0 : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a0.hom.left} {hChart : a0 ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a0 ha hChart S T)

abbrev CurrentSource := OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange
abbrev CurrentTarget := OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen c.targetCompactClosure c.targetRange

variable (H : ℕ→ℕ)
  {Ns Nt : ℕ} {κ ι : Type}
  (wS : κ→DimEmbedding (CurrentSource c) Ns) (wT : ι→DimEmbedding (CurrentTarget c) Nt)
  (rawS : ∀j,MarkedIdeal Ns (Amb wS j)) (rawT : ∀i,MarkedIdeal Nt (Amb wT i))
  (hrecS : ∀j,IsNativeWindowRecord (wS j) (rawS j) (finiteProductHS r H))
  (hrecT : ∀i,IsNativeWindowRecord (wT i) (rawT i) H)
  (hNs : Ns=(finiteProductHS r H) 1-1) (hNt : Nt=H 1-1)
  (pS : κ→ℕ) (pT : ι→ℕ) (hpS : ∀j,1≤pS j) (hpT : ∀i,1≤pT i)
  (TS : Towers wS) (TT : Towers wT) (xs : XStage wS TS) (xt : XStage wT TT)
  (hcS : ∀j,IsCanonical (powerMarked (rawS j) (pS j))
    ((canonicalInvariant Ns).inv (powerMarked (rawS j) (pS j))) (TS j).2)
  (hcT : ∀i,IsCanonical (powerMarked (rawT i) (pT i))
    ((canonicalInvariant Nt).inv (powerMarked (rawT i) (pT i))) (TT i).2)
  (hrS : ∀j,IsGeoResolution (powerMarked (rawS j) (pS j)) (TS j).2)
  (hrT : ∀i,IsGeoResolution (powerMarked (rawT i) (pT i)) (TT i).2)
  (hCoverS : originalSingularHSThreshold (CurrentSource c) (finiteProductHS r H) ⊆
    ⋃j,range (wS j).toLocalEmbedding.toPoint)
  (hCoverT : originalSingularHSThreshold (CurrentTarget c) H ⊆ ⋃i,range (wT i).toLocalEmbedding.toPoint)
  (hOffS : IsIsoOver xs.q (originalSingularHSThreshold (CurrentSource c) (finiteProductHS r H))ᶜ)
  (hOffT : IsIsoOver xt.q (originalSingularHSThreshold (CurrentTarget c) H)ᶜ)

include hrecS hrecT hNs hNt hpS hpT hcS hcT hrS hrT hCoverS hCoverT hOffS hOffT in
/-- Actual native terminal histories give smooth spans around each endpoint point. -/
theorem exists_local_smooth_span (y : xs.Y.obj.left) :
    ∃ (N : SourceReducedComplexSpace) (a : N⟶xs.Y) (b : N⟶xt.Y),
      LocallyRingedSpace.IsOpenImmersion a.hom.left ∧ IsSmoothMorphism b ∧
      y∈range a.hom.left.base ∧ b≫xt.q=a≫xs.q≫c.map := by
  have hThreshold := threshold_preimage_of_source_phase_records c H wS rawS hrecS hCoverS
  by_cases hy : xs.q.hom.left.base y ∈ originalSingularHSThreshold (CurrentSource c) (finiteProductHS r H)
  · have ht : c.map.hom.left.base (xs.q.hom.left.base y) ∈ originalSingularHSThreshold (CurrentTarget c) H :=
      (Set.ext_iff.mp hThreshold _).mpr hy
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hCoverS hy)
    have hyRange : y∈range (xs.map j).hom.left.base := by
      rw [xs.range_map j]
      exact hj
    obtain ⟨q,rfl⟩ := hyRange
    obtain ⟨i,t,htPoint⟩ := Set.mem_iUnion.mp (hCoverT ht)
    let q0 : (wS j).carrier := ⟨(TS j).2.proj q.val,xs.proj_mem j q⟩
    have hq0 : (wS j).toLocalEmbedding.toPoint q0=xs.q.hom.left.base ((xs.map j).hom.left.base q) :=
      (xs.square j q (xs.proj_mem j q)).symm
    have hJanchor := raw_anchor_of_threshold (wS j) (rawS j) (hrecS j) q0 (hq0.symm ▸ hy)
    have hQanchor := raw_anchor_of_threshold (wT i) (rawT i) (hrecT i) t (htPoint.symm ▸ ht)
    exact exists_local_smooth_span_at c.map c.smooth xs xt j i (rawS j) (rawT i) (hrecS j) (hrecT i)
      hNs hNt (pS j) (pT i) (hpS j) (hpT i) (hcS j) (hrS j) (hcT i) (hrT i) q t hJanchor hQanchor htPoint
  · have hOpen : IsOpen (originalSingularHSThreshold (CurrentSource c) (finiteProductHS r H))ᶜ :=
      (original_hs_threshold_dictionary (CurrentSource c) (finiteProductHS r H)).2.1.isClosed.isOpen_compl
    obtain ⟨d,⟨q,hq⟩,hd,_⟩ := LocalEmbedding.exists_domain (xs.q.hom.left.base y) hOpen hy
    obtain ⟨a,ha,hOpenA,hRangeA⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift hOffS (chartInclusion d) hd
    let F := chartInclusion d≫c.map
    have hRangeF : range F.hom.left.base⊆(originalSingularHSThreshold (CurrentTarget c) H)ᶜ := by
      rintro _ ⟨z,rfl⟩
      have h := hd ⟨z,rfl⟩
      intro ht
      exact h ((Set.ext_iff.mp hThreshold _).mp ht)
    obtain ⟨b,hb,_,_⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift hOffT F hRangeF
    have hSmoothF : IsSmoothMorphism F := isSmoothMorphism_comp _ _
      (isSmoothMorphism_of_isOpenImmersion _ d.isOpenImmersion) c.smooth
    refine ⟨chartSpace d,a,b,hOpenA d.isOpenImmersion,
      isSmoothMorphism_lift_of_isIsoOver xt.q hOffT F hRangeF hSmoothF b hb,?_,?_⟩
    · rw [hRangeA]
      exact ⟨q,hq⟩
    · exact hb.trans (congrArg (fun k=>k≫c.map) ha.symm)

private theorem maps_eq (a b : xs.Y⟶xt.Y)
    (ha : a≫xt.q=xs.q≫c.map) (hb : b≫xt.q=xs.q≫c.map) : a=b := by
  apply morphism_eq_of_pointwise_eq
  intro z
  have hbase : ∀u,xt.q.hom.left.base (a.hom.left.base u)=xt.q.hom.left.base (b.hom.left.base u) :=
    fun u=>(congrArg (fun k : xs.Y⟶CurrentTarget c=>k.hom.left.base u) ha).trans
      (congrArg (fun k : xs.Y⟶CurrentTarget c=>k.hom.left.base u) hb).symm
  have hGood : ∀u∈xs.q.hom.left.base ⁻¹' intrinsicRegularLocus (CurrentSource c).obj,
      xt.q.hom.left.base (a.hom.left.base u)∈intrinsicRegularLocus (CurrentTarget c).obj := by
    intro u hu
    have hpoint:=congrArg (fun k : xs.Y⟶CurrentTarget c=>k.hom.left.base u) ha
    change xt.q.hom.left.base (a.hom.left.base u)=
      (c.map).hom.left.base (xs.q.hom.left.base u) at hpoint
    rw [hpoint]
    exact (smoothAt_regular_iff (c.map) _ (c.smooth _)).mp hu
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    xt.isSingularCentreModification.isIsoOver_intrinsicRegularLocus
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hbase
    xs.isSingularCentreModification.dense_preimage_intrinsicRegularLocus hGood) z

include hrecS hrecT hNs hNt hpS hpT hcS hcT hrS hrT hCoverS hCoverT hOffS hOffT in
/-- Ordinary INITIAL covers and TWO actual terminal histories construct the
unique full smooth phase arrow on the same actual current context. -/
theorem exists_unique_phase_map :
    ∃! g : xs.Y⟶xt.Y, IsSmoothMorphism g ∧ g≫xt.q=xs.q≫c.map := by
  classical
  choose N a b ha hb hrange hproj using exists_local_smooth_span c H
    wS wT rawS rawT hrecS hrecT hNs hNt pS pT hpS hpT TS TT xs xt hcS hcT hrS hrT
    hCoverS hCoverT hOffS hOffT
  let V := fun y : xs.Y.obj.left=>(N y).obj.left
  let j := fun y : xs.Y.obj.left=>(a y).hom.left
  let : ∀y,LocallyRingedSpace.IsOpenImmersion (j y) := ha
  have hcover : ∀y : xs.Y.obj.left,∃(u : xs.Y.obj.left)(v : V u),(j u).base v=y := by
    intro y
    obtain ⟨v,hv⟩:=hrange y
    exact ⟨y,v,hv⟩
  have hp (y : xs.Y.obj.left) : (b y).hom.left≫xt.q.hom.left=
      j y≫xs.q.hom.left≫(c.map).hom.left :=
    congrArg (fun k : N y⟶CurrentTarget c=>k.hom.left) (hproj y)
  have hscalar (y : xs.Y.obj.left) : (b y).hom.left≫xt.Y.obj.hom=j y≫xs.Y.obj.hom :=
    (Over.w (b y).hom).trans (Over.w (a y).hom).symm
  have hcompat (y z : xs.Y.obj.left) :
      pullback.fst (j y) (j z)≫(b y).hom.left=pullback.snd (j y) (j z)≫(b z).hom.left := by
    let k := pullback.fst (j y) (j z)≫j y
    let F := pullback.fst (j y) (j z)≫(b y).hom.left
    let G := pullback.snd (j y) (j z)≫(b z).hom.left
    have hk : LocallyRingedSpace.IsOpenImmersion k := by dsimp only [k]; infer_instance
    let : LocallyRingedSpace.IsOpenImmersion k := hk
    have hF : F≫xt.q.hom.left=k≫xs.q.hom.left≫(c.map).hom.left := by
      dsimp only [F,k]
      rw [Category.assoc,hp y,Category.assoc]
    have hG : G≫xt.q.hom.left=k≫xs.q.hom.left≫(c.map).hom.left := by
      dsimp only [G,k]
      rw [Category.assoc,hp z,←Category.assoc,pullback.condition,Category.assoc]
    have hbase : ∀v,xt.q.hom.left.base (F.base v)=xt.q.hom.left.base (G.base v) :=
      fun v=>congrArg (fun l=>l.base v) (hF.trans hG.symm)
    let D := k.base ⁻¹' (xs.q.hom.left.base ⁻¹' intrinsicRegularLocus (CurrentSource c).obj)
    have hD : Dense D := xs.isSingularCentreModification.dense_preimage_intrinsicRegularLocus.preimage
      hk.base_open.isOpenMap
    have hGood : ∀v∈D,xt.q.hom.left.base (F.base v)∈intrinsicRegularLocus (CurrentTarget c).obj := by
      intro v hv
      have hpoint:=congrArg (fun l=>l.base v) hF
      change xt.q.hom.left.base (F.base v)=
        (c.map).hom.left.base (xs.q.hom.left.base (k.base v)) at hpoint
      rw [hpoint]
      exact (smoothAt_regular_iff (c.map) _ (c.smooth _)).mp hv
    have hpoints : F.base=G.base := by
      ext v
      exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
        xt.isSingularCentreModification.isIsoOver_intrinsicRegularLocus
        F.base.hom.continuous G.base.hom.continuous hbase hD hGood) v
    apply HironakaG10GenGluing.lrs_hom_eq_of_base_eq (A := xs.Y) (B := xt.Y) k F G
    · dsimp only [F,k]
      rw [Category.assoc,hscalar y,Category.assoc]
    · dsimp only [G,k]
      rw [Category.assoc,hscalar z,←Category.assoc,←pullback.condition,Category.assoc]
    · exact hpoints
  obtain ⟨g,hg,_⟩ := HironakaIntrinsicMorphismGluing.exists_unique_over V j hcover
    xs.Y.obj.hom xt.Y.obj.hom (fun y=>(b y).hom.left) hcompat hscalar
  let gNative : xs.Y⟶xt.Y := ObjectProperty.homMk g
  have hlocal (y : xs.Y.obj.left) : a y≫gNative=b y := by
    apply HironakaG10GenDisjointModification.hom_ext_left
    exact hg y
  have hfull : gNative≫xt.q=xs.q≫c.map := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change g.left≫xt.q.hom.left=xs.q.hom.left≫(c.map).hom.left
    apply HironakaIntrinsicMorphismGluing.hom_ext V j hcover
    intro y
    rw [←Category.assoc,hg y,hp y]
  have hsm : IsSmoothMorphism gNative := by
    intro y
    obtain ⟨v,hv⟩:=hrange y
    have hl : IsSmoothAt (a y≫gNative) v := (hlocal y).symm ▸ hb y v
    exact hv ▸ isSmoothAt_of_precomp_openImmersion (a y) gNative (ha y) v hl
  refine ⟨gNative,⟨hsm,hfull⟩,?_⟩
  intro g' hg'
  exact maps_eq c wS wT TS TT xs xt g' gNative hg'.2 hfull

end
end Hironaka.Analytic.Unibranch.OriginalNativeCurrentTerminalSmoothPhaseMap
