import Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseSpans
import Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseGluing
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus

/-! Actual smooth native phase-arrow existence on ONE honest product chart.
Full Blueprint FIRST; ordinary initial data, not local-span packets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseGluing
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
open scoped ProductComplexManifold


open OriginalNativeSmoothProductPhaseSpans OriginalNativeSmoothSingularLocus

private theorem product_smooth {Y : SourceReducedComplexSpace}
    (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productAmbient e r)) :
    IsSmoothMorphism (windowFirst e r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e r→e.ambient) O (⊤ : Opens e.ambient) :=
    fun _ _=>mem_univ _
  have hp := isSmoothMorphism_comp (nativeProjection e r ⊤ O hWP) (targetInclusion e ⊤)
    (nativeProjection_isSmooth e r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e ⊤))
  exact (nativeProjection_square e r ⊤ O hWP) ▸ hp

variable {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) (r : ℕ)
  (O : Opens (productAmbient e r)) (H : ℕ→ℕ)
  (hBound : ∀ y∈intrinsicSingularLocus Y.obj,toLex (originalStalkHS Y y)≤toLex H)
  {Ns Nt : ℕ} {κ ι : Type}
  (wS : κ→DimEmbedding (windowSpace e r O) Ns) (wT : ι→DimEmbedding Y Nt)
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
  (hCoverS : originalSingularHSThreshold (windowSpace e r O) (finiteProductHS r H) ⊆
    ⋃j,range (wS j).toLocalEmbedding.toPoint)
  (hCoverT : originalSingularHSThreshold Y H ⊆ ⋃i,range (wT i).toLocalEmbedding.toPoint)
  (hOffS : IsIsoOver xs.q (originalSingularHSThreshold (windowSpace e r O) (finiteProductHS r H))ᶜ)
  (hOffT : IsIsoOver xt.q (originalSingularHSThreshold Y H)ᶜ)


private theorem maps_eq (a b : xs.Y⟶xt.Y)
    (ha : a≫xt.q=xs.q≫windowFirst e r O) (hb : b≫xt.q=xs.q≫windowFirst e r O) : a=b := by
  apply morphism_eq_of_pointwise_eq
  intro z
  have hbase : ∀u,xt.q.hom.left.base (a.hom.left.base u)=xt.q.hom.left.base (b.hom.left.base u) :=
    fun u=>(congrArg (fun k : xs.Y⟶Y=>k.hom.left.base u) ha).trans
      (congrArg (fun k : xs.Y⟶Y=>k.hom.left.base u) hb).symm
  have hGood : ∀u∈xs.q.hom.left.base ⁻¹' intrinsicRegularLocus (windowSpace e r O).obj,
      xt.q.hom.left.base (a.hom.left.base u)∈intrinsicRegularLocus Y.obj := by
    intro u hu
    have hpoint:=congrArg (fun k : xs.Y⟶Y=>k.hom.left.base u) ha
    change xt.q.hom.left.base (a.hom.left.base u)=
      (windowFirst e r O).hom.left.base (xs.q.hom.left.base u) at hpoint
    rw [hpoint]
    exact (smoothAt_regular_iff (windowFirst e r O) _ (product_smooth e r O _)).mp hu
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    xt.isSingularCentreModification.isIsoOver_intrinsicRegularLocus
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hbase
    xs.isSingularCentreModification.dense_preimage_intrinsicRegularLocus hGood) z

include hBound hrecS hrecT hNs hNt hpS hpT hcS hcT hrS hrT hCoverS hCoverT hOffS hOffT in
/-- Ordinary INITIAL covers and TWO actual terminal histories construct the
unique full smooth phase arrow on this one genuine local product chart. -/
theorem exists_unique_smooth_phase_map :
    ∃! g : xs.Y⟶xt.Y, IsSmoothMorphism g ∧ g≫xt.q=xs.q≫windowFirst e r O := by
  classical
  choose N a b ha hb hrange hproj using exists_local_smooth_span e r O H hBound
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
      j y≫xs.q.hom.left≫(windowFirst e r O).hom.left :=
    congrArg (fun k : N y⟶Y=>k.hom.left) (hproj y)
  have hscalar (y : xs.Y.obj.left) : (b y).hom.left≫xt.Y.obj.hom=j y≫xs.Y.obj.hom :=
    (Over.w (b y).hom).trans (Over.w (a y).hom).symm
  have hcompat (y z : xs.Y.obj.left) :
      pullback.fst (j y) (j z)≫(b y).hom.left=pullback.snd (j y) (j z)≫(b z).hom.left := by
    let k := pullback.fst (j y) (j z)≫j y
    let F := pullback.fst (j y) (j z)≫(b y).hom.left
    let G := pullback.snd (j y) (j z)≫(b z).hom.left
    have hk : LocallyRingedSpace.IsOpenImmersion k := by dsimp only [k]; infer_instance
    let : LocallyRingedSpace.IsOpenImmersion k := hk
    have hF : F≫xt.q.hom.left=k≫xs.q.hom.left≫(windowFirst e r O).hom.left := by
      dsimp only [F,k]
      rw [Category.assoc,hp y,Category.assoc]
    have hG : G≫xt.q.hom.left=k≫xs.q.hom.left≫(windowFirst e r O).hom.left := by
      dsimp only [G,k]
      rw [Category.assoc,hp z,←Category.assoc,pullback.condition,Category.assoc]
    have hbase : ∀v,xt.q.hom.left.base (F.base v)=xt.q.hom.left.base (G.base v) :=
      fun v=>congrArg (fun l=>l.base v) (hF.trans hG.symm)
    let D := k.base ⁻¹' (xs.q.hom.left.base ⁻¹' intrinsicRegularLocus (windowSpace e r O).obj)
    have hD : Dense D := xs.isSingularCentreModification.dense_preimage_intrinsicRegularLocus.preimage
      hk.base_open.isOpenMap
    have hGood : ∀v∈D,xt.q.hom.left.base (F.base v)∈intrinsicRegularLocus Y.obj := by
      intro v hv
      have hpoint:=congrArg (fun l=>l.base v) hF
      change xt.q.hom.left.base (F.base v)=
        (windowFirst e r O).hom.left.base (xs.q.hom.left.base (k.base v)) at hpoint
      rw [hpoint]
      exact (smoothAt_regular_iff (windowFirst e r O) _ (product_smooth e r O _)).mp hv
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
  have hfull : gNative≫xt.q=xs.q≫windowFirst e r O := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change g.left≫xt.q.hom.left=xs.q.hom.left≫(windowFirst e r O).hom.left
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
  exact maps_eq e r O wS wT TS TT xs xt g' gNative hg'.2 hfull

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseGluing
