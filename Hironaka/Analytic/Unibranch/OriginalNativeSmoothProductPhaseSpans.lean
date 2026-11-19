import Hironaka.Analytic.Unibranch.OriginalNativeSmoothTerminalWindowSpan
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothBarrierThreshold
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality
import Hironaka.Analytic.Unibranch.HironakaG10GenDisjointModification

/-! Actual initial threshold anchors and whole endpoint smooth spans on ONE
honest local product chart. Full Blueprint FIRST; no future span/cover packet. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseSpans
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

/-- The anchor is derived at the INITIAL point from the actual raw state. -/
theorem raw_anchor_of_threshold {X : SourceReducedComplexSpace} {n : ℕ}
    (w : DimEmbedding X n) (Q : MarkedIdeal n (CMfd.of (n := n) w.ambient)) {H : ℕ→ℕ}
    (hQ : IsNativeWindowRecord w Q H) (c : w.carrier)
    (hc : w.toLocalEmbedding.toPoint c∈originalSingularHSThreshold X H) : c.val∈Q.cosupp := by
  have hs := hQ.2.2.hsTowerState (BlowupTower.refl (X := CMfd.of (n := n) w.ambient)) trivial
  apply (hs.2.2.2.1 c.val).mpr
  intro l
  apply le_antisymm (hs.2.2.1 c.val l)
  exact (hc.2 l).trans_eq (originalStalkHS_localEmbedding_eq X w.toLocalEmbedding c l)

private theorem open_isIsoOver {A B : SourceReducedComplexSpace} (i : A⟶B)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) : IsIsoOver i (range i.hom.left.base) := by
  refine ⟨A.obj.left,𝟙 _,by infer_instance,?_,?_,?_⟩
  · ext a
    simp
  · simpa using hi
  · simp

private theorem chart_projection_open {B C : SourceReducedComplexSpace} (p : B⟶C)
    (e : LocalEmbedding B)
    (V : LocallyRingedSpace) (j : V⟶B.obj.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j)
    (hjp : LocallyRingedSpace.IsOpenImmersion (j≫p.hom.left))
    (he : range e.toPoint⊆range j.base) :
    LocallyRingedSpace.IsOpenImmersion (chartInclusion e≫p).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let k := LocallyRingedSpace.IsOpenImmersion.lift j e.map he
  have hk : LocallyRingedSpace.IsOpenImmersion k := by
    let : IsIso (pullback.snd j e.map) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ he
    dsimp only [k,LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hfac : k≫j=e.map := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ he
  change LocallyRingedSpace.IsOpenImmersion (e.map≫p.hom.left)
  rw [←hfac,Category.assoc]
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k hk _ hjp

/-- The SAME actual native lift is smooth; no smooth-lift packet is assumed. -/
theorem isSmoothMorphism_lift_of_isIsoOver {A B C : SourceReducedComplexSpace}
    (p : B⟶C) {U : Set C.obj.left} (hIso : IsIsoOver p U)
    (F : A⟶C) (hF : range F.hom.left.base⊆U) (hf : IsSmoothMorphism F)
    (b : A⟶B) (hb : b≫p=F) : IsSmoothMorphism b := by
  intro x
  obtain ⟨V,j,hj,hRange,hjp,_⟩ := hIso
  have hx : b.hom.left.base x∈range j.base := by
    rw [hRange]
    exact hF ⟨x,(congrArg (fun a : A⟶C=>a.hom.left.base x) hb).symm⟩
  obtain ⟨e,⟨z,hz⟩,he,_⟩ := LocalEmbedding.exists_domain (b.hom.left.base x)
    hj.base_open.isOpen_range hx
  have hep := chart_projection_open p e V j hj hjp he
  obtain ⟨d,⟨a,ha⟩,hd,_⟩ := LocalEmbedding.exists_domain x
    (e.isOpenEmbedding_toPoint.isOpen_range.preimage b.hom.left.base.hom.continuous) ⟨z,hz⟩
  have hSub : range (chartInclusion d≫b).hom.left.base ⊆ range (chartInclusion e).hom.left.base := by
    rintro _ ⟨v,rfl⟩
    exact hd ⟨v,rfl⟩
  obtain ⟨k,hk,_,_⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift
    (open_isIsoOver (chartInclusion e) e.isOpenImmersion)
    (chartInclusion d≫b) hSub
  have hcomp : k≫(chartInclusion e≫p)=chartInclusion d≫F := by
    rw [←Category.assoc,hk,Category.assoc,hb]
  have hks : IsSmoothMorphism k :=
    isSmoothMorphism_of_postcomp_openImmersion k (chartInclusion e≫p) hep
      (hcomp.symm ▸ isSmoothMorphism_comp _ _
        (isSmoothMorphism_of_isOpenImmersion _ d.isOpenImmersion) hf)
  have hlocal : IsSmoothMorphism (chartInclusion d≫b) := hk ▸
    isSmoothMorphism_comp _ _ hks (isSmoothMorphism_of_isOpenImmersion _ e.isOpenImmersion)
  exact ha ▸ isSmoothAt_of_precomp_openImmersion (chartInclusion d) b d.isOpenImmersion a (hlocal a)

private theorem product_projection_smooth {Y : SourceReducedComplexSpace}
    (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productAmbient e r)) :
    IsSmoothMorphism (windowFirst e r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e r→e.ambient) O (⊤ : Opens e.ambient) :=
    fun _ _=>mem_univ _
  have hp := isSmoothMorphism_comp (nativeProjection e r ⊤ O hWP) (targetInclusion e ⊤)
    (nativeProjection_isSmooth e r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e ⊤))
  exact (nativeProjection_square e r ⊤ O hWP) ▸ hp

section ProductPhase
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

include hBound hrecS hrecT hNs hNt hpS hpT hcS hcT hrS hrT hCoverS hCoverT hOffS hOffT in
/-- True INITIAL covers and actual off-threshold inverses DERIVE whole
endpoint span coverage on this ONE honest product chart. -/
theorem exists_local_smooth_span (y : xs.Y.obj.left) :
    ∃ (N : SourceReducedComplexSpace) (a : N⟶xs.Y) (b : N⟶xt.Y),
      LocallyRingedSpace.IsOpenImmersion a.hom.left ∧ IsSmoothMorphism b ∧
      y∈range a.hom.left.base ∧ b≫xt.q=a≫xs.q≫windowFirst e r O := by
  by_cases hy : xs.q.hom.left.base y∈originalSingularHSThreshold (windowSpace e r O) (finiteProductHS r H)
  · have ht : (windowFirst e r O).hom.left.base (xs.q.hom.left.base y)∈originalSingularHSThreshold Y H :=
      (Set.ext_iff.mp (window_threshold_preimage e r O H hBound) _).mpr hy
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hCoverS hy)
    have hyRange : y∈range (xs.map j).hom.left.base := by
      rw [xs.range_map j]
      exact hj
    obtain ⟨c,rfl⟩ := hyRange
    obtain ⟨i,t,htPoint⟩ := Set.mem_iUnion.mp (hCoverT ht)
    let c0 : (wS j).carrier := ⟨(TS j).2.proj c.val,xs.proj_mem j c⟩
    have hc0 : (wS j).toLocalEmbedding.toPoint c0=xs.q.hom.left.base ((xs.map j).hom.left.base c) :=
      (xs.square j c (xs.proj_mem j c)).symm
    have hJanchor := raw_anchor_of_threshold (wS j) (rawS j) (hrecS j) c0 (hc0.symm ▸ hy)
    have hQanchor := raw_anchor_of_threshold (wT i) (rawT i) (hrecT i) t (htPoint.symm ▸ ht)
    exact exists_local_smooth_span_at (windowFirst e r O) (product_projection_smooth e r O)
      xs xt j i (rawS j) (rawT i) (hrecS j) (hrecT i) hNs hNt (pS j) (pT i)
      (hpS j) (hpT i) (hcS j) (hrS j) (hcT i) (hrT i) c t hJanchor hQanchor htPoint
  · have hOpen : IsOpen (originalSingularHSThreshold (windowSpace e r O) (finiteProductHS r H))ᶜ :=
      (original_hs_threshold_dictionary (windowSpace e r O) (finiteProductHS r H)).2.1.isClosed.isOpen_compl
    obtain ⟨d,⟨c,hc⟩,hd,_⟩ := LocalEmbedding.exists_domain (xs.q.hom.left.base y) hOpen hy
    obtain ⟨a,ha,hOpenA,hRangeA⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift hOffS (chartInclusion d) hd
    let F := chartInclusion d≫windowFirst e r O
    have hRangeF : range F.hom.left.base⊆(originalSingularHSThreshold Y H)ᶜ := by
      rintro _ ⟨z,rfl⟩
      exact (Set.ext_iff.mp (window_threshold_compl_preimage e r O H hBound) _).mpr (hd ⟨z,rfl⟩)
    obtain ⟨b,hb,_,_⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift hOffT F hRangeF
    have hSmoothF : IsSmoothMorphism F := isSmoothMorphism_comp _ _
      (isSmoothMorphism_of_isOpenImmersion _ d.isOpenImmersion) (product_projection_smooth e r O)
    refine ⟨chartSpace d,a,b,hOpenA d.isOpenImmersion,
      isSmoothMorphism_lift_of_isIsoOver xt.q hOffT F hRangeF hSmoothF b hb,?_,?_⟩
    · rw [hRangeA]
      exact ⟨c,hc⟩
    · exact hb.trans (congrArg (fun k=>k≫windowFirst e r O) ha.symm)

end ProductPhase

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseSpans
