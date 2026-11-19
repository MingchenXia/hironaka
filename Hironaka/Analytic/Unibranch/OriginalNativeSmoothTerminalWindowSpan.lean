import Hironaka.Analytic.Unibranch.OriginalNativeIndependentTerminalSmoothLift
import Hironaka.Analytic.Unibranch.OriginalNativeTerminalWindowOverlap

/-! Actual positive-relative-dimension smooth terminal spans on the SAME
native endpoint windows. Blueprint FIRST; no caller span/lift/cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothTerminalWindowSpan
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaHolomorphicJetChartInvariance HironakaG11VanishingWindows HironakaG11PresWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11PresReduction
  HironakaG11PresLineState HironakaG11PresTowerState
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  ResolutionInvariantSpec MarkedIdealBiholomorphism
  HironakaActualPowerBoundaryExponents HironakaG8LocalPower HironakaG8LocalHistory
  HironakaG1OriginalUnequalMarkCanonical HironakaOriginalTerminalOpenComparison
  OriginalNativeProductWindow OriginalNativeSmoothGivenTargetWindow
  OriginalNativeProductIndependentRecord HironakaG1IndependentNativeSmoothCanonicalHistory
  OriginalNativeTerminalPhaseComparison OriginalNativeSmoothPhaseLiftLaws
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeTerminalWindowOverlap
open scoped ProductComplexManifold

private def carrierIso {n : ℕ} {Z : CMfd.{0} n} {C D : Set Z}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (h : C=D) :
    ofClosedAnalytic C hC ≅ ofClosedAnalytic D hD :=
  eqToIso (by cases h; rfl)

private theorem carrierIso_point {n : ℕ} {Z : CMfd.{0} n} {C D : Set Z}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (h : C=D)
    (z : (ofClosedAnalytic C hC).obj.left) : ((carrierIso hC hD h).hom.hom.left.base z).val=z.val := by
  cases h
  rfl

private theorem carrierIso_inv_point {n : ℕ} {Z : CMfd.{0} n} {C D : Set Z}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (h : C=D)
    (z : (ofClosedAnalytic D hD).obj.left) : ((carrierIso hC hD h).inv.hom.left.base z).val=z.val := by
  cases h
  rfl

private def currentIso {n : ℕ} {M Z : CMfd.{0} n} (Q : MarkedIdeal n M)
    (hQ : IsInvDomain n Q) (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    {H : ℕ→ℕ} (hHS : HSTowerState Q W H) (T : BlowupTower M Z) (hT : IsGeoTestTower Q T)
    {C : Set Z} (hC : IsComplexAnalyticSubset (n := n) C)
    (hEq : C=HomogenizedGlueingTower.strictAlong T W) :
    ofClosedAnalytic C hC ≅ strictSpace T W hW :=
  carrierIso hC (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)
    (hEq.trans (strictCarrier_eq_conventional Q hQ W hW hHS T hT))

private theorem currentIso_point {n : ℕ} {M Z : CMfd.{0} n} (Q : MarkedIdeal n M)
    (hQ : IsInvDomain n Q) (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    {H : ℕ→ℕ} (hHS : HSTowerState Q W H) (T : BlowupTower M Z) (hT : IsGeoTestTower Q T)
    {C : Set Z} (hC : IsComplexAnalyticSubset (n := n) C)
    (hEq : C=HomogenizedGlueingTower.strictAlong T W) (z : (ofClosedAnalytic C hC).obj.left) :
    ((currentIso Q hQ W hW hHS T hT hC hEq).hom.hom.left.base z).val=z.val :=
  carrierIso_point hC (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)
    (hEq.trans (strictCarrier_eq_conventional Q hQ W hW hHS T hT)) z

private theorem currentIso_inv_point {n : ℕ} {M Z : CMfd.{0} n} (Q : MarkedIdeal n M)
    (hQ : IsInvDomain n Q) (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    {H : ℕ→ℕ} (hHS : HSTowerState Q W H) (T : BlowupTower M Z) (hT : IsGeoTestTower Q T)
    {C : Set Z} (hC : IsComplexAnalyticSubset (n := n) C)
    (hEq : C=HomogenizedGlueingTower.strictAlong T W) (z : (strictSpace T W hW).obj.left) :
    ((currentIso Q hQ W hW hHS T hT hC hEq).inv.hom.left.base z).val=z.val :=
  carrierIso_inv_point hC (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T)
    (hEq.trans (strictCarrier_eq_conventional Q hQ W hW hHS T hT)) z

private theorem iso_smooth {A B : SourceReducedComplexSpace} (E : A≅B) : IsSmoothMorphism E.hom :=
  isSmoothMorphism_of_isOpenImmersion _ (by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft E).hom
    infer_instance)

private theorem raw_resolution {n : ℕ} {M Z : CMfd.{0} n} (Q : MarkedIdeal n M)
    (hQ : IsInvDomain n Q) (p : ℕ) (hp : 1≤p) (T : BlowupTower M Z)
    (hT : IsGeoResolution (powerMarked Q p) T) : IsGeoResolution Q T :=
  ((locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hp).wEquiv.isGeoResolution_iff T).mpr hT

section Target
variable {Y : SourceReducedComplexSpace} {n : ℕ} {ι : Type}
  {w : ι→DimEmbedding Y n} {TT : Towers w} (xt : XStage w TT) (i : ι)
  (Q : MarkedIdeal n (Amb w i)) {H : ℕ→ℕ} (hQ : IsNativeWindowRecord (w i) Q H)
  (p : ℕ) (hp : 1≤p) (hr : IsGeoResolution (powerMarked Q p) (TT i).2)

private def targetIso : ofClosedAnalytic (xt.carrier i) (xt.analytic i) ≅
    strictSpace (TT i).2 (w i).carrier (w i).analytic :=
  currentIso Q hQ.1 (w i).carrier (w i).analytic hQ.2.2.hsTowerState (TT i).2
    (raw_resolution Q hQ.1 p hp (TT i).2 hr).1 (xt.analytic i) (xt.carrier_eq i)

private theorem targetIso_point (z : (ofClosedAnalytic (xt.carrier i) (xt.analytic i)).obj.left) :
    ((targetIso xt i Q hQ p hp hr).hom.hom.left.base z).val=z.val :=
  currentIso_point Q hQ.1 (w i).carrier (w i).analytic hQ.2.2.hsTowerState (TT i).2
    (raw_resolution Q hQ.1 p hp (TT i).2 hr).1 (xt.analytic i) (xt.carrier_eq i) z

private theorem targetIso_inv_point (z : (strictSpace (TT i).2 (w i).carrier (w i).analytic).obj.left) :
    ((targetIso xt i Q hQ p hp hr).inv.hom.left.base z).val=z.val :=
  currentIso_inv_point Q hQ.1 (w i).carrier (w i).analytic hQ.2.2.hsTowerState (TT i).2
    (raw_resolution Q hQ.1 p hp (TT i).2 hr).1 (xt.analytic i) (xt.carrier_eq i) z

end Target

section Source
variable {X Y : SourceReducedComplexSpace} {f : X⟶Y} {x : X.obj.left}
  {e : LocalEmbedding Y} {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
  {κ : Type} {ww : κ→DimEmbedding X (w.target.dim+w.rank)} {TS : Towers ww}
  (xs : XStage ww TS) (j : κ) {c : (ww j).carrier}
  (M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint (ww j) c)
  (J : MarkedIdeal (w.target.dim+w.rank) (Amb ww j)) {Hs : ℕ→ℕ}
  (hJ : IsNativeWindowRecord (ww j) J Hs) (p : ℕ) (hp : 1≤p)
  (hc : IsCanonical (powerMarked J p)
    ((canonicalInvariant (w.target.dim+w.rank)).inv (powerMarked J p)) (TS j).2)
  (hr : IsGeoResolution (powerMarked J p) (TS j).2)

private def sourceIso :
    windowOpenSpace xs j (OriginalNativeIndependentTerminalSmoothLift.sourceOpen w M) ≅
    OriginalNativeIndependentTerminalSmoothLift.sourceEndpoint w M (TS j).2 := by
  let U := OriginalNativeIndependentTerminalSmoothLift.sourceOpen w M
  let JU := MarkedIdeal.pullback (Subtype.val : U→(ww j).ambient) J
  have hd := original_terminal_open_history_data J hJ.1 (TS j).2
    ((canonicalInvariant_isCanonical_power_iff J hJ.1 p hp (TS j).2).mpr hc)
    (raw_resolution J hJ.1 p hp (TS j).2 hr) U
  have hHS : HSTowerState (X := CMfd.of (n := w.target.dim+w.rank) U) JU
      ((Subtype.val : U→(ww j).ambient) ⁻¹' (ww j).carrier) Hs := by
    intro Z T hT
    exact (hJ.2.2.restrict U).hsTowerState T hT
  exact currentIso JU hd.1
    (OriginalNativeIndependentTerminalSmoothLift.sourceCarrier w M) _ hHS
    (restrict U (TS j).2) hd.2.2.1 _ (windowOpen_carrier xs j U)

private theorem sourceIso_point
    (z : (windowOpenSpace xs j (OriginalNativeIndependentTerminalSmoothLift.sourceOpen w M)).obj.left) :
    ((sourceIso w xs j M J hJ p hp hc hr).hom.hom.left.base z).val=z.val := by
  unfold sourceIso
  apply currentIso_point

private theorem sourceIso_projection :
    (sourceIso w xs j M J hJ p hp hc hr).hom ≫
      OriginalNativeIndependentTerminalSmoothLift.sourceOriginalProjection w M (TS j).2 =
    windowOpenMap xs j (OriginalNativeIndependentTerminalSmoothLift.sourceOpen w M) ≫ xs.q := by
  apply morphism_eq_of_pointwise_eq
  intro z
  have hz := sourceIso_point w xs j M J hJ p hp hc hr z
  change (ww j).toLocalEmbedding.toPoint ⟨(TS j).2.proj
    ((sourceIso w xs j M J hJ p hp hc hr).hom.hom.left.base z).val.val,_⟩ =
    xs.q.hom.left.base ((xs.map j).hom.left.base ⟨z.val.val,z.property⟩)
  rw [xs.square j _ (xs.proj_mem j ⟨z.val.val,z.property⟩)]
  exact congrArg (ww j).toLocalEmbedding.toPoint (Subtype.ext (congrArg (fun a=> (TS j).2.proj a.val) hz))

end Source

private theorem targetIso_projection {Y : SourceReducedComplexSpace} {n : ℕ} {ι : Type}
    {w : ι→DimEmbedding Y n} {TT : Towers w} (xt : XStage w TT) (i : ι)
    (Q : MarkedIdeal n (Amb w i)) {H : ℕ→ℕ} (hQ : IsNativeWindowRecord (w i) Q H)
    (p : ℕ) (hp : 1≤p) (hr : IsGeoResolution (powerMarked Q p) (TT i).2) :
    (targetIso xt i Q hQ p hp hr).inv ≫ xt.map i ≫ xt.q =
      projection (TT i).2 (w i).carrier (w i).analytic ≫ chartInclusion (w i).toLocalEmbedding := by
  apply morphism_eq_of_pointwise_eq
  intro z
  have hz := targetIso_inv_point xt i Q hQ p hp hr z
  change xt.q.hom.left.base ((xt.map i).hom.left.base
      ((targetIso xt i Q hQ p hp hr).inv.hom.left.base z)) =
    (w i).toLocalEmbedding.toPoint ⟨(TT i).2.proj z.val,_⟩
  rw [xt.square i _ (xt.proj_mem i _)]
  exact congrArg (w i).toLocalEmbedding.toPoint (Subtype.ext (congrArg (TT i).2.proj hz))

/-- An ordinary smooth map and the TWO actual whole terminal histories
construct a smooth native span through the SAME actual current point. -/
private theorem exists_local_smooth_span_at_basepoint
    {X Y : SourceReducedComplexSpace} (f : X⟶Y) (x0 : X.obj.left) (hf : IsSmoothMorphism f)
    {Ns Nt : ℕ} {κ ι : Type} {wS : κ→DimEmbedding X Ns} {wT : ι→DimEmbedding Y Nt}
    {TS : Towers wS} {TT : Towers wT} (xs : XStage wS TS) (xt : XStage wT TT)
    (j : κ) (i : ι) (J : MarkedIdeal Ns (Amb wS j)) (Q : MarkedIdeal Nt (Amb wT i))
    {Hs H : ℕ→ℕ} (hJ : IsNativeWindowRecord (wS j) J Hs) (hQ : IsNativeWindowRecord (wT i) Q H)
    (hNs : Ns=Hs 1-1) (hNt : Nt=H 1-1) (p q : ℕ) (hp : 1≤p) (hq : 1≤q)
    (hcS : IsCanonical (powerMarked J p) ((canonicalInvariant Ns).inv (powerMarked J p)) (TS j).2)
    (hrS : IsGeoResolution (powerMarked J p) (TS j).2)
    (hcT : IsCanonical (powerMarked Q q) ((canonicalInvariant Nt).inv (powerMarked Q q)) (TT i).2)
    (hrT : IsGeoResolution (powerMarked Q q) (TT i).2)
    (c : xs.carrier j) (t : (wT i).carrier)
    (hcJ : (TS j).2.proj c.val∈J.cosupp) (htQ : t.val∈Q.cosupp)
    (hcx : xs.q.hom.left.base ((xs.map j).hom.left.base c)=x0)
    (ht : (wT i).toLocalEmbedding.toPoint t=f.hom.left.base x0) :
    ∃ (N : SourceReducedComplexSpace) (a : N⟶xs.Y) (b : N⟶xt.Y),
      LocallyRingedSpace.IsOpenImmersion a.hom.left ∧ IsSmoothMorphism b ∧
      (xs.map j).hom.left.base c∈Set.range a.hom.left.base ∧
      b ≫ xt.q=a ≫ xs.q ≫ f := by
  let c0 : (wS j).carrier := ⟨(TS j).2.proj c.val,xs.proj_mem j c⟩
  obtain ⟨w,hDim,M,A,g,_,hg,_,hOrig,_⟩ :=
    OriginalNativeIndependentTerminalSmoothLift.exists_independent_terminal_smooth_lift
      f x0 (hf x0) (wT i).toLocalEmbedding Q hQ.1 hQ.2.1 hQ.2.2 hNt t ht htQ
      ⊤ trivial (wS j) c0 ((xs.square j c (xs.proj_mem j c)).symm.trans hcx)
      J hJ.1 hJ.2.1 hJ.2.2 hcJ hNs (TS j).2 (TT i).2 p q hp hq hcS hrS hcT hrT
  cases hDim
  change ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint (wS j) c0 at M
  change IndependentCanonicalHistory w M Q J (TT i).2 at A
  change OriginalNativeIndependentTerminalSmoothLift.sourceEndpoint w M (TS j).2 ⟶
    strictSpace (TT i).2 (wT i).carrier (wT i).analytic at g
  have hOriginal : g ≫ projection (TT i).2 (wT i).carrier (wT i).analytic ≫
      chartInclusion (wT i).toLocalEmbedding =
    OriginalNativeIndependentTerminalSmoothLift.sourceOriginalProjection w M (TS j).2 ≫ f := hOrig
  let U := OriginalNativeIndependentTerminalSmoothLift.sourceOpen w M
  let E := sourceIso w xs j M J hJ p hp hcS hrS
  let F := targetIso xt i Q hQ q hq hrT
  let a := windowOpenMap xs j U
  let b := E.hom ≫ g ≫ F.inv ≫ xt.map i
  refine ⟨windowOpenSpace xs j U,a,b,windowOpenMap_isOpenImmersion xs j U,?_,?_,?_⟩
  · exact isSmoothMorphism_comp _ _ (iso_smooth E)
      (isSmoothMorphism_comp _ _ hg (isSmoothMorphism_comp _ _
        (iso_smooth F.symm) (isSmoothMorphism_of_isOpenImmersion _ (xt.isOpenImmersion i))))
  · have hcU : (TS j).2.proj c.val∈U := by
      change c0.val.val∈M.targetOpen
      rw [←M.point_eq]
      exact (M.phi _).property
    exact ⟨⟨⟨c.val,hcU⟩,c.property⟩,rfl⟩
  · change E.hom ≫ g ≫ F.inv ≫ xt.map i ≫ xt.q=a ≫ xs.q ≫ f
    calc
      _ = E.hom ≫ g ≫ projection (TT i).2 (wT i).carrier (wT i).analytic ≫
          chartInclusion (wT i).toLocalEmbedding :=
        congrArg (fun k => E.hom ≫ g ≫ k) (targetIso_projection xt i Q hQ q hq hrT)
      _ = E.hom ≫ OriginalNativeIndependentTerminalSmoothLift.sourceOriginalProjection w M (TS j).2 ≫ f :=
        congrArg (fun k => E.hom ≫ k) hOriginal
      _ = (E.hom ≫ OriginalNativeIndependentTerminalSmoothLift.sourceOriginalProjection w M (TS j).2) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k => k ≫ f) (sourceIso_projection w xs j M J hJ p hp hcS hrS)


/-- An ordinary smooth map and the TWO actual whole terminal histories
construct a smooth native span through the SAME actual current point. -/
theorem exists_local_smooth_span_at
    {X Y : SourceReducedComplexSpace} (f : X⟶Y) (hf : IsSmoothMorphism f)
    {Ns Nt : ℕ} {κ ι : Type} {wS : κ→DimEmbedding X Ns} {wT : ι→DimEmbedding Y Nt}
    {TS : Towers wS} {TT : Towers wT} (xs : XStage wS TS) (xt : XStage wT TT)
    (j : κ) (i : ι) (J : MarkedIdeal Ns (Amb wS j)) (Q : MarkedIdeal Nt (Amb wT i))
    {Hs H : ℕ→ℕ} (hJ : IsNativeWindowRecord (wS j) J Hs) (hQ : IsNativeWindowRecord (wT i) Q H)
    (hNs : Ns=Hs 1-1) (hNt : Nt=H 1-1) (p q : ℕ) (hp : 1≤p) (hq : 1≤q)
    (hcS : IsCanonical (powerMarked J p) ((canonicalInvariant Ns).inv (powerMarked J p)) (TS j).2)
    (hrS : IsGeoResolution (powerMarked J p) (TS j).2)
    (hcT : IsCanonical (powerMarked Q q) ((canonicalInvariant Nt).inv (powerMarked Q q)) (TT i).2)
    (hrT : IsGeoResolution (powerMarked Q q) (TT i).2)
    (c : xs.carrier j) (t : (wT i).carrier)
    (hcJ : (TS j).2.proj c.val∈J.cosupp) (htQ : t.val∈Q.cosupp)
    (ht : (wT i).toLocalEmbedding.toPoint t=f.hom.left.base (xs.q.hom.left.base ((xs.map j).hom.left.base c))) :
    ∃ (N : SourceReducedComplexSpace) (a : N⟶xs.Y) (b : N⟶xt.Y),
      LocallyRingedSpace.IsOpenImmersion a.hom.left ∧ IsSmoothMorphism b ∧
      (xs.map j).hom.left.base c∈Set.range a.hom.left.base ∧
      b ≫ xt.q=a ≫ xs.q ≫ f := by
  exact exists_local_smooth_span_at_basepoint f
    (xs.q.hom.left.base ((xs.map j).hom.left.base c)) hf xs xt j i J Q hJ hQ hNs hNt
    p q hp hq hcS hrS hcT hrT c t hcJ htQ rfl ht

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothTerminalWindowSpan
