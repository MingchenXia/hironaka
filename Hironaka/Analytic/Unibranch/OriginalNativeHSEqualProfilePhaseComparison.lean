import Hironaka.Analytic.Unibranch.OriginalNativeHSFactoryTerminalFrame
import Hironaka.Analytic.Unibranch.OriginalNativeHSFactoryOverlapCut
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedTerminalPhaseComparison

/-! ACTUAL equal-profile factory phases in a genuine old-source overlap.
Blueprint FIRST: original-native-hs-equal-profile-phase-comparison.tex.
Every phase datum is computed internally from ordinary factory inputs. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSEqualProfilePhaseComparison
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11PresReduction
  HironakaG11CompatibleCanonicalTowers BlowupTowers ResolutionInvariantSeq MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualPowerBoundaryExponents CanonicalCentres OriginalNativeHSOuterHistory
  OriginalIntrinsicHSSuperlevels OriginalRelativelyCompactRestriction
  HironakaIntrinsicComplexAnalyticRegularLocus

private theorem resolution_on_base_open {B W : SourceReducedComplexSpace} {n : ℕ} {ι : Type}
    (w : ι → DimEmbedding B n) (j : W ⟶ B) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (raw : ∀i,MarkedIdeal n (Amb w i)) {H : ℕ → ℕ}
    (hRaw : ∀i,IsNativeWindowRecord (w i) (raw i) H)
    (e : ι → ℕ) (he : ∀i,1≤e i) (i : ι) {D : CMfd.{0} n}
    (T : BlowupTower (Amb w i) D) (hr : IsGeoResolution (powerMarked (raw i) (e i)) T) :
    IsGeoResolution (OriginalNativeHSBaseOpenWindows.record w j hj raw e i)
      (OriginalNativeHSBaseOpenWindows.history w j hj i T).tower := by
  rw [OriginalNativeHSBaseOpenWindows.record_eq_pullback w j hj raw hRaw e i]
  have hD := powerMarked_isInvDomain (raw i) (hRaw i).1 (he i)
  exact MarkedIdealOpenBiholomorphism.isGeoResolution_transport_restrict
    (OriginalNativeHSBaseOpenWindows.traceOpen w j hj i)
    (OriginalNativeHSBaseOpenWindows.baseEquiv w j hj i)
    hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent hr

private theorem paste_old_square {A C B D F E Z U : SourceReducedComplexSpace}
    (q : A ⟶ U) (i : U ⟶ Z) (a : A ⟶ C) (r : C ⟶ B) (j : B ⟶ Z)
    (b : Z ⟶ E) (v : B ⟶ D) (l : C ⟶ F) (p : F ⟶ D)
    (J : D ⟶ E) (hs : q ≫ i=a ≫ r ≫ j) (hj : j ≫ b=v ≫ J)
    (hr : r ≫ v=l ≫ p) : q ≫ i ≫ b=(a ≫ l) ≫ p ≫ J := by
  calc
    _ = (a ≫ r ≫ j) ≫ b := congrArg (fun f => f ≫ b) hs
    _ = a ≫ r ≫ (j ≫ b) := by simp only [Category.assoc]
    _ = a ≫ r ≫ (v ≫ J) := congrArg (fun f => a ≫ r ≫ f) hj
    _ = a ≫ (r ≫ v) ≫ J := by simp only [Category.assoc]
    _ = a ≫ (l ≫ p) ≫ J := congrArg (fun f => a ≫ f ≫ J) hr
    _ = _ := by simp only [Category.assoc]

section Cut
variable (Y : SourceReducedComplexSpace) (K : Set Y.obj.left) (hK : IsCompact K)
  (hSing : (K ∩ intrinsicSingularLocus Y.obj).Nonempty)
  {Z : SourceReducedComplexSpace} (a : Z ⟶ Y)
  (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
  (C : Set Z.obj.left) (hC : IsCompact C) (hImage : a.hom.left.base '' C ⊆ K)
local notation "N" => OriginalNativeHSFactoryOverlapCut.neighbourhood Y K hK hSing a ha C hC hImage
local notation "d" => OriginalNativeHSFactoryTerminalFrame.dimension Y K hK hSing
local notation "H" => OriginalNativeHSFactoryTerminalFrame.profile Y K hK hSing
local notation "wF" => OriginalNativeHSFactoryTerminalFrame.window Y K hK hSing
local notation "rF" => OriginalNativeHSFactoryTerminalFrame.rawRecord Y K hK hSing
local notation "eF" => OriginalNativeHSFactoryTerminalFrame.exponent Y K hK hSing
local notation "pF" => OriginalNativeHSFactoryTerminalFrame.positive Y K hK hSing
local notation "sF" => OriginalNativeHSFactoryTerminalFrame.stage Y K hK hSing
local notation "xF" => OriginalNativeHSFactoryTerminalFrame.nativeStage Y K hK hSing
local notation "hF" => OriginalNativeHSShadowPhaseFactory.history Y K hK hSing
local notation "nF" => OriginalNativeHSFactoryTerminalFrame.native_record Y K hK hSing
local notation "wC" => OriginalNativeHSBaseOpenWindows.window (wF) (OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion (N)) (OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion_isOpenImmersion (N))
local notation "rC" => OriginalNativeHSBaseOpenWindows.rawRecord (wF) (OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion (N)) (OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion_isOpenImmersion (N)) (rF)

private def cutStage : GStage (canonicalInvariant (d))
    (OriginalNativeHSBaseOpenWindows.record (wF) (N).inclusion (N).inclusion_isOpenImmersion (rF) (eF))
    (mapAdm (wC)) (OriginalNativeHSShadowPhaseFactory.finalInput Y K hK hSing).clock :=
  OriginalNativeHSBaseOpenStage.stage (wF) (N).inclusion (N).inclusion_isOpenImmersion
    (rF) (nF) (eF) (pF) (canonicalInvariant (d)) (sF)

private def cutNative : XStage (wC) (cutStage Y K hK hSing a ha C hC hImage).T :=
  OriginalNativeHSBaseOpenNativeStage.compatibleNativeStage (wF) (N).openSet (N).compactClosure
    (rF) (nF) (eF) (pF) (canonicalInvariant (d)) (sF) (xF) (hF)
    (OriginalNativeHSFactoryTerminalFrame.history_projection Y K hK hSing)

private def cutHistory : PhysicalHistory (N).source (cutNative Y K hK hSing a ha C hC hImage).Y :=
  OriginalNativePhysicalHistoryRestriction.restrict (hF) (N).openSet (N).compactClosure

private theorem cutProjection : (cutHistory Y K hK hSing a ha C hC hImage).projection=
    (cutNative Y K hK hSing a ha C hC hImage).q := rfl

private theorem cutTerminal (i : (OriginalNativeHSShadowPhaseFactory.finalInput Y K hK hSing).ι) :
    IsGeoResolution (powerMarked ((rC) i) ((eF) i))
      (((cutStage Y K hK hSing a ha C hC hImage).T i).2) := by
  change IsGeoResolution (OriginalNativeHSBaseOpenWindows.record (wF) (N).inclusion
    (N).inclusion_isOpenImmersion (rF) (eF) i)
    (OriginalNativeHSBaseOpenWindows.history (wF) (N).inclusion (N).inclusion_isOpenImmersion i ((sF).T i).2).tower
  exact resolution_on_base_open (wF) (N).inclusion (N).inclusion_isOpenImmersion
    (rF) (nF) (eF) (pF) i ((sF).T i).2
    (OriginalNativeHSFactoryTerminalFrame.terminal Y K hK hSing i)

private theorem cutCover : originalSingularHSThreshold (N).source (H) ⊆
    ⋃i,range ((wC) i).toLocalEmbedding.toPoint :=
  OriginalNativeHSInitialThresholdCover.pullback_threshold_covered (wF) (H)
    (OriginalNativeHSFactoryTerminalFrame.threshold_covered Y K hK hSing)
    (N).inclusion (N).inclusion_isOpenImmersion

private theorem cutOff : IsIsoOver (cutNative Y K hK hSing a ha C hC hImage).q
    (originalSingularHSThreshold (N).source (H))ᶜ := by
  change IsIsoOver (OriginalNativePhysicalHistoryRestriction.restrict (hF) (N).openSet (N).compactClosure).projection _
  rw [OriginalNativePhysicalHistoryRestriction.projection_restrict]
  exact OriginalNativeHSThresholdIsomorphism.isIsoOver_restrictionProjection_threshold_compl (H)
    (hF).projection (hF).singularModification.isProperMap (N).openSet (N).compactClosure
    (OriginalNativeHSFactoryTerminalFrame.off_threshold Y K hK hSing)

local notation "jC" => OriginalNativeHSFactoryOverlapCut.toCommon Y K hK hSing a ha C hC hImage
local notation "hjC" => OriginalNativeHSFactoryOverlapCut.toCommon_isOpenImmersion Y K hK hSing a ha C hC hImage
local notation "J" => OriginalNativeHSShadowPhaseFactory.baseInclusion Y K hK hSing
local notation "hJ" => OriginalNativeHSShadowPhaseFactory.baseInclusion_isOpenImmersion Y K hK hSing

private def firstInclusion : (cutNative Y K hK hSing a ha C hC hImage).Y ⟶
    OriginalNativeHSShadowPhaseFactory.source Y K hK hSing :=
  inclusion _ (preimageOpen (N).openSet (hF).projection)
    (isCompact_closure_preimage (N).openSet (hF).projection (N).compactClosure (hF).singularModification.isProperMap)

private theorem endpoint_range (O : Opens Z.obj.left) (hO : IsCompact (closure (O : Set Z.obj.left)))
    (hRange : closure (O : Set Z.obj.left) ⊆ range (jC).hom.left.base) :
    range (OriginalNativePrescribedOpenHistory.sourceInclusion (jC) (hjC) O hO hRange
      (cutHistory Y K hK hSing a ha C hC hImage) ≫
      firstInclusion Y K hK hSing a ha C hC hImage).hom.left.base =
      ((hF).projection ≫ (J)).hom.left.base ⁻¹' (a.hom.left.base '' (O : Set Z.obj.left)) := by
  ext p
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨(jC).hom.left.base
      ((cutHistory Y K hK hSing a ha C hC hImage).projection.hom.left.base u.val),u.property,?_⟩
    have hs := congrArg (fun f : (N).source ⟶ Y => f.hom.left.base
      ((cutHistory Y K hK hSing a ha C hC hImage).projection.hom.left.base u.val))
      (OriginalNativeHSFactoryOverlapCut.toCommon_square Y K hK hSing a ha C hC hImage)
    have hp := congrArg (fun f : (cutNative Y K hK hSing a ha C hC hImage).Y ⟶
      OriginalNativeHSShadowPhaseFactory.base Y K hK hSing => f.hom.left.base u.val)
      (OriginalNativePhysicalHistoryRestriction.projection_square (hF) (N).openSet (N).compactClosure)
    exact hs.trans (congrArg (J).hom.left.base hp)
  · rintro ⟨z,hz,hzp⟩
    obtain ⟨b,hb⟩ := hRange (subset_closure hz)
    have hs := congrArg (fun f : (N).source ⟶ Y => f.hom.left.base b)
      (OriginalNativeHSFactoryOverlapCut.toCommon_square Y K hK hSing a ha C hC hImage)
    have hbase : (hF).projection.hom.left.base p=b.val :=
      (hJ).base_open.injective (hzp.symm.trans ((congrArg a.hom.left.base hb).symm.trans hs))
    let p₀ : (cutNative Y K hK hSing a ha C hC hImage).Y.obj.left :=
      ⟨p,by change (hF).projection.hom.left.base p ∈ (N).openSet;rw [hbase];exact b.property⟩
    have hq : (cutHistory Y K hK hSing a ha C hC hImage).projection.hom.left.base p₀=b :=
      Subtype.ext ((OriginalNativePhysicalHistoryRestriction.projection_point
        (hF) (N).openSet (N).compactClosure p₀).trans hbase)
    let u : (OriginalNativePrescribedOpenHistory.source (jC) (hjC) O hO hRange
        (cutHistory Y K hK hSing a ha C hC hImage)).obj.left :=
      ⟨p₀,by
        change (jC).hom.left.base ((cutHistory Y K hK hSing a ha C hC hImage).projection.hom.left.base p₀) ∈ O
        rw [hq,hb]
        exact hz⟩
    exact ⟨u,rfl⟩

end Cut

/-- Ordinary dependent equality elimination only; actual phase data are
constructed below, and no such packet is a public input. -/
private theorem compare_dimensions {X BT BS : SourceReducedComplexSpace} {nT nS : ℕ} {ι κ : Type}
    (hd : nT=nS) (jT : BT ⟶ X) (jS : BS ⟶ X)
    (hjT : LocallyRingedSpace.IsOpenImmersion jT.hom.left)
    (hjS : LocallyRingedSpace.IsOpenImmersion jS.hom.left)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
    (hRangeT : closure (U : Set X.obj.left) ⊆ range jT.hom.left.base)
    (hRangeS : closure (U : Set X.obj.left) ⊆ range jS.hom.left.base)
    (wT : ι → DimEmbedding BT nT) (wS : κ → DimEmbedding BS nS)
    (rawT : ∀i,MarkedIdeal nT (Amb wT i)) (rawS : ∀j,MarkedIdeal nS (Amb wS j))
    (H : ℕ → ℕ) (hRawT : ∀i,IsNativeWindowRecord (wT i) (rawT i) H)
    (hRawS : ∀j,IsNativeWindowRecord (wS j) (rawS j) H)
    (eT : ι → ℕ) (eS : κ → ℕ) (heT : ∀i,1≤eT i) (heS : ∀j,1≤eS j)
    {mT mS : ℕ}
    (sT : GStage (canonicalInvariant nT) (fun i=>powerMarked (rawT i) (eT i)) (mapAdm wT) mT)
    (sS : GStage (canonicalInvariant nS) (fun j=>powerMarked (rawS j) (eS j)) (mapAdm wS) mS)
    (xt : XStage wT sT.T) (xs : XStage wS sS.T)
    (hT : PhysicalHistory BT xt.Y) (hS : PhysicalHistory BS xs.Y)
    (hqT : hT.projection=xt.q) (hqS : hS.projection=xs.q)
    (hrT : ∀i,IsGeoResolution (powerMarked (rawT i) (eT i)) (sT.T i).2)
    (hrS : ∀j,IsGeoResolution (powerMarked (rawS j) (eS j)) (sS.T j).2)
    (hCoverT : originalSingularHSThreshold BT H ⊆ ⋃i,range (wT i).toLocalEmbedding.toPoint)
    (hCoverS : originalSingularHSThreshold BS H ⊆ ⋃j,range (wS j).toLocalEmbedding.toPoint)
    (hOffT : IsIsoOver xt.q (originalSingularHSThreshold BT H)ᶜ)
    (hOffS : IsIsoOver xs.q (originalSingularHSThreshold BS H)ᶜ) :
    ∃ F : OriginalNativePrescribedOpenHistory.source jS hjS U hU hRangeS hS ≅
      OriginalNativePrescribedOpenHistory.source jT hjT U hU hRangeT hT,
      F.hom ≫ (OriginalNativePrescribedOpenHistory.history jT hjT U hU hRangeT hT).projection=
        (OriginalNativePrescribedOpenHistory.history jS hjS U hU hRangeS hS).projection := by
  subst nS
  exact OriginalNativePrescribedTerminalPhaseComparison.exists_comparison jT jS hjT hjS U hU hRangeT hRangeS
    wT wS rawT rawS H hRawT hRawS eT eS heT heS sT sS xt xs hT hS hqT hqS
    hrT hrS hCoverT hCoverS hOffT hOffS

section ActualPair
variable (YT YS : SourceReducedComplexSpace) (KT : Set YT.obj.left) (KS : Set YS.obj.left)
  (hKT : IsCompact KT) (hKS : IsCompact KS)
  (hSingT : (KT ∩ intrinsicSingularLocus YT.obj).Nonempty)
  (hSingS : (KS ∩ intrinsicSingularLocus YS.obj).Nonempty)
  {Z : SourceReducedComplexSpace} (aT : Z ⟶ YT) (aS : Z ⟶ YS)
  (haT : LocallyRingedSpace.IsOpenImmersion aT.hom.left)
  (haS : LocallyRingedSpace.IsOpenImmersion aS.hom.left)
  (C : Set Z.obj.left) (hC : IsCompact C)
  (hImageT : aT.hom.left.base '' C ⊆ KT) (hImageS : aS.hom.left.base '' C ⊆ KS)
  (Ω : Opens Z.obj.left) (hCΩ : C ⊆ Ω)
local notation "jT" => OriginalNativeHSFactoryOverlapCut.toCommon YT KT hKT hSingT aT haT C hC hImageT
local notation "jS" => OriginalNativeHSFactoryOverlapCut.toCommon YS KS hKS hSingS aS haS C hC hImageS
local notation "hjT" => OriginalNativeHSFactoryOverlapCut.toCommon_isOpenImmersion YT KT hKT hSingT aT haT C hC hImageT
local notation "hjS" => OriginalNativeHSFactoryOverlapCut.toCommon_isOpenImmersion YS KS hKS hSingS aS haS C hC hImageS

private def commonOpen : Opens Z.obj.left :=
  ⟨range (jT).hom.left.base ∩ range (jS).hom.left.base ∩ Ω,
    ((hjT).base_open.isOpen_range.inter (hjS).base_open.isOpen_range).inter Ω.isOpen⟩

include hCΩ in
private theorem commonCompact_in_open : C ⊆ commonOpen YT YS KT KS hKT hKS hSingT hSingS
    aT aS haT haS C hC hImageT hImageS Ω := by
  intro c hc
  exact ⟨⟨OriginalNativeHSFactoryOverlapCut.compact_retained YT KT hKT hSingT aT haT C hC hImageT hc,
    OriginalNativeHSFactoryOverlapCut.compact_retained YS KS hKS hSingS aS haS C hC hImageS hc⟩,hCΩ hc⟩

/-- All common-fibre points survive ONE actual common neighbourhood, with
closure in BOTH internally derived actual phase-base images and Ω. -/
def neighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood Z C
    (commonOpen YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood Z C hC _
    (commonCompact_in_open YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ)

local notation "NC" => neighbourhood YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ
local notation "NT" => OriginalNativeHSFactoryOverlapCut.neighbourhood YT KT hKT hSingT aT haT C hC hImageT
local notation "NS" => OriginalNativeHSFactoryOverlapCut.neighbourhood YS KS hKS hSingS aS haS C hC hImageS
local notation "incT" => OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion (NT)
local notation "incS" => OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion (NS)
local notation "hincT" => OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion_isOpenImmersion (NT)
local notation "hincS" => OriginalNativePrecompactNeighbourhood.Neighbourhood.inclusion_isOpenImmersion (NS)
local notation "wFT" => OriginalNativeHSFactoryTerminalFrame.window YT KT hKT hSingT
local notation "wFS" => OriginalNativeHSFactoryTerminalFrame.window YS KS hKS hSingS
local notation "rFT" => OriginalNativeHSFactoryTerminalFrame.rawRecord YT KT hKT hSingT
local notation "rFS" => OriginalNativeHSFactoryTerminalFrame.rawRecord YS KS hKS hSingS
local notation "wCT" => OriginalNativeHSBaseOpenWindows.window (wFT) (incT) (hincT)
local notation "wCS" => OriginalNativeHSBaseOpenWindows.window (wFS) (incS) (hincS)
local notation "rCT" => OriginalNativeHSBaseOpenWindows.rawRecord (wFT) (incT) (hincT) (rFT)
local notation "rCS" => OriginalNativeHSBaseOpenWindows.rawRecord (wFS) (incS) (hincS) (rFS)
local notation "eT" => OriginalNativeHSFactoryTerminalFrame.exponent YT KT hKT hSingT
local notation "eS" => OriginalNativeHSFactoryTerminalFrame.exponent YS KS hKS hSingS
local notation "HT" => OriginalNativeHSFactoryTerminalFrame.profile YT KT hKT hSingT
local notation "HS" => OriginalNativeHSFactoryTerminalFrame.profile YS KS hKS hSingS
local notation "sT" => cutStage YT KT hKT hSingT aT haT C hC hImageT
local notation "sS" => cutStage YS KS hKS hSingS aS haS C hC hImageS
local notation "xT" => cutNative YT KT hKT hSingT aT haT C hC hImageT
local notation "xS" => cutNative YS KS hKS hSingS aS haS C hC hImageS
local notation "kT" => cutHistory YT KT hKT hSingT aT haT C hC hImageT
local notation "kS" => cutHistory YS KS hKS hSingS aS haS C hC hImageS

private theorem closure_left : closure ((NC).openSet : Set Z.obj.left) ⊆ range (jT).hom.left.base :=
  fun _ hz => ((NC).closure_subset hz).1.1
private theorem closure_right : closure ((NC).openSet : Set Z.obj.left) ⊆ range (jS).hom.left.base :=
  fun _ hz => ((NC).closure_subset hz).1.2

local notation "clT" => closure_left YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ
local notation "clS" => closure_right YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ

/-- The literal actual left endpoint restriction, including the SAME old physical history. -/
def leftEndpoint : SourceReducedComplexSpace :=
  OriginalNativePrescribedOpenHistory.source (jT) (hjT) (NC).openSet (NC).compactClosure (clT) (kT)
def rightEndpoint : SourceReducedComplexSpace :=
  OriginalNativePrescribedOpenHistory.source (jS) (hjS) (NC).openSet (NC).compactClosure (clS) (kS)

def leftHistory : PhysicalHistory (NC).source
    (leftEndpoint YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ) :=
  OriginalNativePrescribedOpenHistory.history (jT) (hjT) (NC).openSet (NC).compactClosure (clT) (kT)
def rightHistory : PhysicalHistory (NC).source
    (rightEndpoint YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ) :=
  OriginalNativePrescribedOpenHistory.history (jS) (hjS) (NC).openSet (NC).compactClosure (clS) (kS)

local notation "L" => leftEndpoint YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ
local notation "R" => rightEndpoint YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ
local notation "lh" => leftHistory YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ
local notation "rh" => rightHistory YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ

/-- ORIGINAL profile equality derives the dimension alignment and all local
phase inputs; the FULL endpoint iso is an OUTPUT, never a supplied packet. -/
theorem exists_comparison (hProfile : (HT)=(HS)) : ∃ F : (R) ≅ (L),
    F.hom ≫ (lh).projection=(rh).projection := by
  have hd : OriginalNativeHSFactoryTerminalFrame.dimension YT KT hKT hSingT=
      OriginalNativeHSFactoryTerminalFrame.dimension YS KS hKS hSingS :=
    (OriginalNativeHSFactoryTerminalFrame.dimension_eq YT KT hKT hSingT).trans
      ((congrArg (fun H : ℕ → ℕ => H 1-1) hProfile).trans
        (OriginalNativeHSFactoryTerminalFrame.dimension_eq YS KS hKS hSingS).symm)
  have hRawS : ∀i,IsNativeWindowRecord ((wCS) i) ((rCS) i) (HT) :=
    (congrArg (fun H => ∀i,IsNativeWindowRecord ((wCS) i) ((rCS) i) H) hProfile.symm).mp
      (OriginalNativeHSBaseOpenWindows.native_record (wFS) (incS) (hincS) (rFS)
        (OriginalNativeHSFactoryTerminalFrame.native_record YS KS hKS hSingS))
  have hCovS : originalSingularHSThreshold (NS).source (HT) ⊆
      ⋃i,range ((wCS) i).toLocalEmbedding.toPoint :=
    (congrArg (fun H => originalSingularHSThreshold (NS).source H ⊆
      ⋃i,range ((wCS) i).toLocalEmbedding.toPoint) hProfile.symm).mp
      (cutCover YS KS hKS hSingS aS haS C hC hImageS)
  have hOffS : IsIsoOver (xS).q (originalSingularHSThreshold (NS).source (HT))ᶜ :=
    (congrArg (fun H => IsIsoOver (xS).q (originalSingularHSThreshold (NS).source H)ᶜ) hProfile.symm).mp
      (cutOff YS KS hKS hSingS aS haS C hC hImageS)
  exact compare_dimensions hd (jT) (jS) (hjT) (hjS) (NC).openSet (NC).compactClosure (clT) (clS)
    (wCT) (wCS) (rCT) (rCS) (HT)
    (OriginalNativeHSBaseOpenWindows.native_record (wFT) (incT) (hincT) (rFT)
      (OriginalNativeHSFactoryTerminalFrame.native_record YT KT hKT hSingT)) hRawS
    (eT) (eS) (OriginalNativeHSFactoryTerminalFrame.positive YT KT hKT hSingT)
    (OriginalNativeHSFactoryTerminalFrame.positive YS KS hKS hSingS)
    (sT) (sS) (xT) (xS) (kT) (kS)
    (cutProjection YT KT hKT hSingT aT haT C hC hImageT)
    (cutProjection YS KS hKS hSingS aS haS C hC hImageS)
    (cutTerminal YT KT hKT hSingT aT haT C hC hImageT)
    (cutTerminal YS KS hKS hSingS aS haS C hC hImageS)
    (cutCover YT KT hKT hSingT aT haT C hC hImageT) hCovS
    (cutOff YT KT hKT hSingT aT haT C hC hImageT) hOffS

/-- The actual endpoint map back to the SAME original factory endpoint. -/
def leftInclusion : (L) ⟶ OriginalNativeHSShadowPhaseFactory.source YT KT hKT hSingT :=
  OriginalNativePrescribedOpenHistory.sourceInclusion (jT) (hjT) (NC).openSet (NC).compactClosure (clT) (kT) ≫
    inclusion (OriginalNativeHSShadowPhaseFactory.source YT KT hKT hSingT)
      (preimageOpen (NT).openSet (OriginalNativeHSShadowPhaseFactory.history YT KT hKT hSingT).projection)
      (isCompact_closure_preimage (NT).openSet
        (OriginalNativeHSShadowPhaseFactory.history YT KT hKT hSingT).projection (NT).compactClosure
        (OriginalNativeHSShadowPhaseFactory.history YT KT hKT hSingT).singularModification.isProperMap)

def rightInclusion : (R) ⟶ OriginalNativeHSShadowPhaseFactory.source YS KS hKS hSingS :=
  OriginalNativePrescribedOpenHistory.sourceInclusion (jS) (hjS) (NC).openSet (NC).compactClosure (clS) (kS) ≫
    inclusion (OriginalNativeHSShadowPhaseFactory.source YS KS hKS hSingS)
      (preimageOpen (NS).openSet (OriginalNativeHSShadowPhaseFactory.history YS KS hKS hSingS).projection)
      (isCompact_closure_preimage (NS).openSet
        (OriginalNativeHSShadowPhaseFactory.history YS KS hKS hSingS).projection (NS).compactClosure
        (OriginalNativeHSShadowPhaseFactory.history YS KS hKS hSingS).singularModification.isProperMap)

theorem leftInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (leftInclusion YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion (jT) (hjT)
      (NC).openSet (NC).compactClosure (clT) (kT)) _ (inclusion_isOpenImmersion _ _ _)
theorem rightInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (rightInclusion YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion (jS) (hjS)
      (NC).openSet (NC).compactClosure (clS) (kS)) _ (inclusion_isOpenImmersion _ _ _)

theorem left_old_square : (lh).projection ≫ (NC).inclusion ≫ aT =
    leftInclusion YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ ≫
      (OriginalNativeHSShadowPhaseFactory.history YT KT hKT hSingT).projection ≫
        OriginalNativeHSShadowPhaseFactory.baseInclusion YT KT hKT hSingT := by
  exact paste_old_square _ _ _ _ _ _ _ _ _ _
    (OriginalNativePrescribedOpenHistory.projection_square (jT) (hjT) (NC).openSet (NC).compactClosure (clT) (kT))
    (OriginalNativeHSFactoryOverlapCut.toCommon_square YT KT hKT hSingT aT haT C hC hImageT)
    (OriginalNativePhysicalHistoryRestriction.projection_square
      (OriginalNativeHSShadowPhaseFactory.history YT KT hKT hSingT) (NT).openSet (NT).compactClosure)

theorem right_old_square : (rh).projection ≫ (NC).inclusion ≫ aS =
    rightInclusion YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ ≫
      (OriginalNativeHSShadowPhaseFactory.history YS KS hKS hSingS).projection ≫
        OriginalNativeHSShadowPhaseFactory.baseInclusion YS KS hKS hSingS := by
  exact paste_old_square _ _ _ _ _ _ _ _ _ _
    (OriginalNativePrescribedOpenHistory.projection_square (jS) (hjS) (NC).openSet (NC).compactClosure (clS) (kS))
    (OriginalNativeHSFactoryOverlapCut.toCommon_square YS KS hKS hSingS aS haS C hC hImageS)
    (OriginalNativePhysicalHistoryRestriction.projection_square
      (OriginalNativeHSShadowPhaseFactory.history YS KS hKS hSingS) (NS).openSet (NS).compactClosure)

/-- WHOLE inverse-open range in the actual original left factory endpoint. -/
theorem leftInclusion_range : range
    (leftInclusion YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ).hom.left.base =
    ((OriginalNativeHSShadowPhaseFactory.history YT KT hKT hSingT).projection ≫
      OriginalNativeHSShadowPhaseFactory.baseInclusion YT KT hKT hSingT).hom.left.base ⁻¹'
      (aT.hom.left.base '' ((NC).openSet : Set Z.obj.left)) :=
  endpoint_range YT KT hKT hSingT aT haT C hC hImageT (NC).openSet (NC).compactClosure (clT)

theorem rightInclusion_range : range
    (rightInclusion YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ).hom.left.base =
    ((OriginalNativeHSShadowPhaseFactory.history YS KS hKS hSingS).projection ≫
      OriginalNativeHSShadowPhaseFactory.baseInclusion YS KS hKS hSingS).hom.left.base ⁻¹'
      (aS.hom.left.base '' ((NC).openSet : Set Z.obj.left)) :=
  endpoint_range YS KS hKS hSingS aS haS C hC hImageS (NC).openSet (NC).compactClosure (clS)

/-- The comparison's forward map lies over the SAME actual common base. -/
def comparison (hProfile : (HT)=(HS)) : (R) ≅ (L) :=
  (exists_comparison YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ hProfile).choose

theorem comparison_projection (hProfile : (HT)=(HS)) :
    (comparison YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ hProfile).hom ≫
      (lh).projection=(rh).projection :=
  (exists_comparison YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ hProfile).choose_spec

theorem comparison_scalar (hProfile : (HT)=(HS)) :
    (comparison YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ hProfile).hom.hom.left ≫
      (L).obj.hom=(R).obj.hom :=
  Over.w (comparison YT YS KT KS hKT hKS hSingT hSingS aT aS haT haS C hC hImageT hImageS Ω hCΩ hProfile).hom.hom

/-- ANY two full native maps over this SAME computed common base agree;
no ambient off-carrier extension or clock equality is used. -/
theorem maps_eq_over_common_base (f g : (R) ⟶ (L))
    (hf : f ≫ (lh).projection=(rh).projection)
    (hg : g ≫ (lh).projection=(rh).projection) : f=g := by
  have hbase : ∀ z, (lh).projection.hom.left.base (f.hom.left.base z)=
      (lh).projection.hom.left.base (g.hom.left.base z) := fun z =>
    (congrArg (fun p : (R) ⟶ (NC).source => p.hom.left.base z) hf).trans
      (congrArg (fun p : (R) ⟶ (NC).source => p.hom.left.base z) hg).symm
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq f g
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    (lh).singularModification.isIsoOver_intrinsicRegularLocus
    f.hom.left.base.hom.continuous g.hom.left.base.hom.continuous hbase
    (rh).singularModification.dense_preimage_intrinsicRegularLocus
    (fun u hu => (congrArg (fun p : (R) ⟶ (NC).source => p.hom.left.base u) hf).symm ▸ hu)) z

end ActualPair
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSEqualProfilePhaseComparison
