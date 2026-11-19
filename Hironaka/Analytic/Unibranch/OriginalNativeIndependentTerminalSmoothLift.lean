import Hironaka.Analytic.Unibranch.OriginalNativeIndependentStrictSmoothLift
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothPhaseLiftLaws
import Hironaka.Resolution.HironakaOriginalTerminalOpenComparison

/-! Actual per-phase smooth EXISTS from independently chosen WHOLE terminal inputs.
Blueprint FIRST: original-native-independent-terminal-smooth-lift.tex.
No comparison/lift packet or powered native state is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeIndependentTerminalSmoothLift
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaHolomorphicJetChartInvariance
  HironakaG11VanishingWindows HironakaG11PresLineState HironakaG11PresTowerState
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  ResolutionInvariantSpec MarkedIdealBiholomorphism HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCoefficientIdeals
  OriginalNativeProductWindow OriginalNativeProductIndependentRecord OriginalNativeProductSelectedState
  OriginalNativeSmoothGivenTargetWindow HironakaG1IndependentNativeSmoothCanonicalHistory
  OriginalNativeTerminalPhaseComparison OriginalNativeSmoothPhaseLiftLaws
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothAmbientConverse
  HironakaSmoothSubmersionComposition HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaOriginalTerminalOpenComparison HironakaG1OriginalUnequalMarkCanonical
  HironakaActualPowerBoundaryExponents HironakaG8LocalPower HironakaG8LocalHistory HironakaBaseChange
open scoped ProductComplexManifold

section ChosenWindow
variable {X Y : SourceReducedComplexSpace} {f : X⟶Y} {x : X.obj.left}
  {e : LocalEmbedding Y} {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
  {d : DimEmbedding X (w.target.dim+w.rank)} {c : d.carrier}
  (M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint d c)

/-- Actual open of the ORIGINAL chosen source ambient. -/
abbrev sourceOpen : Opens d.ambient := opensWithin d.ambient M.targetOpen

abbrev sourcePhi : type_of% (opensWithinDiffeo d.ambient M.targetOpen M.target_subset).symm :=
  (opensWithinDiffeo d.ambient M.targetOpen M.target_subset).symm

/-- Same exact carrier expression as the actual terminal base isomorphism. -/
abbrev sourceCarrier : Set (CMfd.of (n := w.target.dim+w.rank) (sourceOpen w M)) :=
  (sourcePhi w M) ⁻¹' M.targetCarrier

theorem selected_source_carrier_eq : sourceCarrier w M=
    (Subtype.val : sourceOpen w M → d.ambient) ⁻¹' d.carrier := rfl

private theorem source_analytic : IsComplexAnalyticSubset (n := w.target.dim+w.rank) (sourceCarrier w M) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (sourcePhi w M).contMDiff
    (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic

variable {Z : CMfd.{0} (w.target.dim+w.rank)} (S : BlowupTower (CMfd.of (n := w.target.dim+w.rank) d.ambient) Z)

/-- The literal inverse-open endpoint of SAME physical source history S. -/
abbrev sourceEndpoint : SourceReducedComplexSpace :=
  strictSpace (restrict (sourceOpen w M) S) (sourceCarrier w M) (source_analytic w M)

theorem sourceCarrier_preimage :
    strictTransform (w.target.dim+w.rank) (restrict (sourceOpen w M) S).proj (sourceCarrier w M)=
      (Subtype.val : openPreimage S (sourceOpen w M) → Z) ⁻¹'
        strictTransform (w.target.dim+w.rank) S.proj d.carrier := by
  rw [selected_source_carrier_eq]
  exact strictTransform_preimage_eq S.contMDiff_proj (restrict (sourceOpen w M) S).contMDiff_proj
    (isOpenHoloEmbedding_val (sourceOpen w M))
    (isOpenHoloEmbedding_val (openPreimage S (sourceOpen w M)))
    (fun y=>(proj_restrict (sourceOpen w M) S y).symm) d.carrier

def sourceBaseInclusion : ofClosedAnalytic (sourceCarrier w M) (source_analytic w M) ⟶
    chartSpace d.toLocalEmbedding :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (n := w.target.dim+w.rank) (m := w.target.dim+w.rank)
      (M := sourceOpen w M) (N := d.ambient) (f := Subtype.val)
      contMDiff_subtype_val (fun _ hy=>hy))
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hy=>hy)))

abbrev sourceLocalProjection :=
  OriginalNativeTerminalPhaseComparison.projection (n := w.target.dim+w.rank)
    (X := CMfd.of (n := w.target.dim+w.rank) (sourceOpen w M))
    (Y := CMfd.of (n := w.target.dim+w.rank) (openPreimage S (sourceOpen w M)))
    (restrict (sourceOpen w M) S) (sourceCarrier w M) (source_analytic w M)

private theorem source_original_mapsTo (z : openPreimage S (sourceOpen w M))
    (hz : z∈strictTransform (w.target.dim+w.rank) (restrict (sourceOpen w M) S).proj (sourceCarrier w M)) :
    S.proj z.val∈d.carrier := by
  have hy : z.val∈strictTransform (w.target.dim+w.rank) S.proj d.carrier :=
    (Set.ext_iff.mp (sourceCarrier_preimage w M S) z).mp hz
  exact (closure_minimal sdiff_subset
    (d.toLocalEmbedding.analytic.isClosed.preimage S.contMDiff_proj.continuous)) hy

def sourceOriginalProjection : sourceEndpoint w M S ⟶ X :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (n := w.target.dim+w.rank) (m := w.target.dim+w.rank)
      (M := openPreimage S (sourceOpen w M)) (N := d.ambient)
      (f := fun z=>S.proj z.val) (S.contMDiff_proj.comp contMDiff_subtype_val)
      (source_original_mapsTo w M S) ≫ d.toLocalEmbedding.map)
    ((Category.assoc _ _ _).trans ((congrArg (fun k=>actualSubspaceMap
      (S.contMDiff_proj.comp contMDiff_subtype_val) (source_original_mapsTo w M S) ≫ k)
      d.toLocalEmbedding.overPoint).trans
        (actualSubspaceMap_point (S.contMDiff_proj.comp contMDiff_subtype_val)
          (source_original_mapsTo w M S)))))

variable (J : MarkedIdeal (w.target.dim+w.rank) (CMfd.of (n := w.target.dim+w.rank) d.ambient))

theorem selected_source_record_eq (hJ : IsInvDomain (w.target.dim+w.rank) J) :
    MarkedIdeal.pullback (sourcePhi w M) (ownRestrictedRecord w M J)=
      MarkedIdeal.pullback (Subtype.val : sourceOpen w M → d.ambient) J := by
  change markedPullback (sourcePhi w M) (markedPullback (Opens.inclusion M.target_subset) J)=_
  exact (whole_markedPullback_comp (contMDiff_inclusion M.target_subset)
    (sourcePhi w M).contMDiff J hJ.isWellFormed.isCoherent).symm

private theorem own_native {Hs : ℕ→ℕ} (hJ : IsInvDomain (w.target.dim+w.rank) J)
    (hJState : NativeHSState J d.carrier Hs) :
    NativeHSState (ownRestrictedRecord w M J) M.targetCarrier Hs := by
  let Ψ:=opensWithinDiffeo d.ambient M.targetOpen M.target_subset
  have heq : ownRestrictedRecord w M J=MarkedIdeal.pullback Ψ
      (MarkedIdeal.pullback (Subtype.val : sourceOpen w M → d.ambient) J) :=
    whole_markedPullback_comp contMDiff_subtype_val Ψ.contMDiff J hJ.isWellFormed.isCoherent
  rw [heq]
  exact NativeHSState.pullback (X' := CMfd.of (n := w.target.dim+w.rank) M.targetOpen) Ψ
    (hJState.restrict (sourceOpen w M))

private theorem iso_smooth {A B : SourceReducedComplexSpace} (a : A≅B) : IsSmoothMorphism a.hom :=
  isSmoothMorphism_of_isOpenImmersion a.hom (by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft a).hom
    infer_instance)

variable {Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient)}
  {D : CMfd.{0} e.dim} {T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D}
  (A : IndependentCanonicalHistory w M Q J T)
  (hJ : IsInvDomain (w.target.dim+w.rank) J) {Hs : ℕ→ℕ} (hJState : NativeHSState J d.carrier Hs)
  (hSCan : IsCanonical J ((canonicalInvariant (w.target.dim+w.rank)).inv J) S)
  (hSRes : IsGeoResolution J S)
  (hQ : IsInvDomain e.dim Q) {H : ℕ→ℕ} (hState : NativeHSState Q e.carrier H)
  (hTCan : IsCanonical Q ((canonicalInvariant e.dim).inv Q) T) (hTRes : IsGeoResolution Q T)

private theorem actual_base_submersion {n m : ℕ} {B D : CMfd.{0} n} {C E : CMfd.{0} m}
    {b : C→B} {g : E→D} {S : BlowupTower C E} {U : BlowupTower B D}
    (h : HironakaSmoothSubmersionCartesianTower.IsActualTowerPullback b S U g) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b := by
  induction h with
  | refl hf=>exact hf
  | step _ _ _ _ ih=>exact ih

include A in
private theorem initial_submersion :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (w.target.dim+w.rank)) 𝓘(ℂ,ComplexModel e.dim) ∞
      ((ownBaseMap w M) ∘ sourcePhi w M) :=
  isSubmersion_composition (X := CMfd.of (n := e.dim) e.ambient)
    (Y := CMfd.of (n := w.target.dim+w.rank) M.targetOpen)
    (Z := CMfd.of (n := w.target.dim+w.rank) (sourceOpen w M))
    (actual_base_submersion A.cartesian)
    (isSubmersion_biholomorphism (D := CMfd.of (n := w.target.dim+w.rank) (sourceOpen w M))
      (C := CMfd.of (n := w.target.dim+w.rank) M.targetOpen) (sourcePhi w M))

private theorem initial_preimage : sourceCarrier w M=
    ((ownBaseMap w M) ∘ sourcePhi w M) ⁻¹' e.carrier := by
  change (sourcePhi w M) ⁻¹' M.targetCarrier=_
  rw [OriginalNativeIndependentStrictSmoothLift.initial_carrier_preimage w M]
  rfl

def initialBaseMap : ofClosedAnalytic (sourceCarrier w M) (source_analytic w M) ⟶ chartSpace e :=
  subspaceMorphism (initial_submersion w M J A) (source_analytic w M) e.analytic (initial_preimage w M)

theorem initialBaseMap_isSmooth : IsSmoothMorphism (initialBaseMap w M J A) :=
  isSmoothMorphism_subspaceMorphism (initial_submersion w M J A)
    (source_analytic w M) e.analytic (initial_preimage w M)

include J A hTRes in
private theorem intermediate_resolution : IsGeoResolution (ownRestrictedRecord w M J) A.tower := by
  refine ⟨(canonicalInvariant (w.target.dim+w.rank)).isInvValue.isGeoTestTower_of_isCanonical
    A.domain A.tower A.canonical,?_⟩
  rw [A.cosupp,hTRes.2,preimage_empty]

include J hJ hSCan hSRes in
private theorem source_terminal_inputs :
    IsCanonical (MarkedIdeal.pullback (sourcePhi w M) (ownRestrictedRecord w M J))
      ((canonicalInvariant (w.target.dim+w.rank)).inv
        (MarkedIdeal.pullback (sourcePhi w M) (ownRestrictedRecord w M J))) (restrict (sourceOpen w M) S) ∧
    IsGeoResolution (MarkedIdeal.pullback (sourcePhi w M) (ownRestrictedRecord w M J))
      (restrict (sourceOpen w M) S) := by
  have hs:=original_terminal_open_history_data J hJ S hSCan hSRes (sourceOpen w M)
  rw [selected_source_record_eq w M J hJ]
  exact hs.2

include J A hJ hSCan hSRes hTRes in
private theorem exists_source_comparison :
    ∃ cmp : sourceEndpoint w M S ≅ strictSpace A.tower M.targetCarrier
        (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic,
      ∀z,A.tower.proj (cmp.hom.hom.left.base z).val=
        sourcePhi w M ((restrict (sourceOpen w M) S).proj z.val) := by
  have hs:=source_terminal_inputs w M S J hJ hSCan hSRes
  have hr:=intermediate_resolution w M J A hTRes
  let cmp:=comparison (X := CMfd.of (n := w.target.dim+w.rank) M.targetOpen)
    (X' := CMfd.of (n := w.target.dim+w.rank) (sourceOpen w M)) (ownRestrictedRecord w M J) A.domain (sourcePhi w M)
    (restrict (sourceOpen w M) S) A.tower hs.1 A.canonical hs.2 hr M.targetCarrier
    (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic
  refine ⟨cmp,?_⟩
  intro z
  change A.tower.proj (ambientComparison (ownRestrictedRecord w M J) A.domain (sourcePhi w M)
    (restrict (sourceOpen w M) S) A.tower hs.1 A.canonical hs.2 hr z.val)=_
  exact ambientComparison_proj (X := CMfd.of (n := w.target.dim+w.rank) M.targetOpen)
    (X' := CMfd.of (n := w.target.dim+w.rank) (sourceOpen w M)) (ownRestrictedRecord w M J) A.domain (sourcePhi w M)
    (restrict (sourceOpen w M) S) A.tower hs.1 A.canonical hs.2 hr z.val

include J A hJ hJState hQ hState hTCan in
private theorem source_alignment :
    ∃ eA : OriginalNativeIndependentStrictSmoothLift.sourceStrictSpace w M A hQ hState hTCan ≅
        strictSpace A.tower M.targetCarrier
          (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic,
      eA.hom ≫ projection A.tower M.targetCarrier
        (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic=
      OriginalNativeIndependentStrictSmoothLift.sourceProjection w M A hQ hState hTCan := by
  let R:=ownRestrictedRecord w M J
  have hOwnState : NativeHSState R M.targetCarrier Hs := own_native w M J hJ hJState
  have hOwnTest : IsGeoTestTower R A.tower :=
    (canonicalInvariant (w.target.dim+w.rank)).isInvValue.isGeoTestTower_of_isCanonical A.domain A.tower A.canonical
  let eA:=iteratedEndpointIso R A.domain M.targetCarrier
    (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic hOwnState.hsTowerState A.tower hOwnTest
  exact ⟨eA,(iteratedProjection_eq_of_pointwise R A.domain M.targetCarrier
    (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic
    hOwnState.hsTowerState A.tower hOwnTest
    (OriginalNativeIndependentStrictSmoothLift.sourceProjection w M A hQ hState hTCan)
    (fun _=>rfl)).symm⟩

include hQ hState hTCan in
private theorem target_alignment :
    ∃ eT : OriginalNativeIndependentStrictSmoothLift.targetStrictSpace hQ hState hTCan ≅
        strictSpace T e.carrier e.analytic,
      eT.hom ≫ projection T e.carrier e.analytic=
        OriginalNativeIndependentStrictSmoothLift.targetProjection hQ hState hTCan := by
  have hTest : IsGeoTestTower Q T :=
    (canonicalInvariant e.dim).isInvValue.isGeoTestTower_of_isCanonical hQ T hTCan
  let eT:=iteratedEndpointIso Q hQ e.carrier e.analytic hState.hsTowerState T hTest
  exact ⟨eT,(iteratedProjection_eq_of_pointwise Q hQ e.carrier e.analytic hState.hsTowerState T hTest
    (OriginalNativeIndependentStrictSmoothLift.targetProjection hQ hState hTCan) (fun _=>rfl)).symm⟩

include J A hJ hJState hSCan hSRes hQ hState hTCan hTRes in
private theorem map_from_chosen_source :
    ∃ g : sourceEndpoint w M S ⟶ strictSpace T e.carrier e.analytic,
      IsSmoothMorphism g ∧
      g ≫ projection T e.carrier e.analytic=sourceLocalProjection w M S ≫ initialBaseMap w M J A ∧
      g ≫ projection T e.carrier e.analytic ≫ chartInclusion e=sourceOriginalProjection w M S ≫ f := by
  obtain ⟨cmp,hCmp⟩:=exists_source_comparison w M S J A hJ hSCan hSRes hTRes
  obtain ⟨eA,hApr⟩:=source_alignment w M J A hJ hJState hQ hState hTCan
  obtain ⟨eT,hTpr⟩:=target_alignment hQ hState hTCan
  let g : sourceEndpoint w M S ⟶ strictSpace T e.carrier e.analytic :=
    cmp.hom ≫ eA.inv ≫
      OriginalNativeIndependentStrictSmoothLift.nativeLift w M A hQ hState hTCan ≫ eT.hom
  have hAprInv : eA.inv ≫ OriginalNativeIndependentStrictSmoothLift.sourceProjection w M A hQ hState hTCan=
      projection A.tower M.targetCarrier
        (d.toLocalEmbedding.restrict M.targetOpen M.target_subset).analytic := by
    exact (congrArg (fun k=>eA.inv ≫ k) hApr.symm).trans (eA.inv_hom_id_assoc _)
  have hProj : g ≫ projection T e.carrier e.analytic=
      sourceLocalProjection w M S ≫ initialBaseMap w M J A := by
    apply morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    let zA := eA.inv.hom.left.base (cmp.hom.hom.left.base z)
    have ht := congrArg (fun k=>((k.hom.left.base
      ((OriginalNativeIndependentStrictSmoothLift.nativeLift w M A hQ hState hTCan).hom.left.base zA))).val) hTpr
    have hs := congrArg (fun k=>(k.hom.left.base (cmp.hom.hom.left.base z)).val) hAprInv
    calc
      _=T.proj (A.lift zA.val) := ht
      _=ownBaseMap w M (A.tower.proj zA.val) := A.cartesian.proj_comm zA.val
      _=ownBaseMap w M (A.tower.proj (cmp.hom.hom.left.base z).val) := congrArg (ownBaseMap w M) hs
      _=ownBaseMap w M (sourcePhi w M ((restrict (sourceOpen w M) S).proj z.val)) :=
        congrArg (ownBaseMap w M) (hCmp z)
  refine ⟨g,?_,hProj,?_⟩
  · exact isSmoothMorphism_comp cmp.hom _ (iso_smooth cmp)
      (isSmoothMorphism_comp eA.inv _ (iso_smooth eA.symm)
        (isSmoothMorphism_comp _ eT.hom
          (OriginalNativeIndependentStrictSmoothLift.nativeLift_isSmooth w M A hQ hState hTCan)
          (iso_smooth eT)))
  · apply morphism_eq_of_pointwise_eq
    intro z
    let p := (sourceLocalProjection w M S).hom.left.base z
    let q : (OriginalNativeIndependentStrictSmoothLift.sourceInitialSpace w M).obj.left :=
      ⟨sourcePhi w M p.val,p.property⟩
    have h := congrArg (fun k=>k.hom.left.base q)
      (OriginalNativeIndependentStrictSmoothLift.initial_original_square w M A)
    have hp := congrArg (fun k=>k.hom.left.base z) hProj
    calc
      _=e.toPoint ((initialBaseMap w M J A).hom.left.base p) := congrArg e.toPoint hp
      _=f.hom.left.base ((chartInclusion
          (d.toLocalEmbedding.restrict M.targetOpen M.target_subset)).hom.left.base q) := h
      _=_ := by
        apply congrArg f.hom.left.base
        apply congrArg d.toLocalEmbedding.toPoint
        apply Subtype.ext
        exact proj_restrict (sourceOpen w M) S z.val

end ChosenWindow

/-- Retype the SAME actual source endpoint along the derived dimension equality. -/
def castEndpoint {N L : ℕ} (h : N=L) (Z : CMfd.{0} N) : CMfd.{0} L := by
  cases h
  exact Z

def castTower {X : SourceReducedComplexSpace} {N L : ℕ} (h : N=L) (d : DimEmbedding X N)
    {Z : CMfd.{0} N} (S : BlowupTower (CMfd.of (n := N) d.ambient) Z) :
    BlowupTower (CMfd.of (n := L) (d.cast h).ambient) (castEndpoint h Z) := by
  cases h
  exact S


/-- Actual chosen RAW inputs and TWO whole positive-power terminal histories
construct the genuine local native smooth arrow. No intermediate packet is input. -/
theorem exists_independent_terminal_smooth_lift
    {X Y : SourceReducedComplexSpace} (f : X⟶Y) (x : X.obj.left) (hsm : IsSmoothAt f x)
    (e : LocalEmbedding Y) (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient))
    (hQ : IsInvDomain e.dim Q) (hE : Q.E=[]) {H : ℕ→ℕ} (hState : NativeHSState Q e.carrier H)
    (he : e.dim=H 1-1) (a : e.carrier) (ha : e.toPoint a=f.hom.left.base x) (haQ : a.val∈Q.cosupp)
    (V : Opens X.obj.left) (hxV : x∈V)
    {N : ℕ} (d : DimEmbedding X N) (c : d.carrier) (hc : d.toLocalEmbedding.toPoint c=x)
    (J : MarkedIdeal N (CMfd.of (n := N) d.ambient))
    {Hs : ℕ→ℕ} (hJ : IsInvDomain N J) (hJE : J.E=[]) (hJState : NativeHSState J d.carrier Hs)
    (hJc : c.val∈J.cosupp) (hd : N=Hs 1-1)
    {C : CMfd.{0} N} (S : BlowupTower (CMfd.of (n := N) d.ambient) C)
    {D : CMfd.{0} e.dim} (T : BlowupTower (CMfd.of (n := e.dim) e.ambient) D)
    (p q : ℕ) (hp : 1≤p) (hq : 1≤q)
    (hSCan : IsCanonical (powerMarked J p) ((canonicalInvariant N).inv (powerMarked J p)) S)
    (hSRes : IsGeoResolution (powerMarked J p) S)
    (hTCan : IsCanonical (powerMarked Q q) ((canonicalInvariant e.dim).inv (powerMarked Q q)) T)
    (hTRes : IsGeoResolution (powerMarked Q q) T) :
    ∃ w : GivenTargetWindow f x e V,∃ hDim : N=w.target.dim+w.rank,
      ∃ M : ProductRecordModel w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint
        (d.cast hDim) (castWindowPoint hDim d c),
      ∃ A : IndependentCanonicalHistory w M Q (castWindowRecord hDim d J) T,
      ∃ g : sourceEndpoint w M (castTower hDim d S) ⟶ strictSpace T e.carrier e.analytic,
        IsSmoothMorphism (initialBaseMap w M (castWindowRecord hDim d J) A) ∧ IsSmoothMorphism g ∧
        g ≫ projection T e.carrier e.analytic=
          sourceLocalProjection w M (castTower hDim d S) ≫ initialBaseMap w M (castWindowRecord hDim d J) A ∧
        g ≫ projection T e.carrier e.analytic ≫ chartInclusion e=
          sourceOriginalProjection w M (castTower hDim d S) ≫ f ∧
        g.hom.left ≫ (strictSpace T e.carrier e.analytic).obj.hom=
          (sourceEndpoint w M (castTower hDim d S)).obj.hom := by
  have hSCanRaw := (canonicalInvariant_isCanonical_power_iff J hJ p hp S).mpr hSCan
  have hTCanRaw := (canonicalInvariant_isCanonical_power_iff Q hQ q hq T).mpr hTCan
  have hSResRaw : IsGeoResolution J S :=
    ((locEquiv_powerMarked (κ := Kinds.wp) rfl J hJ hp).wEquiv.isGeoResolution_iff S).mpr hSRes
  have hTResRaw : IsGeoResolution Q T :=
    ((locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hq).wEquiv.isGeoResolution_iff T).mpr hTRes
  obtain ⟨w,hDim,M,hA,_⟩:=exists_independent_native_smooth_canonical_history f x hsm e Q hQ hE hState
    he a ha haQ V hxV d c hc J hJ hJE hJState hJc hd T hTCanRaw
  change N=w.target.dim+w.rank at hDim
  refine ⟨w,hDim,M,?_⟩
  cases hDim
  obtain ⟨A⟩:=hA
  obtain ⟨g,hg,hLocal,hSquare⟩:=map_from_chosen_source w M S J A hJ hJState hSCanRaw hSResRaw
    hQ hState hTCanRaw hTResRaw
  exact ⟨A,g,initialBaseMap_isSmooth w M J A,hg,hLocal,hSquare,Over.w g.hom⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeIndependentTerminalSmoothLift
