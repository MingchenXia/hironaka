import Hironaka.Resolution.HironakaActualNativeSectionZeroHeadRecords

/-! Entire original controlled records on genuine smaller native reference
windows and the SAME actual original tails, with all pre-cut born slots kept. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionZeroTailSubwindows
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings GermIdealOrder GermIdealPullbackCalculus
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactStageKept CodimOneSupportAlong
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionCoefficientRecords HironakaDisjointNativeContactReference
  HironakaDisjointNativeReferenceWindow
  HironakaSmoothSubmersionCoefficientIdeals HironakaActualRawRecordPullbacks
  HironakaSmoothSubmersionOrderedChoiceImageTrace

variable {n k : ℕ} {X : CMfd.{0} n} {hk : k≤n} {W : Set X}
  {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

/-- Literal smaller native source inclusion; no closed-image assertion. -/
def subwindowSource (O : Opens X) (B : Opens (nativeManifold hk W hW))
    (hBO : (B : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (O : Set X)) : B→O:=
  fun p=>⟨p.val.val,hBO p.property⟩

/-- Literal endpoint on the SAME actual original restricted histories. -/
def subwindowEndpoint (h : Lift hk W hWc hW E T V hVc hV Q)
    (O : Opens X) (B : Opens (nativeManifold hk W hW))
    (hBO : (B : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (O : Set X)) :
    openPreimage Q B → openPreimage T O:=fun p=>⟨p.val.val,by
      change T.proj p.val.val∈O
      rw [h.square p.val]
      exact hBO p.property⟩

theorem subwindowSource_contMDiff (O : Opens X) (B : Opens (nativeManifold hk W hW))
    (hBO : (B : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (O : Set X)) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ (subwindowSource O B hBO) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  apply (ContMDiff.subtypeVal_comp_iff O _).mp
  exact (contMDiff_val hk hW).comp contMDiff_subtype_val

theorem subwindowEndpoint_contMDiff (h : Lift hk W hWc hW E T V hVc hV Q)
    (O : Opens X) (B : Opens (nativeManifold hk W hW))
    (hBO : (B : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (O : Set X)) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ (subwindowEndpoint h O B hBO) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  apply (ContMDiff.subtypeVal_comp_iff (openPreimage T O) _).mp
  exact (contMDiff_val hk hV).comp contMDiff_subtype_val

/-- Exact whole initial and endpoint records for arbitrary SMALLER native
windows on the SAME actual histories. Every ordered old/born slot is kept. -/
theorem actual_subwindow_records (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (O : Opens X) (B : Opens (nativeManifold hk W hW))
    (hBO : (B : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (O : Set X))
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x a,M.ideal.mem x a → HolomorphicAt n a x) :
    markedPullback (m:=k) (subwindowSource O B hBO)
        (MarkedIdeal.pullback (Subtype.val : O→X) M)=
      MarkedIdeal.pullback (Subtype.val : B→nativeManifold hk W hW) (nativePullback hk W hW M) ∧
    geoTransformAlong
        (MarkedIdeal.pullback (Subtype.val : B→nativeManifold hk W hW) (nativePullback hk W hW M))
        (restrict B Q)=
      markedPullback (m:=k) (subwindowEndpoint h O B hBO)
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→X) M) (restrict O T)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hS:=subwindowSource_contMDiff O B hBO
  have hEnd:=subwindowEndpoint_contMDiff h O B hBO
  constructor
  · apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · simp only [nativePullback,MarkedIdeal.pullback,markedPullback,List.map_map,Function.comp_def]
      rfl
    · change GermIdeal.pullback (m:=k) (subwindowSource O B hBO)
        (GermIdeal.pullback (m:=n) (Subtype.val : O→X) M.ideal)=
        GermIdeal.pullback (m:=k) (Subtype.val : B→nativeManifold hk W hW)
          (GermIdeal.pullback (m:=k) (Subtype.val : W→X) M.ideal)
      rw [←whole_pullback_comp contMDiff_subtype_val hS M.ideal hhol,
        ←whole_pullback_comp (contMDiff_val hk hW) contMDiff_subtype_val M.ideal hhol]
      rfl
    · rfl
  · rw [geoTransformAlong_restrict_of_hhol (nativePullback hk W hW M) (fun _ _ ha=>ha.1) B Q,
      h.whole_records hn hE hTrans M hME hMN hhol,
      geoTransformAlong_restrict_of_hhol M hhol O T]
    have hCurrent:=holomorphic_geoTransformAlong M hhol T
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · simp only [nativePullback,MarkedIdeal.pullback,markedPullback,List.map_map,Function.comp_def]
      rfl
    · change GermIdeal.pullback (m:=k)
        (Subtype.val : openPreimage Q B→nativeManifold hk V hV)
        (GermIdeal.pullback (m:=k) (Subtype.val : V→Y) (geoTransformAlong M T).ideal)=
        GermIdeal.pullback (m:=k) (subwindowEndpoint h O B hBO)
          (GermIdeal.pullback (m:=n) (Subtype.val : openPreimage T O→Y) (geoTransformAlong M T).ideal)
      rw [←whole_pullback_comp (contMDiff_val hk hV) contMDiff_subtype_val _ hCurrent,
        ←whole_pullback_comp contMDiff_subtype_val hEnd _ hCurrent]
      rfl
    · rfl

/-- A nonempty SMALLER window inside any prescribed native neighbourhood
of the SAME original zero head, and ENTIRE fixed-contact records along
its genuine original tail. The independent native choice is not equated. -/
theorem original_zero_contact_subwindow_tail
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hME : M.E=E) (hMN : M.N⊆W)
    (hd : 1≤M.d) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hT : IsGeoTestTower (barMarked M) T)
    (p : nativeManifold hk V hV) (hp : p.val∈(geoTransformAlong (barMarked M) T).cosupp)
    (hl : level M T p.val=0)
    (hZ : p.val∉codimOnePartAlong (geoTransformAlong (barMarked M) T).N
      (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d)
    (C : Opens (nativeManifold hk V hV)) (hpC : p∈C)
    {Z : CMfd.{0} n}{S : BlowupTower Y Z}{V' : Set Z}{hV'c : IsClosed V'}
    {hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
    {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')}
    (hTail : Lift hk V hVc hV (boundary E T) S V' hV'c hV' R) :
    ∃(B : Opens (nativeManifold hk V hV)),p∈B ∧ B≤C ∧
      ∃hBA : (B : Set (nativeManifold hk V hV))⊆
        (Subtype.val : V→Y) ⁻¹' (maskB M T p.val : Set Y),
      geoTransformAlong
        (contactMarkedKept (nativePullback hk W hW M)
          ((tangentChoice M (T.proj p.val)).2 ∘ (Subtype.val : W→X)) Q B) (restrict B R)=
        markedPullback (m:=k) (subwindowEndpoint hTail (maskB M T p.val) B hBA)
          (geoTransformAlong (lowerMarkedB M T p.val) (restrict (maskB M T p.val) S)) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let AM:=maskB M T p.val
  let Atrace : Opens (nativeManifold hk V hV):=
    ⟨(Subtype.val : V→Y) ⁻¹' (AM : Set Y),AM.isOpen.preimage continuous_subtype_val⟩
  let B:=Atrace⊓C
  have hpA : p.val∈AM:=mem_maskB M hM hd hmax T hT hp hl hZ
  have hBA : (B : Set (nativeManifold hk V hV))⊆(Subtype.val : V→Y) ⁻¹' (AM : Set Y):=
    fun _ hz=>hz.1
  refine ⟨B,⟨hpA,hpC⟩,fun _ hz=>hz.2,hBA,?_⟩
  let u:=(tangentChoice M (T.proj p.val)).2
  let A:=contactHead M u T
  have hAE : A.E=boundary E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=(⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) hME T
  have hAN : A.N⊆V:=by
    let L : MarkedIdeal n X:=⟨M.N∩{x | u x=0},E,IdealWeightPowers.unitIdeal n X,1⟩
    have hs:=HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h L (fun _ hz=>hMN hz.1)
    rw [N_geoTransformAlong] at hs
    exact hs
  have hAH : ∀y a,A.ideal.mem y a → HolomorphicAt n a y:=fun _ _ ha=>ha.1
  obtain ⟨hEC,hTC⟩:=h.geometry hn hE hTrans
  have hWhole:=(actual_subwindow_records hTail hn hEC hTC AM B hBA A hAE hAN hAH).2
  have hhol : ∀x a,M.ideal.mem x a → HolomorphicAt n a x:=
    fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent ha
  rw [native_contact_head h hn hE hTrans M hME hMN hhol u] at hWhole
  exact hWhole

end
end Hironaka.HironakaActualNativeSectionZeroTailSubwindows
