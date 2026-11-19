import Hironaka.Resolution.HironakaActualNativeSectionCoefficientRecords
import Hironaka.Resolution.HironakaDisjointNativeReferenceWindow
import Hironaka.Invariant.ContactStageKept

/-! The SAME original function and complete kept contact records at original
native heads and actual reference opens. No numerical or canonicality certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointNativeContactReference
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower HomogenizedIdealAlong StepOneValue CoefficientIdealRestriction
  NormalCrossings GermIdealPullbackCalculus RelativePrincipalizationSpan IdealWeightPowers
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionCoefficientRecords HironakaActualRawRecordPullbacks
  HironakaDisjointNativeReferenceWindow HironakaSmoothSubmersionCoefficientIdeals
  ContactStageKept SubmanifoldChartedSpace HironakaSmoothSubmersionOrderedChoiceImageTrace

/-- The original whole contact-head record, with its entire boundary kept. -/
def contactHead {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (u : X → ℂ) (T : BlowupTower X Y) : MarkedIdeal n Y :=
  withN (coeffMarkedAlong (geoTransformAlong (barMarked M) T))
    (strictAlong T (M.N∩{x | u x=0}))

variable {n k : ℕ} {X : CMfd.{0} n} {hk : k≤n} {W : Set X}
  {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n := n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

/-- The SAME original contact function gives an entire native contact-head
record equality, without tangent, Test, CAN, domain or comparison premises. -/
theorem native_contact_head (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) (u : X → ℂ) :
    nativePullback hk V hV (contactHead M u T)=
      contactHead (nativePullback hk W hW M) (u∘Subtype.val) Q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let A : MarkedIdeal n X := ⟨M.N∩{x | u x=0},E,unitIdeal n X,1⟩
  have hRec := h.whole_records hn hE hTrans A rfl (fun _ hx => hMN hx.1) (fun _ _ hg => hg)
  have hCarrier := congrArg (fun K : MarkedIdeal k (nativeManifold hk V hV) => K.N) hRec
  change (geoTransformAlong (nativePullback hk W hW A) Q).N=
    (Subtype.val : V → Y) ⁻¹' (geoTransformAlong A T).N at hCarrier
  rw [N_geoTransformAlong,N_geoTransformAlong] at hCarrier
  change strictAlong Q ((nativePullback hk W hW M).N∩{p | u p.val=0})=
    (Subtype.val : V → Y) ⁻¹' strictAlong T (M.N∩{x | u x=0}) at hCarrier
  have hBar := nativePullback_barMarked hk hW M hMN hhol
  have hCurrentBar : nativePullback hk V hV (geoTransformAlong (barMarked M) T)=
      geoTransformAlong (barMarked (nativePullback hk W hW M)) Q := by
    rw [←h.whole_records hn hE hTrans (barMarked M) hME hMN (fun _ _ hg => hg.1),hBar]
  have hCoeff := nativePullback_coeffMarkedAlong hk hV (geoTransformAlong (barMarked M) T)
    (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h (barMarked M) hMN)
    (holomorphic_geoTransformAlong (barMarked M) (fun _ _ hg => hg.1) T)
  rw [hCurrentBar] at hCoeff
  change withN (nativePullback hk V hV (coeffMarkedAlong (geoTransformAlong (barMarked M) T)))
      ((Subtype.val : V → Y) ⁻¹' strictAlong T (M.N∩{x | u x=0}))=
    withN (coeffMarkedAlong (geoTransformAlong (barMarked (nativePullback hk W hW M)) Q))
      (strictAlong Q ((nativePullback hk W hW M).N∩{p | u p.val=0}))
  rw [hCoeff]
  exact congrArg (withN (coeffMarkedAlong (geoTransformAlong
    (barMarked (nativePullback hk W hW M)) Q))) hCarrier.symm

private theorem contact_head_facts (h : Lift hk W hWc hW E T V hVc hV Q)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W) (u : X → ℂ) :
    (contactHead M u T).N⊆V ∧ (contactHead M u T).E=boundary E T ∧
      ∀y g,(contactHead M u T).ideal.mem y g → HolomorphicAt n g y := by
  refine ⟨?_,?_,fun _ _ hg => hg.1⟩
  · let A : MarkedIdeal n X := ⟨M.N∩{x | u x=0},E,unitIdeal n X,1⟩
    have hs := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h A (fun _ hx => hMN hx.1)
    rw [N_geoTransformAlong] at hs
    exact hs
  · change (geoTransformAlong (barMarked M) T).E=boundary E T
    exact MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked M) (𝔫 := (⟨univ,E,unitIdeal n X,1⟩ : MarkedIdeal n X)) hME T

/-- Whole kept contact records on the same actual head open and its literal
native inverse image, with the SAME original function and all boundary slots. -/
theorem native_contact_kept (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) (u : X → ℂ) (O : Opens Y) :
    markedPullback (m := k) (sourceInclusion hk V hV O) (contactMarkedKept M u T O)=
      contactMarkedKept (nativePullback hk W hW M) (u∘Subtype.val) Q (nativeWindow hk V hV O) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let K := contactHead M u T
  have hK : ∀y g,K.ideal.mem y g → HolomorphicAt n g y := (contact_head_facts h M hME hMN u).2.2
  have hInc := (source_geometry hk V hV hVc O).1
  have hWhole : markedPullback (m := k) (sourceInclusion hk V hV O)
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → Y) K)=
      MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : nativeWindow hk V hV O → nativeManifold hk V hV) (nativePullback hk V hV K) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · change (K.E.map ((Subtype.val : O → Y) ⁻¹' ·)).map ((sourceInclusion hk V hV O) ⁻¹' ·)=
        (K.E.map ((Subtype.val : V → Y) ⁻¹' ·)).map
          ((Subtype.val : nativeWindow hk V hV O → nativeManifold hk V hV) ⁻¹' ·)
      simp only [List.map_map]
      rfl
    · change GermIdeal.pullback (m := k) (sourceInclusion hk V hV O)
          (GermIdeal.pullback (m := n) (Subtype.val : O → Y) K.ideal)=
        GermIdeal.pullback (m := k)
          (Subtype.val : nativeWindow hk V hV O → nativeManifold hk V hV)
          (GermIdeal.pullback (m := k) (Subtype.val : V → Y) K.ideal)
      rw [←whole_pullback_comp contMDiff_subtype_val hInc K.ideal hK,
        ←whole_pullback_comp (contMDiff_val hk hV) contMDiff_subtype_val K.ideal hK]
      rfl
    · rfl
  change markedPullback (m := k) (sourceInclusion hk V hV O)
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → Y) K)=_
  rw [hWhole,native_contact_head h hn hE hTrans M hME hMN hhol u]
  rfl

end
end Hironaka.HironakaDisjointNativeContactReference
