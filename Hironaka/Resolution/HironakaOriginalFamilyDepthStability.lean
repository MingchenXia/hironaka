import Hironaka.Resolution.HironakaActualNativeRecursiveValues
import Hironaka.Resolution.HironakaActualSectionBoundaryDimension

/-! Actual source-bound stability on the SAME original history. Depth padding
keeps gamma unchanged. Its proved commutation with actual gamma shifts gives
SAME-bound native histories from the closed offset producer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaOriginalFamilyDepthStability
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  ResolutionInvariantSpec ResolutionInvariantExt InvDomainTowerAlong CanonicalCentres
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime
  GeneralValue NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail MonomialCaseAlong MonomialInvariant
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaActualSectionBoundaryDimension
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeRecursiveValues NormalCrossings

def depthPadMap (h : ℕ) : (q : ℕ) → ValTy q → ValTy (h+q)
  | 0 => seedDimension h
  | q+1 => generalDimensionMap 0 (stepDimensionMap (depthPadMap h q))

theorem strictMono_depthPadMap (h : ℕ) : ∀q,StrictMono (depthPadMap h q)
  | 0 => strictMono_seedDimension h
  | q+1 => strictMono_generalDimensionMap 0 (strictMono_stepDimensionMap (strictMono_depthPadMap h q))

private theorem dimensionValue_zero (v : WithBot Val) : dimensionValue 0 v=v := by
  have hf : dimensionKey 0=id:=by
    funext a
    simp only [dimensionKey,Nat.add_zero,Prod.mk.eta,toLex_ofLex,id_eq]
  simp only [dimensionValue,hf,WithBot.map_id,id_eq]

private theorem stepMap_comp {α β γ : Type} (f : β→γ) (g : α→β) (v : ℕ ×ₗ WithTop α) :
    stepDimensionMap f (stepDimensionMap g v)=stepDimensionMap (f∘g) v := by
  simp only [stepDimensionMap,ofLex_toLex,WithTop.map_map]

private theorem generalMap_zero_comp {α β γ : Type} (f : β→γ) (g : α→β) (t : ℕ)
    (v : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop α)) :
    generalDimensionMap 0 f (generalDimensionMap t g v)=generalDimensionMap t (f∘g) v := by
  unfold generalDimensionMap
  simp only [ofLex_toLex]
  cases ofLex (ofLex v).2 with
  | inl a => simp only [Sum.map_inl,dimensionValue_zero]
  | inr b => simp only [Sum.map_inr,WithTop.map_map]

theorem depthPadMap_sameIndexMap (t : ℕ) : ∀q (v : ValTy q),
    depthPadMap t q (sameIndexMap t q v)=familyDimensionMap t q v
  | 0,_ => rfl
  | q+1,v => by
      change generalDimensionMap 0 (stepDimensionMap (depthPadMap t q))
          (generalDimensionMap t (stepDimensionMap (sameIndexMap t q)) v)=_
      rw [generalMap_zero_comp]
      have hf : stepDimensionMap (depthPadMap t q) ∘ stepDimensionMap (sameIndexMap t q)=
          stepDimensionMap (familyDimensionMap t q):=by
        funext w
        rw [Function.comp_apply,stepMap_comp]
        have ht : depthPadMap t q ∘ sameIndexMap t q=familyDimensionMap t q:=funext (depthPadMap_sameIndexMap t q)
        rw [ht]
      rw [hf]
      rfl

private def StableAt (h q : ℕ) : Prop :=
  ∀{n : ℕ}{X : CMfd.{0} n}(hn : 0<n)(M : MarkedIdeal n X),IsInvDomain q M →
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsCanonical M ((invFamily hn q).inv M) T →
      IsCanonical M ((invFamily hn (h+q)).inv M) T ∧
        ∀z∈(geoTransformAlong M T).cosupp,(invFamily hn (h+q)).inv M T z=depthPadMap h q ((invFamily hn q).inv M T z)

private theorem zero_can_empty {n : ℕ} {X : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
    (M : MarkedIdeal n X) (hM : IsInvDomain 0 M)
    (I : ∀{Y : CMfd.{0} n},BlowupTower X Y → Y → Λ) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsCanonical M I T → IsEmptyTower T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hCan => by
      refine ⟨zero_can_empty M hM I T hCan.1,?_⟩
      rcases hCan.2 with hC|hC
      · exact hC
      have hTest:=(countCentresMeeting_eq_zero_of_dimLE_zero hM I ∅ T hCan.1).1
      have hCos:=cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T hTest
      rw [hC,hCos]
      exact eq_empty_iff_forall_notMem.mpr fun _ h=>h.1

private theorem step_value_of_induction {h q n : ℕ} {X : CMfd.{0} n}
    (hIH : StableAt h q) (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) {Y : CMfd.{0} n}(T : BlowupTower X Y)
    (hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M) T)
    (z : Y) (hz : z∈(geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (h+q)) M T z=
      stepDimensionMap (depthPadMap h q) (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M T z) := by
  by_cases hsp : IsSpecial M T z
  · unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    simp only [if_pos hsp,stepDimensionMap,ofLex_toLex,WithTop.map_top]
  obtain ⟨hTBar,_hTOrig,hTCos⟩:=Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn q) M hM hmax hn T hCan
  have hCanBar:=(Seq.StepOneBridge.isCanonical_iff (invFamily hn q) M hM hmax hn T).mp hCan
  have hzBar : z∈(geoTransformAlong (barMarked M) T).cosupp:=hTCos.symm ▸ hz
  obtain ⟨hp,hDom,hLowerCan,hLowerCos⟩:=Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k:=q+1)
    (invFamily hn q) hM.isWellFormed hM.one_le_d hn hmax hM.dimLE T hTBar hCanBar z hzBar hsp
  simp only [Nat.add_sub_cancel] at hDom
  have hv:=(hIH hn _ hDom _ hLowerCan).2 _ hLowerCos
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  simp only [if_neg hsp]
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn (h+q)) M (lowerMarkedM M) hp,
    Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hn q) M (lowerMarkedM M) hp]
  simp only [stepDimensionMap,ofLex_toLex,WithTop.map_coe]
  exact congrArg (fun v : ValTy (h+q)=>toLex (level M T z,(v : WithTop (ValTy (h+q))))) hv

private theorem general_value_of_induction {h q n : ℕ} {X : CMfd.{0} n}
    (hIH : StableAt h q) (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M)
    {Y : CMfd.{0} n}(T : BlowupTower X Y) (hCan : IsCanonical M ((invFamily hn (q+1)).inv M) T)
    (z : Y) (hz : z∈(geoTransformAlong M T).cosupp) :
    (invFamily hn (h+(q+1))).inv M T z=depthPadMap h (q+1) ((invFamily hn (q+1)).inv M T z) := by
  let F0 : ∀{A : CMfd.{0} n},MarkedIdeal n A → ∀{B : CMfd.{0} n},BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy q):=
    fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (X:=A) (invFamily hn q) L (Y:=B) S y
  let Fh : ∀{A : CMfd.{0} n},MarkedIdeal n A → ∀{B : CMfd.{0} n},BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy (h+q)):=
    fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (X:=A) (invFamily hn (h+q)) L (Y:=B) S y
  have hT:=ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical (invFamily hn (q+1)).isInvValue hM T hCan
  change genInv Fh M T z=generalDimensionMap 0 (stepDimensionMap (depthPadMap h q)) (genInv F0 M T z)
  by_cases hZero : nmOrd (geoTransformAlong M T) z=0
  · rw [genInv_of_nmOrd_eq_zero Fh M T hZero,genInv_of_nmOrd_eq_zero F0 M T hZero]
    simp only [generalDimensionMap,ofLex_toLex,Sum.map_inl,dimensionValue_zero]
  let o:=nmOrd (geoTransformAlong M T) z
  have ho : 0<o:=Nat.pos_of_ne_zero hZero
  let r:=regimeRun (OrdRegime M o) T z
  obtain ⟨hp,hDom,hMax,hLowerCan,hLowerCos⟩:=GeneralCanonicalTail.hasGenLowerData_of_isCanonical F0
    (StepOneSeq.isMaxOrderValue_stepOneInvM (k:=q+1) (invFamily hn q) hn) hn hM T hT hCan z hz o rfl ho
  have hv:=step_value_of_induction hIH hn _ hDom hMax _ hLowerCan _ hLowerCos
  have hLower : genLowerValue Fh M o (head T r) (tail T r) z=
      WithTop.map (stepDimensionMap (depthPadMap h q)) (genLowerValue F0 M o (head T r) (tail T r) z):=by
    rw [genLowerValue_eq_of_mem Fh M hp,genLowerValue_eq_of_mem F0 M hp]
    simp only [WithTop.map_coe]
    exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy (h+q))=>(v : WithTop (ℕ ×ₗ WithTop (ValTy (h+q))))) hv
  unfold generalDimensionMap genInv genSecond
  rw [show nmOrd (geoTransformAlong M T) z=o from rfl]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr]
  rw [hLower]

private theorem general_can_of_induction {h q n : ℕ} {X : CMfd.{0} n}
    (hIH : StableAt h q) (hn : 0<n) (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsCanonical M ((invFamily hn (q+1)).inv M) T →
      IsCanonical M ((invFamily hn (h+(q+1))).inv M) T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hCan => by
      refine ⟨general_can_of_induction hIH hn M hM T hCan.1,?_⟩
      rcases hCan.2 with hC|hC
      · exact Or.inl hC
      right
      have hEq :=ResolutionInvariantExt.maxLocus_congr
        (fun z hz=>general_value_of_induction hIH hn M hM T hCan.1 z hz)
      have hMono:=MaxLocusLocal.maxLocus_comp_strictMono (strictMono_depthPadMap h (q+1))
        ((invFamily hn (q+1)).inv M T) (geoTransformAlong M T).cosupp
      exact hC.trans (hEq.trans hMono).symm

private theorem stability_all (h : ℕ) : ∀q,StableAt h q := by
  intro q
  induction q with
  | zero =>
    intro n X hn M hM Y T hCan
    have hEmpty:=zero_can_empty M hM ((invFamily hn 0).inv M) T hCan
    have hTest:=(countCentresMeeting_eq_zero_of_dimLE_zero hM ((invFamily hn 0).inv M) ∅ T hCan).1
    refine ⟨isCanonical_of_isEmptyTower _ _ T hEmpty,?_⟩
    intro z hz
    rw [cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T hTest] at hz
    exact False.elim hz
  | succ q ih =>
    intro n X hn M hM Y T hCan
    exact ⟨general_can_of_induction ih hn M hM T hCan,fun z hz=>general_value_of_induction ih hn M hM T hCan z hz⟩

/-- Actual ORIGINAL source-bound stability on the SAME original M/history.
Higher canonicality and full values are proved, with tight carrier bound q. -/
theorem original_family_depth_stability {n : ℕ} {X : CMfd.{0} n} (hn : 0<n) (h q : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain q M) {Y : CMfd.{0} n}(T : BlowupTower X Y)
    (hCan : IsCanonical M ((invFamily hn q).inv M) T) :
    IsCanonical M ((invFamily hn (h+q)).inv M) T ∧
      ∀z∈(geoTransformAlong M T).cosupp,(invFamily hn (h+q)).inv M T z=depthPadMap h q ((invFamily hn q).inv M T z) :=
  stability_all h q hn M hM T hCan

/-- Padding the recursive depth below an actual Step One history changes its
values by the step map and preserves and reflects its canonicality. -/
theorem original_step_one_depth_stability {n : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (h q : ℕ) (M : MarkedIdeal n X) (hM : IsInvDomain (q + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (T : BlowupTower X Y) :
    let f : ∀ {Z : CMfd.{0} n}, BlowupTower X Z → Z → ℕ ×ₗ WithTop (ValTy q) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M
    let g : ∀ {Z : CMfd.{0} n}, BlowupTower X Z → Z → ℕ ×ₗ WithTop (ValTy (h + q)) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn (h + q)) M
    (IsCanonical M g T ↔ IsCanonical M f T) ∧
      (IsCanonical M f T → ∀ z ∈ (geoTransformAlong M T).cosupp,
        g T z = stepDimensionMap (depthPadMap h q) (f T z)) := by
  let f : ∀ {Z : CMfd.{0} n}, BlowupTower X Z → Z → ℕ ×ₗ WithTop (ValTy q) :=
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) M
  let g : ∀ {Z : CMfd.{0} n}, BlowupTower X Z → Z → ℕ ×ₗ WithTop (ValTy (h + q)) :=
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn (h + q)) M
  have hv {Z : CMfd.{0} n} (S : BlowupTower X Z) (hCan : IsCanonical M f S) :
      ∀ z ∈ (geoTransformAlong M S).cosupp, g S z = stepDimensionMap (depthPadMap h q) (f S z) :=
    fun z hz => step_value_of_induction (stability_all h q) hn M hM hmax S hCan z hz
  refine ⟨?_, hv T⟩
  change IsCanonical M g T ↔ IsCanonical M f T
  induction T with
  | refl => exact Iff.rfl
  | @step Y Z S C π hπ ih =>
    have hLoci (hCan : IsCanonical M f S) :
        ResolutionDriver.maxLocus (g S) (geoTransformAlong M S).cosupp =
          ResolutionDriver.maxLocus (f S) (geoTransformAlong M S).cosupp :=
      (maxLocus_congr (hv S hCan)).trans (MaxLocusLocal.maxLocus_comp_strictMono
        (strictMono_stepDimensionMap (strictMono_depthPadMap h q)) (f S) (geoTransformAlong M S).cosupp)
    constructor
    · rintro ⟨hPrefix, hEmpty | hCentre⟩
      · exact ⟨ih.mp hPrefix, Or.inl hEmpty⟩
      · exact ⟨ih.mp hPrefix, Or.inr (hCentre.trans (hLoci (ih.mp hPrefix)))⟩
    · rintro ⟨hPrefix, hEmpty | hCentre⟩
      · exact ⟨ih.mpr hPrefix, Or.inl hEmpty⟩
      · exact ⟨ih.mpr hPrefix, Or.inr (hCentre.trans (hLoci hPrefix).symm)⟩

/-- The actual SAME-bound original native comparison follows from PROVED
source-bound stability and the closed offset producer, with all CAN derived. -/
theorem Lift.original_same_bound_values {n k q : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    (hn : 0<n) (hkpos : 0<k) (M : MarkedIdeal n X) (hM : IsInvDomain q M)
    (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q) (hCan : IsCanonical M ((invFamily hn q).inv M) T) :
    IsCanonical (nativePullback hk W hW M) ((invFamily hkpos q).inv (nativePullback hk W hW M)) Q ∧
      ∀z : nativeManifold hk V hV,z.val∈(geoTransformAlong M T).cosupp →
        (invFamily hn q).inv M T z.val=sameIndexMap (n-k) q ((invFamily hkpos q).inv (nativePullback hk W hW M) Q z) := by
  have hPad:=original_family_depth_stability hn (n-k) q M hM T hCan
  obtain ⟨hNativeCan,hValues⟩:=HironakaActualNativeRecursiveValues.Lift.original_recursive_values hn hkpos M hM hMN hTrans h hPad.1
  refine ⟨hNativeCan,fun z hz=>?_⟩
  apply (strictMono_depthPadMap (n-k) q).injective
  exact (hPad.2 z.val hz).symm.trans ((hValues z hz).trans (depthPadMap_sameIndexMap (n-k) q _).symm)

end
end Hironaka.HironakaOriginalFamilyDepthStability
