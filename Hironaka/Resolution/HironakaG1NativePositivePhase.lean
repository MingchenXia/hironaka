import Hironaka.Resolution.HironakaG1ActualHighestPhaseKeys
import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaG8BFamilyPad

/-! # Native realization of the actual positive selected section phase

The section phase uses its own positive regime cut. The Cartier
counterexample shows why transport of this section value does not
assert equality with the raw padded maximum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1NativePositivePhase
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  NormalCrossings NormalCrossingsInvariance SubmanifoldChartedSpace
  HomogenizedGlueingTower HomogenizedIdealAlong CoefficientIdeal CoefficientIdealRestriction MemberInterTowerAlong InvDomainMemberRestriction InvDomainRebase
  HironakaG8BFamilyPad HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperNormalPhaseNative HironakaG1RecursiveMemberValueTransport
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeHistoryExistence
  HironakaActualNativeInvariantDomain HironakaActualNativeSectionOrderHistory
  HironakaDisjointNativeOpenLift HironakaActualSectionBoundaryDimension
  HironakaG1LaterLiteralSectionCanonicalTail HironakaG1LaterSectionPairOrder
  HironakaActualSectionBoundaryGeometry RelativePrincipalizationSpan

private theorem isTransverse_of_list_members {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} {E F : List (Set X)} (h : IsTransverse n W E)
    (hSub : ∀ D ∈ F, D ∈ E) : IsTransverse n W F := by
  classical
  intro x hx
  obtain ⟨S₀,S,hCoords,hTrans⟩ := h x hx
  have hFind (i : Fin F.length) : ∃ j : Fin E.length, E.get j = F.get i :=
    List.mem_iff_get.mp (hSub _ (List.get_mem F i))
  choose p hp using hFind
  refine ⟨S₀, S ∘ p, isCoordinateFamilyAt_reindex hCoords ?_, ?_⟩
  · rintro (_ | i) _
    · exact ⟨none,rfl,rfl⟩
    · exact ⟨some (p i),hp i,rfl⟩
  · intro i hi
    exact hTrans (p i) (hp i ▸ hi)

set_option maxHeartbeats 1200000 in
/-- The retained positive section record is supported on the genuine
native section at the actual tested head. Deleting original members
preserves transversality of the section to the retained ordered list. -/
theorem selected_section_supported_native_head {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)}
    (H : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) (O : Opens Y) :
    let S := positiveMemberOn (sectionMarked Q) H p O
    ∃ (W : Set (CMfd.of (n := n+1) O)) (_hWc : IsClosed W)
      (_hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n),
      W = (Subtype.val : O → Y) ⁻¹' strictAlong H (zeroPlane U) ∧
      S.N ⊆ W ∧ IsTransverse (n+1) W S.E := by
  intro S
  let X := CMfd.of (n := n+1) (productOpen U)
  let Sec := sectionMarked Q
  obtain ⟨V,hVc,hV,N,hLift,_,_,_,hTrans,_,_⟩ :=
    exists_upper_native_test_history Q hQ H hH
  let W : Set (CMfd.of (n := n+1) O) := openSection V O
  have hWc : IsClosed W := hVc.preimage continuous_subtype_val
  have hW : ∀x ∈ W, RegularAtDim (n := n+1) W x n := openSection_regular hV O
  have hW_eq : W = (Subtype.val : O → Y) ⁻¹' strictAlong H (zeroPlane U) :=
    congrArg (fun A : Set Y => (Subtype.val : O → Y) ⁻¹' A) hLift.carrier
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hAlong : (geoTransformAlong (barMarked (X := X) Sec) H).N ⊆ strictAlong H (zeroPlane U) := by
    rw [N_geoTransformAlong]
    exact strictAlong_mono H hSupport
  let A := geoTransformAlong (barMarked (X := X) Sec) H
  let I := membersThrough A.E (origMembers Sec H) p
  have hN : S.N ⊆ W := by
    intro x hx
    rw [hW_eq]
    have hx' : x.val ∈ A.N := hx.1
    exact hAlong hx'
  have hE : A.E = (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked (X := X) Sec)
      (𝔫 := sectionBarCoefficient Q) rfl H
  have hSub : ∀ D ∈ (memberRestrict A I).E, D ∈ (geoTransformAlong (sectionBarCoefficient Q) H).E := by
    intro D hD
    rw [← hE]
    rw [memberRestrict_E] at hD
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hD
    exact List.get_mem A.E i
  have hTr : IsTransverse (n+1) W S.E := by
    change IsTransverse (n+1) W ((memberRestrict A I).E.map ((Subtype.val : O → Y) ⁻¹' ·))
    exact isTransverse_preimage (pullsBackCoordinates_val O) (isTransverse_of_list_members hTrans hSub)
  exact ⟨W,hWc,hW,hW_eq,hN,hTr⟩

set_option maxHeartbeats 1700000 in
/-- Positive counterpart of the actual native zero-phase construction.
The section's literal selected suffix lifts to the native transformed
section. The returned native value reads the actual upper section at
the chosen point through the same-bound dimension embedding. -/
theorem exists_actual_positive_selected_native_phase {n k s : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp)
    (hLevel : level (sectionMarked Q) T y = s+1) (hNS : ¬ IsSpecial (sectionMarked Q) T y) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let j := regimeRun (stepRegime Sec (s+1)) T y
    let H := head T j
    let R := tail T j
    let p := R.proj y
    ∃ (O : Opens (split T j).1) (u : (split T j).1 → ℂ) (hp : p ∈ O),
      let S := positiveMemberOn Sec H p O
      let L := positiveMemberOn P H p O
      let C := withN (coeffMarkedAlong L) (L.N ∩ {z : O | u z.val = 0})
      let A := CMfd.of (n := n+1) O
      let D := CMfd.of (n := n+1) (openPreimage R O)
      let G := restrict O R
      LaterSectionComparison (X := A) Q.d k C S ∧
      ∃ (W : Set A) (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n+1) W x n),
      W = (Subtype.val : O → (split T j).1) ⁻¹' strictAlong H (zeroPlane U) ∧
      S.N ⊆ W ∧ IsTransverse (n+1) W S.E ∧
      ∃ (V : Set D) (hVc : IsClosed V) (hV : ∀ x ∈ V, RegularAtDim (n := n+1) V x n)
        (N : BlowupTower (nativeManifold (Y := A) (Nat.le_succ n) W hW)
          (nativeManifold (Y := D) (Nat.le_succ n) V hV)),
        Lift (Nat.le_succ n) W hWc hW S.E G V hVc hV N ∧
        let SNative := nativePullback (Y := A) (Nat.le_succ n) W hW S
        let CNative := nativePullback (Y := A) (Nat.le_succ n) W hW C
        IsInvDomain k SNative ∧ IsGeoTestTower SNative N ∧
        IsInvDomain k CNative ∧ IsCanonical CNative ((invFamily hn k).inv CNative) N ∧
        (∀ z : nativeManifold (Y := D) (Nat.le_succ n) V hV,
          z.val ∈ (geoTransformAlong C G).cosupp →
          (invFamily (Nat.succ_pos n) k).inv C G z.val =
            sameIndexMap 1 k ((invFamily hn k).inv CNative N z)) ∧
        IsCanonical SNative ((invFamily hn k).inv SNative) N ∧
        geoTransformAlong SNative N = nativePullback (Y := D) (Nat.le_succ n) V hV (geoTransformAlong S G) ∧
        (Subtype.val : V → D) '' (geoTransformAlong SNative N).cosupp = (geoTransformAlong S G).cosupp ∧
        ∃ z : nativeManifold (Y := D) (Nat.le_succ n) V hV,
          z.val = (⟨y,hp⟩ : openPreimage R O) ∧ z ∈ (geoTransformAlong SNative N).cosupp ∧
          Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) Sec T y =
            toLex (s+1, (sameIndexMap 1 k ((invFamily hn k).inv SNative N z) : WithTop (ValTy k))) := by
  intro P Sec j H R p
  let X := CMfd.of (n := n+1) (productOpen U)
  let I := invFamily (Nat.succ_pos n) k
  have hSec := section_projected_domain (k+1) Q.N Q.E Q.ideal Q.d hQ
  have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (X := X) (k := k+1) I Sec
    hSec hMax (Nat.succ_pos n) T hCan).2.1
  have hSH := ((isGeoTestTower_iff_head_tail Sec T j).mp hT).1
  have hPH := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mpr hSH
  obtain ⟨O,u,hp,_,hComp,hCanC,hCanS,hEndC,hRead⟩ :=
    later_literal_section_finite_read Q hQ T y hy hLevel hNS hMax hCan
  let A := CMfd.of (n := n+1) O
  let D := CMfd.of (n := n+1) (openPreimage R O)
  let G : BlowupTower A D := restrict O R
  let S := positiveMemberOn Sec H p O
  let L := positiveMemberOn P H p O
  let C := withN (coeffMarkedAlong L) (L.N ∩ {z : O | u z.val = 0})
  obtain ⟨W,hWc,hW,hW_eq,hSN,hTrans⟩ := selected_section_supported_native_head Q hQ H hPH p O
  have hS := hComp.sectionDomain
  have hSG := I.isInvValue.isGeoTestTower_of_isCanonical hS G hCanS
  obtain ⟨V,hVc,hV,N,hLift,hNativeTest⟩ := exists_native_history_of_original_test
    (Nat.succ_pos n) (Nat.le_succ n) W hWc hW S hS hSN hTrans G hSG
  let SNative := nativePullback (Y := A) (Nat.le_succ n) W hW S
  have hDom := isInvDomain_nativePullback (Nat.succ_pos n) (Nat.le_succ n) hW S hS hSN hTrans
  have hNV := HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (n := n+1) (k := n) (q := k) (X := A) (hk := Nat.le_succ n)
    (W := W) (hWc := hWc) (hW := hW) (T := G) (V := V) (hVc := hVc) (hV := hV) (Q := N)
    (Nat.succ_pos n) hn S hS hSN hTrans hLift hCanS
  have hCE : C.E = S.E := hComp.localClass.wEquiv.1
  have hCN : C.N ⊆ W := hComp.carrier.symm ▸ hSN
  have hCTr : IsTransverse (n+1) W C.E := hCE.symm ▸ hTrans
  have hCLift : Lift (Nat.le_succ n) W hWc hW C.E G V hVc hV N := hCE.symm ▸ hLift
  have hCD := isInvDomain_nativePullback (X := A) (Nat.succ_pos n) (Nat.le_succ n)
    hW C hComp.contactDomain hCN hCTr
  have hCV := HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (n := n+1) (k := n) (q := k) (X := A) (hk := Nat.le_succ n)
    (W := W) (hWc := hWc) (hW := hW) (T := G) (V := V) (hVc := hVc) (hV := hV) (Q := N)
    (Nat.succ_pos n) hn C hComp.contactDomain hCN hCTr hCLift hCanC
  have hHol : ∀ x g, S.ideal.mem x g → HolomorphicAt (n+1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hS.isWellFormed.isCoherent hg
  have hWhole := hLift.whole_records (Nat.succ_pos n) hS.isWellFormed.isSNCDivisor hTrans S rfl hSN hHol
  have hCos := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift (Nat.succ_pos n)
    hS.isWellFormed.isSNCDivisor hTrans S rfl hSN hHol
  have hSupport := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift S hSN
  have hImage : (Subtype.val : V → D) '' (geoTransformAlong SNative N).cosupp = (geoTransformAlong S G).cosupp := by
    rw [hCos]
    apply Set.image_preimage_eq_iff.mpr
    exact fun z hz => ⟨⟨z,hSupport hz.1⟩,rfl⟩
  let a : openPreimage R O := ⟨y,hp⟩
  have hEndS : a ∈ (geoTransformAlong S G).cosupp := by
    have hSGC : IsGeoTestTower C G := (hComp.localClass.wEquiv.2 G).1.mpr hSG
    exact ((hComp.localClass.wEquiv.2 G).2 hSGC) ▸ hEndC
  let z : nativeManifold (Y := D) (Nat.le_succ n) V hV := ⟨a,hSupport hEndS.1⟩
  have hz : z ∈ (geoTransformAlong SNative N).cosupp := hCos.symm ▸ hEndS
  have hVal := hNV.2 z hEndS
  have hDim : (n+1)-n = 1 := by omega
  rw [hDim] at hVal
  refine ⟨O,u,hp,hComp,W,hWc,hW,hW_eq,hSN,hTrans,V,hVc,hV,N,hLift,hDom,hNativeTest,hCD,hCV.1,?_,hNV.1,
    hWhole,hImage,z,rfl,hz,?_⟩
  · intro w hw
    simpa only [hDim] using hCV.2 w hw
  · exact hRead.trans (congrArg (fun v : ValTy k => toLex (s+1,(v : WithTop (ValTy k)))) hVal)

end
end Hironaka.HironakaG1NativePositivePhase
