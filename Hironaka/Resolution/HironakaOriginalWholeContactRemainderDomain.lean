/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.BlowupSplitProjectionExact
import Hironaka.Resolution.HironakaOriginalWholeMemberLowerAnalytic
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderExtension
/-! Actual original all-dimensional chosen contact opens, genuine unselected
contact components and whole lower prefix domains. Original historical positions
are retained as empty entries. Complete source-first blueprint precedes code.
Entire original mask record equality and global arbitrary lower thresholds remain
next consumers. No caller tangent/open/domain/nonzero/normal-form certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalWholeContactRemainderDomain
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction DropMembers
  GermIdealOrder BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneSpecialAnalyticLoci
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneZeroContactPatchValues MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HomogenizedGlueingTower GlobalComponents CodimOneSupportAlong
open DivisorExponentAlong MemberInterLocusAlong MemberInterTowerAlong
  StepOneLowerDomain StepOneValue StepOneRegime CanonicalCentres
  HironakaDimensionThreeStepOneLowerAnalyticLoci ContactEquivalenceAlong MaximalContactAlongTower TangentDirectionAlong ContactStageKept ContactStageInvDomain
  HomogenizedIdealAlong HomogenizedIdealAlongTower NormalCrossings NormalCrossingsInvariance
  HironakaCoherentTransformExtension LocalGiraudTransformAlong
open HironakaGeneralThreeNonspecialAnalyticLoci
open MaxLocusLocal BlowupTowerIsomorphism RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
open HironakaStepOneZeroContactRemainderExtension NonmonomialOrderLocal MonomialPartAlong
variable {n k b : ℕ} {X Y : CMfd.{u} n}

private theorem contact_model_geometry {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q)) :
    let V := openPreimage H U
    let L := contactMarkedKept K w H V
    IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧ ResolutionInvariantSpec.DimLE n L.N (k+1) ∧
      IsGeoTestTower L (restrict V Q) ∧
      (geoTransformAlong L (restrict V Q)).cosupp =
        (Subtype.val : openPreimage Q V → Z) ⁻¹' (geoTransformAlong (barMarked K) (H.append Q)).cosupp := by
  dsimp only
  have hH := ((isGeoTestTower_append_iff (barMarked K) H Q).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hN := isClosedSubmanifold_strictAlong_stage_of_le K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa (openPreimage H U) subset_rfl
  have hI : (contactMarkedKept K w H (openPreimage H U)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N w H hH)
  have hdim0 := dimLE_strictAlong_stage K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa hK.dimLE
  have hdim : ResolutionInvariantSpec.DimLE n (contactMarkedKept K w H (openPreimage H U)).N (k+1) := by
    change ResolutionInvariantSpec.DimLE n ((Subtype.val : openPreimage H U → Y) ⁻¹'
      strictAlong H (K.N ∩ {x | w x = 0})) (k+1)
    simpa only [show (k+2)-1=k+1 by omega] using hdim0
  have ht := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H Q hT
    (openPreimage H U) subset_rfl
  exact ⟨hN, hI, hdim, ht⟩

/-- Original actual zero-level data internally produce the SAME enlarged contact model. -/
theorem exists_actual_enlarged_zero_contact_model (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧ H.proj p₀ ∈ U ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      lowerMask K (level K R p) H p₀ = maskB K H p₀ ∧
      maskB K H p₀ ≤ V ∧ IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧
        ResolutionInvariantSpec.DimLE n L.N (k+1) ∧ IsGeoTestTower L (restrict V Q) ∧
        (geoTransformAlong L (restrict V Q)).cosupp =
          (Subtype.val : openPreimage Q V → Y) ⁻¹' (geoTransformAlong K R).cosupp := by
  dsimp only
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+2) (invFamily hn (k+1)) K hK hmax hn R hcan
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hh := ((isGeoTestTower_iff_head_tail (barMarked K) R (regimeRun (stepRegime K (level K R p)) R p)).mp hb.1).1
  obtain ⟨_, hpH⟩ := StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hns
  obtain ⟨hpU, hw⟩ := tangentChoice_spec K (exists_tangent_of_mem_cosupp K hK.isWellFormed
    hK.one_le_d hmax _ hh hpH)
  let U : Opens X := ⟨_, hw.isOpen⟩
  have hsplit : (head R (regimeRun (stepRegime K (level K R p)) R p)).append
    (tail R (regimeRun (stepRegime K (level K R p)) R p)) = R := head_append_tail R _
  have hT : IsGeoTestTower (barMarked K)
      ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
        (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by rw [hsplit]; exact hb.1
  obtain ⟨hN, hI, hd, ht, hcs⟩ := contact_model_geometry K hK U _ hw _ _ hT
  rw [hsplit, hb.2.2] at hcs
  refine ⟨U, rfl, hpU, hw, ?_, ?_, hN, hI, hd, ht, hcs⟩
  · rw [hl]; rfl
  · intro z hz
    exact (interior_subset hz).1


private theorem remainder_cosupp (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (k : ℕ) :
    (contactRemainderMarked L k).cosupp = L.cosupp ∩ (contactRemainderMarked L k).N := by
  have hsub : (contactRemainderMarked L k).N ⊆ L.N := by
    change remainingComponents (n := n) L.N L.cosupp ⊆ L.N
    rw [remainingComponents_eq_diff_selected hN]
    exact sdiff_subset
  ext x
  constructor
  · rintro ⟨hxN, hxord⟩
    have hev := eventually_mem_remainingComponents_iff hN hxN
    refine ⟨⟨hsub hxN, fun g hg => ?_⟩, hxN⟩
    obtain ⟨f, hf, hgf⟩ := hxord g hg
    refine ⟨f, hf, ?_⟩
    filter_upwards [hev, hgf] with z hz hgz hzH
    exact hgz (hz.mpr hzH)
  · rintro ⟨hxA, hxN⟩
    exact ⟨hxN, fun g hg => (hxA.2 g hg).mono_set hsub⟩

theorem contactRemainder_geometry_and_nonzero (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1 ≤ L.d) (hDim : ResolutionInvariantSpec.DimLE n L.N b) :
    IsClosedSubmanifold n (contactRemainderMarked L k).N ∧
      (contactRemainderMarked L k).ideal.IsCoherent ∧
      ResolutionInvariantSpec.DimLE n (contactRemainderMarked L k).N b ∧
      (∀ x ∈ (contactRemainderMarked L k).N,
        IsNonzeroAlongAt (contactRemainderMarked L k).N (contactRemainderMarked L k).ideal x) ∧
      (contactRemainderMarked L k).cosupp = L.cosupp ∩ (contactRemainderMarked L k).N := by
  have hA := isComplexAnalyticSubset_cosupport_along hI hN hd
  have hRN := isClosedSubmanifold_remainingComponents hN L.cosupp
  have hsub : (contactRemainderMarked L k).N ⊆ L.N := by
    change remainingComponents (n := n) L.N L.cosupp ⊆ L.N
    rw [remainingComponents_eq_diff_selected hN]
    exact sdiff_subset
  have hdim : ResolutionInvariantSpec.DimLE n (contactRemainderMarked L k).N b := by
    intro x hx
    obtain ⟨j, hj⟩ := hRN.2 x hx
    obtain ⟨d, hd, hxH⟩ := hDim x (hsub hx)
    exact ⟨j, (BlowupStrictSubmanifold.le_of_regularAtDim_subset hj hxH hsub).trans hd, hj⟩
  have hcs := remainder_cosupp L hN k
  have hthin := thin_inter_remainingComponents hN hA
  refine ⟨hRN, hI, hdim, ?_, hcs⟩
  intro x hx
  apply isNonzeroAlongAt_of_thin_cosupport (d := L.d) hI
  · intro O hO hOA
    apply hthin O hO
    change O ∩ (contactRemainderMarked L k).N ⊆ L.cosupp ∩ (contactRemainderMarked L k).N
    rw [← hcs]
    exact hOA
  · exact hx

private theorem contact_partition (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) :
    L.N = remainingComponents (n := n) L.N L.cosupp ∪ selectedComponents (n := n) L.N L.cosupp ∧
      Disjoint (remainingComponents (n := n) L.N L.cosupp) (selectedComponents (n := n) L.N L.cosupp) := by
  rw [remainingComponents_eq_diff_selected hN]
  have hsub : selectedComponents (n := n) L.N L.cosupp ⊆ L.N := by
    rintro x ⟨B, ⟨hB, _⟩, hxB⟩
    exact subset_of_mem_globalComponents (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hB hxB
  exact ⟨(sdiff_union_of_subset hsub).symm, disjoint_sdiff_left⟩

private theorem remainder_strict_geometry (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hDim : ResolutionInvariantSpec.DimLE n L.N b)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    IsClosedSubmanifold n (geoTransformAlong (contactRemainderMarked L k) T).N ∧
      ResolutionInvariantSpec.DimLE n (geoTransformAlong (contactRemainderMarked L k) T).N b ∧
      ∀ x ∈ (geoTransformAlong (contactRemainderMarked L k) T).N,
        ∀ᶠ y in 𝓝 x,
          y ∈ (geoTransformAlong (contactRemainderMarked L k) T).N ↔
            y ∈ (geoTransformAlong L T).N := by
  have hR := isClosedSubmanifold_remainingComponents hN L.cosupp
  have hS := isClosedSubmanifold_selectedComponents hN L.cosupp
  obtain ⟨hpart, hdis⟩ := contact_partition L hN
  have hcarrier : (geoTransformAlong (contactRemainderMarked L k) T).N =
      strictAlong T (remainingComponents (n := n) L.N L.cosupp) :=
    N_geoTransformAlong (contactRemainderMarked L k) T
  have hfull : (geoTransformAlong L T).N = strictAlong T L.N := N_geoTransformAlong L T
  have hNSM := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT).1
  have hev : ∀ x ∈ (geoTransformAlong (contactRemainderMarked L k) T).N,
      ∀ᶠ y in 𝓝 x,
        y ∈ (geoTransformAlong (contactRemainderMarked L k) T).N ↔ y ∈ (geoTransformAlong L T).N := by
    intro x hx
    rw [hcarrier] at hx ⊢
    rw [hfull]
    exact eventually_mem_strictAlong_iff_of_closed_partition hR.1 hS.1 hdis hpart T hx
  have hRN : IsClosedSubmanifold n (geoTransformAlong (contactRemainderMarked L k) T).N := by
    refine ⟨?_, ?_⟩
    · rw [hcarrier]
      exact isClosed_strictAlong T hR.1
    · intro x hx
      obtain ⟨d, hd⟩ := hNSM.2 x ((hev x hx).self_of_nhds.mp hx)
      exact ⟨d, CodimOneSupport.regularAtDim_of_eventually_mem_iff
        ((hev x hx).mono fun _ h => h.symm) hd⟩
  have hdT := InvDomainTowerAlong.dimLE_geoTransformAlong hN hI hDim T hT
  refine ⟨hRN, ?_, hev⟩
  intro x hx
  obtain ⟨d, hd⟩ := hRN.2 x hx
  obtain ⟨j, hj, hjR⟩ := hdT x ((hev x hx).self_of_nhds.mp hx)
  exact ⟨d, (BlowupStrictSubmanifold.le_of_regularAtDim_subset hd hjR
    (fun y hy => (hev y hy).self_of_nhds.mp hy)).trans hj, hd⟩

private theorem remainder_transform_coherent_nonzero (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d)
    (hDim : ResolutionInvariantSpec.DimLE n L.N b) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower L T →
      (geoTransformAlong (contactRemainderMarked L k) T).ideal.IsCoherent ∧
        ∀ x ∈ (geoTransformAlong (contactRemainderMarked L k) T).N,
          IsNonzeroAlongAt (geoTransformAlong (contactRemainderMarked L k) T).N
            (geoTransformAlong (contactRemainderMarked L k) T).ideal x
  | _, .refl, _ => by
    have h := contactRemainder_geometry_and_nonzero L k hN hI hd hDim
    exact ⟨h.2.1, h.2.2.2.1⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := hT
    obtain ⟨hIT, hnzT⟩ := remainder_transform_coherent_nonzero L k hN hI hd hDim T hTT
    have hNT := (remainder_strict_geometry L k hN hI hDim T hTT).1
    have hN' := (remainder_strict_geometry L k hN hI hDim (.step T C π hπ) ⟨hTT, hC⟩).1
    exact ⟨isCoherent_geoTransform_ideal_of_smooth_strict _ hIT hπ hN',
      isNonzeroAlongAt_geoTransform_of_smooth_strict _ hNT hIT hπ hN' hnzT⟩

private theorem snc_empty_cons {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor n E) : NormalCrossings.IsSNCDivisor n (∅ :: E) := by
  classical
  refine ⟨fun A hA => ?_, fun x => ?_⟩
  · rcases List.mem_cons.mp hA with rfl | hA
    · exact isClosed_empty
    · exact hE.1 A hA
  · obtain ⟨S, ⟨Φ, ht, h0, hcoords⟩, hcard, hinj⟩ := hE.2 x
    let S' : Fin (∅ :: E).length → Finset (Fin n) := Fin.cases ∅ S
    refine ⟨S', ⟨Φ, ht, h0, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa [S'] using hcoords j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa [S'] using hcard j
    · intro i hi j hj heq
      refine Fin.cases ?_ (fun a => ?_) i hi heq
      · simp
      · intro ha hea
        refine Fin.cases ?_ (fun b => ?_) j hj hea
        · simp
        · intro hb hab
          exact congrArg Fin.succ (hinj (by simpa using ha) (by simpa using hb)
            (by simpa [S'] using hab))

private theorem snc_empty_prefix {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor n E) (k : ℕ) :
    NormalCrossings.IsSNCDivisor n (List.replicate k ∅ ++ E) := by
  induction k with
  | zero => simpa using hE
  | succ k ih => simpa [List.replicate_succ] using snc_empty_cons ih

private theorem transverse_empty_prefix {A : Set X} {E : List (Set X)}
    (h : NormalCrossings.IsTransverse n A E) (k : ℕ) :
    NormalCrossings.IsTransverse n A (List.replicate k ∅ ++ E) := by
  apply ContactStageInvDomain.isTransverse_append_of_forall_notMem h
  intro H hH x hx
  have hH' : H = ∅ := List.eq_of_mem_replicate hH
  simp [hH']

private theorem remainder_boundary (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (contactRemainderMarked L k) T).E =
        List.replicate k ∅ ++ (geoTransformAlong L T).E.drop k
  | _, .refl => rfl
  | _, .step T C π hπ => by
    change (geoTransformAlong (contactRemainderMarked L k) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C] =
      ((List.replicate k ∅) ++
        ((geoTransformAlong L T).E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]).drop k)
    rw [remainder_boundary L k hk T]
    have hkT : k ≤ ((geoTransformAlong L T).E.map (BlowupStrictSubmanifold.geoStrictTransform π C)).length :=
      by simpa using hk.trans (length_E_le_length_E_geoTransformAlong L T)
    rw [List.map_append, List.map_replicate, List.drop_append_of_le_length hkT]
    have hempty : BlowupStrictSubmanifold.geoStrictTransform π C ∅ = ∅ := by
      simp [BlowupStrictSubmanifold.geoStrictTransform]
    simp only [hempty, List.map_drop, List.append_assoc]

private theorem contact_exceptional_boundary {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q))
    (U : Opens X) (w : X → ℂ) :
    let V := openPreimage H U
    let L := contactMarkedKept K w H V
    K.E.length ≤ L.E.length ∧
      (geoTransformAlong L (restrict V Q)).E =
        (geoTransformAlong (barMarked K) (H.append Q)).E.map
          ((Subtype.val : openPreimage Q V → Z) ⁻¹' ·) ∧
      IsSNCDivisor n ((geoTransformAlong L (restrict V Q)).E.drop K.E.length) := by
  dsimp only
  have hB := isWellFormed_barMarked K hK.isWellFormed
  obtain ⟨hH, hQ⟩ := (isGeoTestTower_append_iff (barMarked K) H Q).mp hT
  have hBH := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hB H hH
  have hinit : (contactMarkedKept K w H (openPreimage H U)).E =
      (MarkedIdeal.pullback (Subtype.val : openPreimage H U → Y)
        (geoTransformAlong (barMarked K) H)).E := rfl
  have heq := geoTransformAlong_E_eq_of_E_eq hinit (restrict (openPreimage H U) Q)
  rw [geoTransformAlong_restrict (openPreimage H U) hBH.isClosedSubmanifold_N hBH.isCoherent Q hQ] at heq
  have heq' : (geoTransformAlong (contactMarkedKept K w H (openPreimage H U))
      (restrict (openPreimage H U) Q)).E =
      (geoTransformAlong (barMarked K) (H.append Q)).E.map
        ((Subtype.val : openPreimage Q (openPreimage H U) → Z) ⁻¹' ·) := by
    simpa only [geoTransformAlong_append, MarkedIdeal.pullback] using heq
  refine ⟨?_, heq', ?_⟩
  · change K.E.length ≤ ((geoTransformAlong (barMarked K) H).E.map
      ((Subtype.val : openPreimage H U → Y) ⁻¹' ·)).length
    rw [List.length_map]
    exact length_E_le_length_E_geoTransformAlong (barMarked K) H
  · rw [heq']
    apply NormalCrossingsComparison.isSNCDivisor_of_sublist
      (isSNCDivisor_map_preimage (pullsBackCoordinates_val _) continuous_subtype_val (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hB _ hT).isSNCDivisor)
    exact List.drop_sublist _ _

private theorem contact_exceptional_transverse {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q)) :
    let V := openPreimage H U
    let L := contactMarkedKept K w H V
    IsTransverse n (geoTransformAlong L (restrict V Q)).N
      ((geoTransformAlong L (restrict V Q)).E.drop K.E.length) := by
  dsimp only
  have hB := isWellFormed_barMarked K hK.isWellFormed
  have hA : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' (K.N ∩ {x | w x = 0})) := by
    have hh := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) U)
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) K)
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hK.isWellFormed.isClosedSubmanifold_N U)
      (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hK.isWellFormed.isCoherent)
      (isTangentDirectionAlong_pullback_val U
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hK.isWellFormed.isCoherent) hw)
    simpa [MarkedIdeal.pullback] using hh
  have hcent : ∀ {Z' : CMfd.{u} n} (T : BlowupTower X Z') (C : Set Z'),
      IsGeoTestTower (barMarked K) T → (geoTransformAlong (barMarked K) T).IsAdmissibleCentre C →
      C ∩ T.proj ⁻¹' (U : Set X) ⊆ strictAlong T (K.N ∩ {x | w x = 0}) := by
    intro Z' T C ht hc z hz
    have ha := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent hK.one_le_d).2 T).1.mp ht
    have hcs : z ∈ (geoTransformAlong K T).cosupp := by
      rw [← (coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
        hK.isWellFormed.isCoherent hK.one_le_d).2 T |>.2 ht]
      exact hc.2.1 hz.1
    exact strictAlong_mono T (fun x hx => hx.1)
      (cosupp_subset_strictAlong_along K hK.isWellFormed.isClosedSubmanifold_N
        hK.isWellFormed.isCoherent hK.one_le_d hw T ha ⟨hcs, hz.2⟩)
  have htr := CodimOneAdmissibleAlong.isTransverse_drop_E_inter_preimage
    (barMarked K) hB U hA hcent (H.append Q) hT
  let V := openPreimage H U
  let W := openPreimage Q V
  have htr' := isTransverse_preimage (pullsBackCoordinates_val W) htr
  have hN : (geoTransformAlong (contactMarkedKept K w H V) (restrict V Q)).N =
      (Subtype.val : W → Z) ⁻¹' (strictAlong (H.append Q) (K.N ∩ {x | w x = 0}) ∩
        (H.append Q).proj ⁻¹' (U : Set X)) := by
    rw [N_geoTransformAlong]
    change strictAlong (restrict V Q) ((Subtype.val : V → Y) ⁻¹' strictAlong H (K.N ∩ {x | w x = 0})) = _
    rw [strictAlong_restrict, ← strictAlong_append]
    ext z
    constructor
    · intro hz
      exact ⟨hz, by
        rw [BlowupTower.proj_append]
        exact z.2⟩
    · exact fun hz => hz.1
  rw [hN, (contact_exceptional_boundary K hK H Q hT U w).2.1, ← List.map_drop]
  exact htr'

theorem contact_remainder_domain {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q)) :
    let V := openPreimage H U
    let L := contactMarkedKept K w H V
    IsInvDomain (k+1) (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V Q)) := by
  dsimp only
  let V := openPreimage H U
  let L := contactMarkedKept K w H V
  have hH := ((isGeoTestTower_append_iff (barMarked K) H Q).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hN : IsClosedSubmanifold n L.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa V subset_rfl
  have hI : L.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N w H hH)
  have hdim : ResolutionInvariantSpec.DimLE n L.N (k+1) := by
    change ResolutionInvariantSpec.DimLE n ((Subtype.val : openPreimage H U → Y) ⁻¹'
      strictAlong H (K.N ∩ {x | w x = 0})) (k+1)
    simpa only [show (k+2)-1=k+1 by omega] using dimLE_strictAlong_stage K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa hK.dimLE
  have ht : IsGeoTestTower L (restrict V Q) := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H Q hT V subset_rfl).1
  have hd : 1 ≤ L.d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  obtain ⟨hRN, hRdim, hRGerm⟩ := remainder_strict_geometry (X := CMfd.of (n := n) V) (Y := CMfd.of (n := n) (openPreimage Q V)) L K.E.length hN hI hdim (restrict V Q) ht
  obtain ⟨hRI, hnz⟩ := remainder_transform_coherent_nonzero (X := CMfd.of (n := n) V) L K.E.length hN hI hd hdim (restrict V Q) ht
  have hb := contact_exceptional_boundary K hK H Q hT U w
  have he := remainder_boundary L K.E.length hb.1 (restrict V Q)
  have htr := contact_exceptional_transverse K hK U w hw H Q hT
  have htrR : IsTransverse n (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V Q)).N
      ((geoTransformAlong L (restrict V Q)).E.drop K.E.length) := by
    apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
    intro x hx
    exact ⟨_, (hRGerm x hx).self_of_nhds.mp hx, hRGerm x hx, htr⟩
  refine ⟨⟨hRN, hRI, ?_, ?_⟩, hRdim, ?_, hnz⟩
  · rw [he]
    exact snc_empty_prefix hb.2.2 _
  · rw [he]
    exact transverse_empty_prefix htrR _
  · rwa [d_geoTransformAlong]

theorem contactRemainder_actual_prefix_domain (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      maskB K H p₀ ≤ V ∧
      ∀ j : ℕ, IsInvDomain (k+1) (geoTransformAlong (contactRemainderMarked L K.E.length)
        (restrict V (head Q j))) := by
  dsimp only
  obtain ⟨U, hU, _, hw, _, hsub, _, _, _, _, _⟩ :=
    exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  refine ⟨U, hU, hw, hsub, ?_⟩
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+2) (invFamily hn (k+1)) K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
      (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by
    rw [head_append_tail]; exact hb.1
  have hsplit := (isGeoTestTower_append_iff _ _ _).mp ht
  intro j
  have hpref := ((isGeoTestTower_iff_head_tail _ _ j).mp hsplit.2).1
  exact contact_remainder_domain K hK U _ hw _ _
    ((isGeoTestTower_append_iff _ _ _).mpr ⟨hsplit.1, hpref⟩)


/-- The actual remaining-tail projection between the entire chosen final and prefix opens. -/
def contactPrefixProjection (Q : BlowupTower X Y) (V : Opens X) (j : ℕ) :
    openPreimage Q V → openPreimage (head Q j) V := fun z =>
  ⟨(tail Q j).proj z, by
    change ((head Q j).proj ∘ (tail Q j).proj) (z : Y) ∈ V
    rw [← proj_eq_comp Q j]
    exact z.property⟩

/-- This genuine open-subtype lift of the original tail projection is holomorphic. -/
theorem contMDiff_contactPrefixProjection (Q : BlowupTower X Y) (V : Opens X) (j : ℕ) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (contactPrefixProjection Q V j) := by
  exact (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((tail Q j).contMDiff_proj.comp contMDiff_subtype_val)

/-- Only actual original zero-level data produce every genuine whole contact prefix order equation. -/
theorem contactRemainder_actual_prefix_analytic (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain (k+2) K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      maskB K H p₀ ≤ V ∧
      ∀ j : ℕ, let J := geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V (head Q j));
        IsInvDomain (k+1) J ∧ (nmPart J).IsCoherent ∧
          ∀ q : ℕ, IsComplexAnalyticSubset (n := n)
            (contactPrefixProjection Q V j ⁻¹' ordGe J q) := by
  dsimp only
  obtain ⟨U,hU,hw,hsub,hD⟩ := contactRemainder_actual_prefix_domain hn K hK hmax R hcan p hp hns hl
  refine ⟨U,hU,hw,hsub,?_⟩
  intro j
  have hd := hD j
  have hcoh := isCoherent_nonmonomialPartAlong hn hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isSNCDivisor hd.isWellFormed.isTransverse hd.isWellFormed.isCoherent hd.isNonzeroAlongAt
  refine ⟨hd,hcoh,?_⟩
  intro q
  apply AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_contactPrefixProjection _ _ _)
  cases q with
  | zero =>
    change IsComplexAnalyticSubset (n := n) (GermIdealOrder.cosupport n _ _ 0)
    rw [GermIdealOrder.cosupport_zero
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hd.isWellFormed.isClosedSubmanifold_N
  | succ q =>
    exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hcoh
      hd.isWellFormed.isClosedSubmanifold_N (Nat.succ_pos q)

end
end Hironaka.HironakaOriginalWholeContactRemainderDomain
