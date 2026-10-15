/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneZeroContactPatchValues

/-!
# Genuine enlarged zero-contact remainders with whole original mask dictionaries

The real locally finite smooth global component family removes only the actual
contact components contained in its true cosupport. Analytic continuation and
actual coherent generators produce nonzero along EVERY remaining point. The
real closed component partition supplies exact strict-transform germs at every
original parent-test prefix. Smooth strict carriers internally produce coherent
controlled colons and preserve nonzero without candidate-centre containment.

Actual Giraud centre containment and genuine tangent contact geometry produce
transversality to ALL accumulated exceptional members. Literal historical index
positions are preserved by replacing the original boundary block with exactly
its original number of empty entries. Direct coordinate proofs show this empty
prefix preserves SNC and transversality, and the true map/append recursion proves
the entire boundary dictionary at every original prefix.

Original domain-three maximal-order and literal constructed Step1 data produce
ONE true chosen tangent open, a genuine domain-two remainder at EVERY actual tail
prefix, and equality of ENTIRE original masked marked records at every prefix.
Actual masked nonzero internally excludes all removed components on the SAME
whole original mask. Coherent open controlled-transform identities and the true
nested-open tower isomorphism give whole carrier/ideal/boundary/mark equality.
The final original invFamily3 consumer internally produces its SAME companion.
The private output proposition abbreviates ONLY the full conclusion.

Candidate global canonicality, deeper zero-contact history, cross-contact patch
descent, whole original zero-level/General3 thresholds and noncompact global G3
termination remain OPEN. No such conclusions are supplied as input certificates.
Blueprint: `hironaka-step-one-zero-contact-remainder-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneZeroContactRemainderExtension
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
variable {n : ℕ} {X Y : CMfd.{u} n}

def contactRemainderMarked {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (L : MarkedIdeal n M) (k : ℕ) : MarkedIdeal n M :=
  ⟨remainingComponents (n := n) L.N L.cosupp, List.replicate k ∅ ++ L.E.drop k, L.ideal, L.d⟩

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
    (hd : 1 ≤ L.d) (hDim : ResolutionInvariantSpec.DimLE n L.N 2) :
    IsClosedSubmanifold n (contactRemainderMarked L k).N ∧
      (contactRemainderMarked L k).ideal.IsCoherent ∧
      ResolutionInvariantSpec.DimLE n (contactRemainderMarked L k).N 2 ∧
      (∀ x ∈ (contactRemainderMarked L k).N,
        IsNonzeroAlongAt (contactRemainderMarked L k).N (contactRemainderMarked L k).ideal x) ∧
      (contactRemainderMarked L k).cosupp = L.cosupp ∩ (contactRemainderMarked L k).N := by
  have hA := isComplexAnalyticSubset_cosupport_along hI hN hd
  have hRN := isClosedSubmanifold_remainingComponents hN L.cosupp
  have hsub : (contactRemainderMarked L k).N ⊆ L.N := by
    change remainingComponents (n := n) L.N L.cosupp ⊆ L.N
    rw [remainingComponents_eq_diff_selected hN]
    exact sdiff_subset
  have hdim : ResolutionInvariantSpec.DimLE n (contactRemainderMarked L k).N 2 := by
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
    (hDim : ResolutionInvariantSpec.DimLE n L.N 2)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    IsClosedSubmanifold n (geoTransformAlong (contactRemainderMarked L k) T).N ∧
      ResolutionInvariantSpec.DimLE n (geoTransformAlong (contactRemainderMarked L k) T).N 2 ∧
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
    (hDim : ResolutionInvariantSpec.DimLE n L.N 2) :
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
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
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
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
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

private theorem contact_remainder_domain {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q)) :
    let V := openPreimage H U
    let L := contactMarkedKept K w H V
    IsInvDomain 2 (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V Q)) := by
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
  have hdim : ResolutionInvariantSpec.DimLE n L.N 2 := dimLE_strictAlong_stage K
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
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
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
      ∀ j : ℕ, IsInvDomain 2 (geoTransformAlong (contactRemainderMarked L K.E.length)
        (restrict V (head Q j))) := by
  dsimp only
  obtain ⟨U, hU, _, hw, _, hsub, _, _, _, _, _⟩ :=
    exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  refine ⟨U, hU, hw, hsub, ?_⟩
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
      (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by
    rw [head_append_tail]; exact hb.1
  have hsplit := (isGeoTestTower_append_iff _ _ _).mp ht
  intro j
  have hpref := ((isGeoTestTower_iff_head_tail _ _ j).mp hsplit.2).1
  exact contact_remainder_domain K hK U _ hw _ _
    ((isGeoTestTower_append_iff _ _ _).mpr ⟨hsplit.1, hpref⟩)

private theorem preimage_remaining_eq_of_nonzero (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d)
    (O : Opens X)
    (hnz : ∀ p ∈ (MarkedIdeal.pullback (Subtype.val : O → X) L).N,
      IsNonzeroAlongAt (MarkedIdeal.pullback (Subtype.val : O → X) L).N
        (MarkedIdeal.pullback (Subtype.val : O → X) L).ideal p) :
    (Subtype.val : O → X) ⁻¹' remainingComponents (n := n) L.N L.cosupp =
      (Subtype.val : O → X) ⁻¹' L.N := by
  have hcoh : (MarkedIdeal.pullback (Subtype.val : O → X) L).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  have hcs := cosupp_pullback_val L (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hI) O
  ext p
  rw [remainingComponents_eq_diff_selected hN]
  refine ⟨fun hp => hp.1, fun hp => ⟨hp, ?_⟩⟩
  intro hps
  have hnr : (p : X) ∉ remainingComponents (n := n) L.N L.cosupp := by
    rw [remainingComponents_eq_diff_selected hN]
    exact fun h => h.2 hps
  have hnear : ∀ᶠ y in 𝓝 (p : X), y ∈ L.N → y ∈ L.cosupp := by
    filter_upwards [(isClosedSubmanifold_remainingComponents hN L.cosupp).1.isOpen_compl.mem_nhds hnr] with y hy hyN
    have hys : y ∈ selectedComponents (n := n) L.N L.cosupp := by
      by_contra hnot
      exact hy (by rw [remainingComponents_eq_diff_selected hN]; exact ⟨hyN, hnot⟩)
    rcases hys with ⟨B, ⟨_, hBA⟩, hyB⟩
    exact hBA hyB
  obtain ⟨g, hg, hf⟩ := hnz p hp
  have hm := HomogenizedGlueing.eventually_mem hcoh hg
  have hv := continuous_subtype_val.continuousAt.tendsto.eventually hnear
  obtain ⟨q, ⟨hqN, hqg⟩, hqm, hqv⟩ := (hf.and_eventually (hm.and hv)).exists
  have hqcs : q ∈ (MarkedIdeal.pullback (Subtype.val : O → X) L).cosupp := by
    rw [hcs]
    exact hqv hqN
  exact hqg ((vanishesToOrderOn_one_iff hqN
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh _ _ hqm)).mp
      ((hqcs.2 g hqm).mono hd))

private theorem remainder_mask_eq (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (hd : 1 ≤ L.d)
    (hk : k ≤ L.E.length) (O : Opens X)
    (hnz : ∀ p ∈ (MarkedIdeal.pullback (Subtype.val : O → X) L).N,
      IsNonzeroAlongAt (MarkedIdeal.pullback (Subtype.val : O → X) L).N
        (MarkedIdeal.pullback (Subtype.val : O → X) L).ideal p)
    (hhist : ∀ B ∈ L.E.take k, ∀ p : O, (p : X) ∉ B) :
    MarkedIdeal.pullback (Subtype.val : O → X) (contactRemainderMarked L k) =
      MarkedIdeal.pullback (Subtype.val : O → X) L := by
  have hNrec := preimage_remaining_eq_of_nonzero L hN hI hd O hnz
  have hErec : (L.E.take k).map ((Subtype.val : O → X) ⁻¹' ·) = List.replicate k ∅ := by
    apply List.eq_replicate_iff.mpr
    refine ⟨?_, ?_⟩
    · simp only [List.length_map, List.length_take, Nat.min_eq_left hk]
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
      exact eq_empty_iff_forall_notMem.mpr (hhist A hA)
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hNrec
  · change (List.replicate k ∅ ++ L.E.drop k).map ((Subtype.val : O → X) ⁻¹' ·) =
      L.E.map ((Subtype.val : O → X) ⁻¹' ·)
    rw [List.map_append, List.map_replicate, preimage_empty]
    conv_rhs => rw [← List.take_append_drop k L.E, List.map_append, hErec]
  · rfl
  · rfl

private theorem contact_remainder_initial_mask {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q))
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (p₀ : Y) (hW : maskB K H p₀ ≤ openPreimage H U)
    (hwchoice : w = (tangentChoice K (H.proj p₀)).2) :
    let V := openPreimage H U
    let W := maskB K H p₀
    let L := contactMarkedKept K w H V
    MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) (contactRemainderMarked L K.E.length) =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) := by
  dsimp only
  let V := openPreimage H U
  let W := maskB K H p₀
  let L := contactMarkedKept K w H V
  have hH := ((isGeoTestTower_append_iff _ H Q).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hLN : IsClosedSubmanifold n L.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa V subset_rfl
  have hG := isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N w H hH
  have hLI : L.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hG
  have hinit : MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) L =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) := by
    dsimp only [L]
    rw [hwchoice] at hG ⊢
    exact pullback_val_pullback_val hG hW
  have hdom := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le K hK.isWellFormed
    hK.one_le_d hK.dimLE U hw H hH W hW
    (fun z hz _ => (interior_subset hz).2.2)
    (fun A hA z hz _ => (interior_subset hz).2.1 A hA)
  have hlower : IsInvDomain 2 (StepOneValueMasked.lowerMarkedB K H p₀) := by
    simpa only [hwchoice, StepOneValueMasked.lowerMarkedB, W] using hdom
  have hsmall := InvDomainTowerAlong.isInvDomain_pullback (nestedOpensDiffeo (n := n) hW) hlower
  rw [← hinit] at hsmall
  have hh : ∀ B ∈ L.E.take K.E.length, ∀ p : nestedOpens V W, (p : V) ∉ B := by
    intro B hB p
    change B ∈ ((geoTransformAlong (barMarked K) H).E.map ((Subtype.val : V → Y) ⁻¹' ·)).take K.E.length at hB
    rw [← List.map_take] at hB
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    have hpW : ((p : V) : Y) ∈ maskB K H p₀ := p.2
    exact (interior_subset hpW).2.1 A hA
  have heq := remainder_mask_eq (X := CMfd.of (n := n) V) L K.E.length hLN hLI
    (ContactIndependenceAlong.one_le_coeffMarkedAlong_d _) (contact_exceptional_boundary K hK H Q hT U w).1
    (nestedOpens V W) hsmall.isNonzeroAlongAt hh
  exact heq.trans hinit

private theorem remainder_transform_restrict (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hd : 1 ≤ L.d) (hDim : ResolutionInvariantSpec.DimLE n L.N 2) (O : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower L T →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) (contactRemainderMarked L k)) (restrict O T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T O → Y)
          (geoTransformAlong (contactRemainderMarked L k) T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := hT
    have ih := remainder_transform_restrict L k hN hI hd hDim O T hTT
    have hIT := (remainder_transform_coherent_nonzero L k hN hI hd hDim T hTT).1
    have hInew := (remainder_transform_coherent_nonzero L k hN hI hd hDim (.step T C π hπ) ⟨hTT, hC⟩).1
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) (contactRemainderMarked L k))
      (restrict O T)).geoTransform ((Subtype.val : openPreimage T O → _) ⁻¹' C) _ = _
    rw [ih]
    exact geoTransform_pullback_val hIT hπ hInew (openPreimage T O) _

theorem contactRemainder_original_mask_record_eq (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) :
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    let W := maskB K H p₀
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      ∃ hW : W ≤ openPreimage H U,
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) (contactRemainderMarked L K.E.length) =
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) := by
  dsimp only
  obtain ⟨U, hU, _, hw, _, hW, _, _, _, _, _⟩ :=
    exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  refine ⟨U, hU, hw, hW, ?_⟩
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
      (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by
    rw [head_append_tail]; exact hb.1
  exact contact_remainder_initial_mask K hK _ _ ht U _ hw _ hW rfl

private theorem contact_remainder_nested_transform {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (P : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append P))
    (p₀ : Y) (hW : maskB K H p₀ ≤ openPreimage H U)
    (hwchoice : w = (tangentChoice K (H.proj p₀)).2) :
    let V := openPreimage H U
    let W := maskB K H p₀
    let L := contactMarkedKept K w H V
    let χ := nestedDiffeo (openPreimage P V)
      (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
      (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
    MarkedIdeal.pullback χ (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
      MarkedIdeal.pullback
        (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
        (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P)) := by
  dsimp only
  let V := openPreimage H U
  let W := maskB K H p₀
  let L := contactMarkedKept K w H V
  have hH := ((isGeoTestTower_append_iff _ H P).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hLN : IsClosedSubmanifold n L.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa V subset_rfl
  have hLI : L.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N w H hH)
  have hdim : ResolutionInvariantSpec.DimLE n L.N 2 := dimLE_strictAlong_stage K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa hK.dimLE
  have htV : IsGeoTestTower L (restrict V P) := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H P hT V subset_rfl).1
  have htW := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H P hT W hW).1
  rw [hwchoice] at htW
  have hNW := isClosedSubmanifold_strictAlong_stage_of_le K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa W hW
  rw [hwchoice] at hNW
  have hIW : (StepOneValueMasked.lowerMarkedB K H p₀).ideal.IsCoherent := by
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N _ H hH)
  have hinit := contact_remainder_initial_mask K hK H P hT U w hw p₀ hW hwchoice
  have hiso := isTowerIso_restrict_nestedOpens (X := Y) hW P
  have h1 := IsTowerIso.geoTransformAlong_eq (nestedOpensDiffeo (n := n) hW) hNW hIW hiso htW
  rw [← hinit] at h1
  have h2 := remainder_transform_restrict (X := CMfd.of (n := n) V) L K.E.length hLN hLI
    (ContactIndependenceAlong.one_le_coeffMarkedAlong_d _) hdim (nestedOpens V W) (restrict V P) htV
  exact h1.symm.trans h2

/-- The complete genuine output, never a supplied hypothesis. -/
private def contactRemainderOutput (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) : Prop :=
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let w := (tangentChoice K (H.proj p₀)).2
    let W := maskB K H p₀
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      ∃ hW : W ≤ openPreimage H U,
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) (contactRemainderMarked L K.E.length) =
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) ∧
      ∀ j : ℕ, let P := head Q j
        let χ := nestedDiffeo (openPreimage P V)
          (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
          (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
        IsInvDomain 2 (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P)) ∧
          MarkedIdeal.pullback χ
            (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
            MarkedIdeal.pullback
              (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
              (geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P))

private theorem actual_contact_remainder_output (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) : contactRemainderOutput K R p := by
  dsimp only [contactRemainderOutput]
  obtain ⟨U, hU, _, hw, _, hW, _, _, _, _, _⟩ :=
    exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
      (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by
    rw [head_append_tail]; exact hb.1
  have hsplit := (isGeoTestTower_append_iff _ _ _).mp ht
  refine ⟨U, hU, hw, hW, contact_remainder_initial_mask K hK _ _ ht U _ hw _ hW rfl, ?_⟩
  intro j
  have hpref := ((isGeoTestTower_iff_head_tail _ _ j).mp hsplit.2).1
  have htp := (isGeoTestTower_append_iff _ _ _).mpr ⟨hsplit.1, hpref⟩
  exact ⟨contact_remainder_domain K hK U _ hw _ _ htp,
    contact_remainder_nested_transform K hK U _ hw _ _ htp _ hW rfl⟩

/-- The SAME enlarged remainder has a genuine lower domain at every original prefix
and its ENTIRE original masked controlled marked records agree. -/
theorem contactRemainder_actual_masked_prefix_eq (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) : contactRemainderOutput K R p :=
  actual_contact_remainder_output hn K hK hmax R hcan p hp hns hl

/-- Original literal General3 supplies its actual companion internally and produces
ONE genuine remainder with all-prefix domains and whole original mask dictionaries. -/
theorem exists_actual_general_three_contact_remainder (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hns : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hl : level (companionAt m T x) (companionTailAt m T x) p = 0) :
    contactRemainderOutput
      (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
      (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
      (companionAt m T x) (companionTailAt m T x) p := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  exact actual_contact_remainder_output
    (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
    (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
    hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK p hp hns hl

end
end Hironaka.HironakaStepOneZeroContactRemainderExtension
