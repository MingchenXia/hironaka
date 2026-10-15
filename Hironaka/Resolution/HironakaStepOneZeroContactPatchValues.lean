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
import Hironaka.Invariant.ContactStageDimensionExact
import Hironaka.Resolution.HironakaStepOnePositiveAnalyticSuperlevels

/-!
# Actual enlarged zero-contact coefficient models with literal masked transforms

Original domain-three maximal order and actual constructed canonical Step1
internally supply the true chosen tangent open. Its WHOLE inverse image,
retaining boundaries excluded by maskB, supports the SAME coherent contact
coefficient datum and the actual restricted test tail. Every literal prefix
has a smooth dimension-at-most-two carrier, coherent ideal and ALL ordinary
ideal-order analytic predicates. Genuine nested-open tower identities produce
whole marked record equality with literal lowerMarkedB and exact ALL-order
predicate pullbacks at every original tail prefix. The final original
invFamily3 consumer internally produces its actual companion and ALL this
geometry on ONE chosen open. Its private output proposition abbreviates ONLY
the full conclusion; no caller output certificate is an input.

Enlarged-model global nonzero, lower invariant domain/canonicality, cross
contact/history gluing, whole original zero-level/General3 thresholds and
noncompact global G3 termination remain OPEN.
Blueprint: `hironaka-step-one-zero-contact-patch-values-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneZeroContactPatchValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HomogenizedIdealAlong HomogenizedIdealAlongTower TangentDirectionAlong StepOneValue StepOneLowerDomain StepOneRegime ContactStageKept
  ContactStageInvDomain GlobalComponents AnalyticDimensionBasics CodimOneSupportAlong
  HironakaDimensionThreeStepOneLowerAnalyticLoci HironakaCoherentTransformExtension
  HironakaGeneralThreeNonspecialAnalyticLoci HironakaStepOneMemberAcrossMaskValues
  HironakaGeneralTwoAnalyticSuperlevels CanonicalCentres
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen MaxLocusLocal BlowupTowerIsomorphism
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem contact_model_geometry {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append Q)) :
    let V := openPreimage H U
    let L := contactMarkedKept K w H V
    IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧ ResolutionInvariantSpec.DimLE n L.N 2 ∧
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
  have hdim := dimLE_strictAlong_stage K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa hK.dimLE
  have ht := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H Q hT
    (openPreimage H U) subset_rfl
  exact ⟨hN, hI, hdim, ht⟩

/-- Original actual zero-level data internally produce the SAME enlarged contact model. -/
theorem exists_actual_enlarged_zero_contact_model (hn : 0 < n)
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
    ∃ U : Opens X, (U : Set X) = (tangentChoice K (H.proj p₀)).1 ∧ H.proj p₀ ∈ U ∧
      IsTangentDirectionAlong K.N K.ideal K.d U w ∧
      let V := openPreimage H U
      let L := contactMarkedKept K w H V
      lowerMask K (level K R p) H p₀ = maskB K H p₀ ∧
      maskB K H p₀ ≤ V ∧ IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧
        ResolutionInvariantSpec.DimLE n L.N 2 ∧ IsGeoTestTower L (restrict V Q) ∧
        (geoTransformAlong L (restrict V Q)).cosupp =
          (Subtype.val : openPreimage Q V → Y) ⁻¹' (geoTransformAlong K R).cosupp := by
  dsimp only
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
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

private theorem prefix_geometry_and_order (L : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (hdim : ResolutionInvariantSpec.DimLE n L.N 2) (hd : 1 ≤ L.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    ∀ j : ℕ, let J := geoTransformAlong L (head T j)
      IsClosedSubmanifold n J.N ∧ J.ideal.IsCoherent ∧
        ResolutionInvariantSpec.DimLE n J.N 2 ∧ 1 ≤ J.d ∧
        ∀ q : ℕ, IsComplexAnalyticSubset (n := n)
          (GermIdealOrder.cosupport n J.N J.ideal q) := by
  intro j
  dsimp only
  have ht := ((isGeoTestTower_iff_head_tail L T j).mp hT).1
  obtain ⟨hNj, hIj⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI (head T j) ht
  refine ⟨hNj, hIj, InvDomainTowerAlong.dimLE_geoTransformAlong hN hI hdim _ ht, ?_, ?_⟩
  · rwa [d_geoTransformAlong]
  · intro q
    by_cases hq : q = 0
    · rw [hq, GermIdealOrder.cosupport_zero (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hIj)]
      exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hNj
    · exact isComplexAnalyticSubset_cosupport_along hIj hNj (by omega)

/-- All literal prefixes retain genuine geometry and ALL natural ideal-order analytic predicates. -/
theorem enlarged_zero_contact_prefix_geometry_and_order_predicates (hn : 0 < n)
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
      ∀ j : ℕ, let J := geoTransformAlong L (head (restrict V Q) j)
        IsClosedSubmanifold n J.N ∧ J.ideal.IsCoherent ∧
          ResolutionInvariantSpec.DimLE n J.N 2 ∧ 1 ≤ J.d ∧
          ∀ q : ℕ, IsComplexAnalyticSubset (n := n)
            (GermIdealOrder.cosupport n J.N J.ideal q) := by
  dsimp only
  obtain ⟨U, hU, _, hw, _, hsub, hN, hI, hdim, ht, _⟩ :=
    exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  refine ⟨U, hU, hw, hsub, prefix_geometry_and_order _ hN hI hdim ?_ _ ht⟩
  exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _

private theorem order_dictionary_of_nested_record (S : MarkedIdeal n X) (J : MarkedIdeal n Y)
    (B : Opens Y) (χ : CMfd.of (n := n) B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (hS : S.ideal.IsCoherent) (hJ : J.ideal.IsCoherent)
    (heq : MarkedIdeal.pullback χ S = MarkedIdeal.pullback (Subtype.val : B → Y) J) :
    ∀ q : ℕ, χ ⁻¹' GermIdealOrder.cosupport n S.N S.ideal q =
      (Subtype.val : B → Y) ⁻¹' GermIdealOrder.cosupport n J.N J.ideal q := by
  intro q
  let S' : MarkedIdeal n X := ⟨S.N, S.E, S.ideal, q⟩
  let J' : MarkedIdeal n Y := ⟨J.N, J.E, J.ideal, q⟩
  have hN : χ ⁻¹' S.N = (Subtype.val : B → Y) ⁻¹' J.N := congrArg (fun A : MarkedIdeal n B => A.N) heq
  have hE : S.E.map (χ ⁻¹' ·) = J.E.map ((Subtype.val : B → Y) ⁻¹' ·) :=
    congrArg (fun A : MarkedIdeal n B => A.E) heq
  have hI : GermIdeal.pullback (m := n) χ S.ideal =
      GermIdeal.pullback (m := n) (Subtype.val : B → Y) J.ideal :=
    congrArg (fun A : MarkedIdeal n B => A.ideal) heq
  have hq : MarkedIdeal.pullback χ S' = MarkedIdeal.pullback (Subtype.val : B → Y) J' :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE hI rfl
  have h1 := MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := χ) (𝔪 := S') hS
  have h2 := cosupp_pullback_val J' (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hJ) B
  change χ ⁻¹' S'.cosupp = (Subtype.val : B → Y) ⁻¹' J'.cosupp
  rw [← h1, hq, h2]

private theorem nested_contact_transform_identity {Z : CMfd.{u} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (U : Opens X) (w : X → ℂ) (hw : IsTangentDirectionAlong K.N K.ideal K.d U w)
    (H : BlowupTower X Y) (P : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked K) (H.append P))
    (W : Opens Y) (hW : W ≤ openPreimage H U) :
    let V := openPreimage H U
    let χ := nestedDiffeo (openPreimage P V)
      (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
      (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
    MarkedIdeal.pullback χ (geoTransformAlong (contactMarkedKept K w H W) (restrict W P)) =
      MarkedIdeal.pullback
        (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
        (geoTransformAlong (contactMarkedKept K w H V) (restrict V P)) ∧
      ∀ q : ℕ, χ ⁻¹' GermIdealOrder.cosupport n
        (geoTransformAlong (contactMarkedKept K w H W) (restrict W P)).N
        (geoTransformAlong (contactMarkedKept K w H W) (restrict W P)).ideal q =
        (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V) ⁻¹'
          GermIdealOrder.cosupport n (geoTransformAlong (contactMarkedKept K w H V) (restrict V P)).N
            (geoTransformAlong (contactMarkedKept K w H V) (restrict V P)).ideal q := by
  dsimp only
  have hH := ((isGeoTestTower_append_iff (barMarked K) H P).mp hT).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  obtain ⟨hNV, hIV, _, htV, _⟩ := contact_model_geometry K hK U w hw H P hT
  have hNW := isClosedSubmanifold_strictAlong_stage_of_le K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa W hW
  have hglobal := isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent
    hK.isWellFormed.isClosedSubmanifold_N w H hH
  have hIW : (contactMarkedKept K w H W).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hglobal
  have htW := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H P hT W hW).1
  have hinit : MarkedIdeal.pullback (Subtype.val : nestedOpens (openPreimage H U) W → openPreimage H U)
      (contactMarkedKept K w H (openPreimage H U)) =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (contactMarkedKept K w H W) :=
    pullback_val_pullback_val hglobal hW
  have hiso := isTowerIso_restrict_nestedOpens (X := Y) hW P
  have h1 := IsTowerIso.geoTransformAlong_eq (nestedOpensDiffeo (n := n) hW) hNW hIW hiso htW
  rw [← hinit] at h1
  have h2 := geoTransformAlong_restrict (U := nestedOpens (openPreimage H U) W) hNV hIV
    (restrict (openPreimage H U) P) htV
  have hrec := h1.symm.trans h2
  have hIS := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hNW hIW _ htW).2
  have hIJ := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hNV hIV _ htV).2
  exact ⟨hrec, order_dictionary_of_nested_record _ _ _ _ hIS hIJ hrec⟩

/-- Entire original masked controlled marked records and ALL ordinary-order predicates agree at every prefix. -/
theorem enlarged_zero_contact_masked_transform_identity (hn : 0 < n)
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
      MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) L =
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) ∧
      ∀ j : ℕ, let P := head Q j
        let χ := nestedDiffeo (openPreimage P V)
          (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
          (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
        MarkedIdeal.pullback χ
          (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
          MarkedIdeal.pullback
            (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
            (geoTransformAlong L (restrict V P)) ∧
          ∀ q : ℕ, χ ⁻¹' GermIdealOrder.cosupport n
            (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)).N
            (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)).ideal q =
            (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V) ⁻¹'
              GermIdealOrder.cosupport n (geoTransformAlong L (restrict V P)).N
                (geoTransformAlong L (restrict V P)).ideal q := by
  dsimp only
  obtain ⟨U, hU, _, hw, _, hsub, _, _, _, _, _⟩ :=
    exists_actual_enlarged_zero_contact_model hn K hK hmax R hcan p hp hns hl
  refine ⟨U, hU, hw, hsub, ?_, ?_⟩
  · have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
    have hH := ((isGeoTestTower_iff_head_tail (barMarked K) R (regimeRun (stepRegime K (level K R p)) R p)).mp hb.1).1
    exact pullback_val_pullback_val
      (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N _ _ hH) hsub
  · intro j
    have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
    obtain ⟨hH, hQ⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R (regimeRun (stepRegime K (level K R p)) R p)).mp hb.1
    have hP := ((isGeoTestTower_iff_head_tail _ _ j).mp hQ).1
    have hT := (isGeoTestTower_append_iff (barMarked K) _ _).mpr ⟨hH, hP⟩
    exact nested_contact_transform_identity K hK U _ hw _ _ hT _ hsub

/-- Only the full genuine conclusion, factored to keep elaboration at the default budget. -/
private def enlargedContactOutput (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) : Prop :=
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
      IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧ ResolutionInvariantSpec.DimLE n L.N 2 ∧
      IsGeoTestTower L (restrict V Q) ∧
      (geoTransformAlong L (restrict V Q)).cosupp =
        (Subtype.val : openPreimage Q V → Y) ⁻¹'
          (geoTransformAlong K R).cosupp ∧
      (∀ j : ℕ, let J := geoTransformAlong L (head (restrict V Q) j)
        IsClosedSubmanifold n J.N ∧ J.ideal.IsCoherent ∧ ResolutionInvariantSpec.DimLE n J.N 2 ∧
          1 ≤ J.d ∧ ∀ q : ℕ, IsComplexAnalyticSubset (n := n)
            (GermIdealOrder.cosupport n J.N J.ideal q)) ∧
      MarkedIdeal.pullback (Subtype.val : nestedOpens V W → V) L =
        MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (StepOneValueMasked.lowerMarkedB K H p₀) ∧
      ∀ j : ℕ, let P := head Q j
        let χ := nestedDiffeo (openPreimage P V)
          (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
          (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
        MarkedIdeal.pullback χ
          (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
          MarkedIdeal.pullback
            (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V)
            (geoTransformAlong L (restrict V P)) ∧
          ∀ q : ℕ, χ ⁻¹' GermIdealOrder.cosupport n
            (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)).N
            (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)).ideal q =
            (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V) ⁻¹'
              GermIdealOrder.cosupport n (geoTransformAlong L (restrict V P)).N
                (geoTransformAlong L (restrict V P)).ideal q

private theorem actual_enlarged_contact_output (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) : enlargedContactOutput K R p := by
  dsimp only [enlargedContactOutput]
  obtain ⟨U, hU, hw, hW, hinit, hdict⟩ := enlarged_zero_contact_masked_transform_identity
    hn K hK hmax R hcan p hp hns hl
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2) K hK hmax hn R hcan
  have hsplit : (head R (regimeRun (stepRegime K (level K R p)) R p)).append
      (tail R (regimeRun (stepRegime K (level K R p)) R p)) = R := head_append_tail R _
  have hT : IsGeoTestTower (barMarked K)
      ((head R (regimeRun (stepRegime K (level K R p)) R p)).append
        (tail R (regimeRun (stepRegime K (level K R p)) R p))) := by rw [hsplit]; exact hb.1
  obtain ⟨hN, hI, hd, ht, hcs⟩ := contact_model_geometry K hK U _ hw _ _ hT
  rw [hsplit, hb.2.2] at hcs
  refine ⟨U, hU, hw, hW, hN, hI, hd, ht, hcs,
    prefix_geometry_and_order _ hN hI hd ?_ _ ht, hinit, hdict⟩
  exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _

/-- The literal original invFamily3 internally supplies ONE enlarged model with ALL prefix and masked dictionaries. -/
theorem exists_actual_general_three_enlarged_zero_contact_model (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hns : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hl : level (companionAt m T x) (companionTailAt m T x) p = 0) :
    enlargedContactOutput
      (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
      (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
      (companionAt m T x) (companionTailAt m T x) p := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  exact actual_enlarged_contact_output
    (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
    (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
    hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK p hp hns hl

end
end Hironaka.HironakaStepOneZeroContactPatchValues
