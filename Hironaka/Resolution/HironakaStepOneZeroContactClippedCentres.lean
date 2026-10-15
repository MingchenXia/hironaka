/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.SharpGeometryExact
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderExtension
import Hironaka.Resolution.HironakaStageCenters


/-!
# Actual zero-contact stalk dictionary and admissible clipped original centres

The genuine closed selected/remaining component partition produces the actual
selected-complement open. Entire controlled ideals agree on its entire inverse
image at every original parent-test prefix. Smooth strict carriers internally
produce coherent controlled colons without centre containment in the remainder.
Thus EVERY ambient function has the SAME actual ideal-stalk membership at every
remaining point, and EVERY Nat along-carrier order threshold agrees there.

Each real original centre intersected with the actual remaining strict carrier
has the original centre germ locally. This internally produces closed smoothness,
actual cosupport containment and normal crossings with precisely the retained
empty historical entries plus the actual exceptional boundary. Actual induction
produces this admissibility for EVERY literal original centre. The original maps
remain blowups along their ORIGINAL centres; no clipped blowup map is inferred.

Original domain-three maximal-order and literal canonical Step1 data produce ONE
true chosen tangent open, the SAME remainder, the full original masked record
dictionary, all-prefix domain two, ALL stalk/order dictionaries and all literal
clipped centres jointly. The actual original invFamily3 companion consumer
internally supplies its own domain, maximal order and literal canonical Step1.
Private output propositions abbreviate ONLY conclusions, never supplied inputs.

Clipped-tower construction/comparison, candidate canonicality, deeper zero-contact
histories, cross-contact patch descent, whole original zero-level/General3
superlevels and general noncompact global termination remain OPEN.
Blueprint: `hironaka-step-one-zero-contact-clipped-centres-extension.tex`.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneZeroContactClippedCentres
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction DropMembers
  GermIdealOrder BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberTailExtension
  HironakaStepOneMemberLowerExtension MarkedIdealBiholomorphism
  HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaStepOneZeroContactRemainderExtension MarkedIdealRestrictOpen
  HomogenizedGlueingTower GlobalComponents MemberInterTowerAlong NormalCrossings
  HironakaStageCenters HironakaCoherentTransformExtension CodimOneSupportAlong
open StepOneLowerDomain StepOneValue StepOneRegime CanonicalCentres
  HironakaDimensionThreeStepOneLowerAnalyticLoci ContactEquivalenceAlong MaximalContactAlongTower
  TangentDirectionAlong ContactStageKept ContactStageInvDomain HomogenizedIdealAlong HomogenizedIdealAlongTower
  HironakaGeneralThreeNonspecialAnalyticLoci MaxLocusLocal BlowupTowerIsomorphism
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem partition (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) :
    L.N = remainingComponents (n := n) L.N L.cosupp ∪ selectedComponents (n := n) L.N L.cosupp ∧
      Disjoint (remainingComponents (n := n) L.N L.cosupp) (selectedComponents (n := n) L.N L.cosupp) := by
  rw [remainingComponents_eq_diff_selected hN]
  have hs : selectedComponents (n := n) L.N L.cosupp ⊆ L.N := by
    rintro x ⟨B, ⟨hB, _⟩, hx⟩
    exact subset_of_mem_globalComponents (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hB hx
  exact ⟨(sdiff_union_of_subset hs).symm, disjoint_sdiff_left⟩

private def remainingOpen (L : MarkedIdeal n X) (hN : IsClosedSubmanifold n L.N) : Opens X :=
  ⟨(selectedComponents (n := n) L.N L.cosupp)ᶜ,
    (isClosedSubmanifold_selectedComponents hN L.cosupp).1.isOpen_compl⟩

private theorem strict_geometry (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    IsClosedSubmanifold n (geoTransformAlong (contactRemainderMarked L k) T).N ∧
      ∀ x ∈ (geoTransformAlong (contactRemainderMarked L k) T).N,
        ∀ᶠ y in 𝓝 x, y ∈ (geoTransformAlong (contactRemainderMarked L k) T).N ↔
          y ∈ (geoTransformAlong L T).N := by
  have hR := isClosedSubmanifold_remainingComponents hN L.cosupp
  have hS := isClosedSubmanifold_selectedComponents hN L.cosupp
  obtain ⟨hp, hd⟩ := partition L hN
  have hr : (geoTransformAlong (contactRemainderMarked L k) T).N =
      strictAlong T (remainingComponents (n := n) L.N L.cosupp) := N_geoTransformAlong _ T
  have hf : (geoTransformAlong L T).N = strictAlong T L.N := N_geoTransformAlong L T
  have hev : ∀ x ∈ (geoTransformAlong (contactRemainderMarked L k) T).N,
      ∀ᶠ y in 𝓝 x, y ∈ (geoTransformAlong (contactRemainderMarked L k) T).N ↔
        y ∈ (geoTransformAlong L T).N := by
    intro x hx
    rw [hr] at hx ⊢
    rw [hf]
    exact eventually_mem_strictAlong_iff_of_closed_partition hR.1 hS.1 hd hp T hx
  refine ⟨⟨?_, ?_⟩, hev⟩
  · rw [hr]; exact isClosed_strictAlong T hR.1
  · intro x hx
    obtain ⟨d, hd⟩ := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT).1.2
      x ((hev x hx).self_of_nhds.mp hx)
    exact ⟨d, CodimOneSupport.regularAtDim_of_eventually_mem_iff
      ((hev x hx).mono fun _ h => h.symm) hd⟩

private theorem coherent (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower L T →
      (geoTransformAlong (contactRemainderMarked L k) T).ideal.IsCoherent
  | _, .refl, _ => hI
  | _, .step T C π hπ, hT => by
    exact isCoherent_geoTransform_ideal_of_smooth_strict _
      (coherent L k hN hI T hT.1) hπ (strict_geometry L k hN hI _ hT).1

private theorem remainder_restrict (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) (O : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower L T →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) (contactRemainderMarked L k)) (restrict O T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T O → Y)
          (geoTransformAlong (contactRemainderMarked L k) T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) (contactRemainderMarked L k))
      (restrict O T)).geoTransform ((Subtype.val : openPreimage T O → _) ⁻¹' C) _ = _
    rw [remainder_restrict L k hN hI O T hT.1]
    exact geoTransform_pullback_val (coherent L k hN hI T hT.1) hπ
      (coherent L k hN hI _ hT) (openPreimage T O) _

theorem remainder_controlled_ideal_open_eq (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) :
    let O := openPreimage T (remainingOpen L hN)
    GermIdeal.pullback (m := n) (Subtype.val : O → Y)
      (geoTransformAlong (contactRemainderMarked L k) T).ideal =
      GermIdeal.pullback (m := n) (Subtype.val : O → Y) (geoTransformAlong L T).ideal := by
  dsimp only
  let G := remainingOpen L hN
  let M := MarkedIdeal.pullback (Subtype.val : G → X) L
  let A := MarkedIdeal.pullback (Subtype.val : G → X) (contactRemainderMarked L k)
  have hi : A = ({ M with E := A.E } : MarkedIdeal n G) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · change (Subtype.val : G → X) ⁻¹' remainingComponents (n := n) L.N L.cosupp =
        (Subtype.val : G → X) ⁻¹' L.N
      ext x
      rw [remainingComponents_eq_diff_selected hN]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    · rfl
    · rfl
    · rfl
  have hfields := (geoTransformAlong_withE (X := CMfd.of (n := n) G) M A.E (restrict G T)).2.1
  rw [← hi] at hfields
  have ha := congrArg MarkedIdeal.ideal (remainder_restrict L k hN hI G T hT)
  have hm := congrArg MarkedIdeal.ideal (geoTransformAlong_restrict G hN hI T hT)
  exact ha.symm.trans (hfields.trans hm)

private theorem stalks_of_open_eq (I J : GermIdeal n Y) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (O : Opens Y) (heq : GermIdeal.pullback (m := n) (Subtype.val : O → Y) I =
      GermIdeal.pullback (m := n) (Subtype.val : O → Y) J) (x : Y) (hx : x ∈ O) :
    ∀ g : Y → ℂ, I.mem x g ↔ J.mem x g := by
  let p : O := ⟨x, hx⟩
  have transfer (A B : GermIdeal n Y) (hA : A.IsCoherent) (hB : B.IsCoherent)
      (hAB : GermIdeal.pullback (m := n) (Subtype.val : O → Y) A =
        GermIdeal.pullback (m := n) (Subtype.val : O → Y) B) (g : Y → ℂ) (hg : A.mem x g) : B.mem x g := by
    have hr := comp_val_mem_pullback_val O (x := p) hA hg
    rw [hAB] at hr
    have hb := (mem_pullback_val_iff O hB).mp hr
    apply HomogenizedIdeal.mem_congr hB hb
    filter_upwards [O.isOpen.mem_nhds hx] with y hy
    exact extendOpens_val O (g ∘ Subtype.val) ⟨y, hy⟩
  exact fun g => ⟨transfer I J hI hJ heq g, transfer J I hJ hI heq.symm g⟩

theorem remainder_actual_stalk_and_all_orders (L : MarkedIdeal n X) (k : ℕ)
    (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T)
    (x : Y) (hx : x ∈ (geoTransformAlong (contactRemainderMarked L k) T).N) :
    (∀ g : Y → ℂ, (geoTransformAlong (contactRemainderMarked L k) T).ideal.mem x g ↔
      (geoTransformAlong L T).ideal.mem x g) ∧
    ∀ q : ℕ, x ∈ cosupport n (geoTransformAlong (contactRemainderMarked L k) T).N
        (geoTransformAlong (contactRemainderMarked L k) T).ideal q ↔
      x ∈ cosupport n (geoTransformAlong L T).N (geoTransformAlong L T).ideal q := by
  have hc := coherent L k hN hI T hT
  have hf := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT).2
  let O := openPreimage T (remainingOpen L hN)
  have hxO : x ∈ O := by
    change T.proj x ∉ selectedComponents (n := n) L.N L.cosupp
    have hp : T.proj x ∈ remainingComponents (n := n) L.N L.cosupp :=
      strictAlong_subset_preimage T (isClosedSubmanifold_remainingComponents hN L.cosupp).1
        (by simpa only [N_geoTransformAlong, contactRemainderMarked] using hx)
    exact fun hs => Set.disjoint_left.mp (partition L hN).2 hp hs
  have hm := stalks_of_open_eq _ _ hc hf O
    (remainder_controlled_ideal_open_eq L k hN hI T hT) x hxO
  have hev := (strict_geometry L k hN hI T hT).2 x hx
  refine ⟨hm, fun q => ?_⟩
  constructor
  · rintro ⟨hxa, ho⟩
    refine ⟨hev.self_of_nhds.mp hxa, fun g hg => ?_⟩
    obtain ⟨f, hf, hgf⟩ := ho g ((hm g).mpr hg)
    refine ⟨f, hf, ?_⟩
    filter_upwards [hev, hgf] with y hy hgy hyN
    exact hgy (hy.mpr hyN)
  · rintro ⟨hxb, ho⟩
    refine ⟨hx, fun g hg => ?_⟩
    obtain ⟨f, hf, hgf⟩ := ho g ((hm g).mp hg)
    refine ⟨f, hf, ?_⟩
    filter_upwards [hev, hgf] with y hy hgy hyN
    exact hgy (hy.mp hyN)

private theorem boundary (L : MarkedIdeal n X) (k : ℕ) (hk : k ≤ L.E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (contactRemainderMarked L k) T).E =
        List.replicate k ∅ ++ (geoTransformAlong L T).E.drop k
  | _, .refl => rfl
  | _, .step T C π hπ => by
    change (geoTransformAlong (contactRemainderMarked L k) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C] =
      List.replicate k ∅ ++
        ((geoTransformAlong L T).E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]).drop k
    rw [boundary L k hk T]
    have hkT : k ≤ ((geoTransformAlong L T).E.map (BlowupStrictSubmanifold.geoStrictTransform π C)).length :=
      by simpa using hk.trans (length_E_le_length_E_geoTransformAlong L T)
    rw [List.map_append, List.map_replicate, List.drop_append_of_le_length hkT]
    have hempty : BlowupStrictSubmanifold.geoStrictTransform π C ∅ = ∅ := by
      simp [BlowupStrictSubmanifold.geoStrictTransform]
    simp only [hempty, List.map_drop, List.append_assoc]

theorem remainder_clipped_centre_isAdmissible (L : MarkedIdeal n X) (k : ℕ)
    (hk : k ≤ L.E.length) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) (C : Set Y)
    (hC : (geoTransformAlong L T).IsAdmissibleCentre C) :
    (geoTransformAlong (contactRemainderMarked L k) T).IsAdmissibleCentre
      (C ∩ (geoTransformAlong (contactRemainderMarked L k) T).N) := by
  let A := geoTransformAlong (contactRemainderMarked L k) T
  let B := geoTransformAlong L T
  have hgeom := strict_geometry L k hN hI T hT
  have hnear : ∀ x ∈ C ∩ A.N, ∀ᶠ y in 𝓝 x, y ∈ C ∩ A.N ↔ y ∈ C := by
    intro x hx
    filter_upwards [hgeom.2 x hx.2] with y hy
    exact ⟨fun h => h.1, fun hyC => ⟨hyC, hy.mpr (hC.subset_N hyC)⟩⟩
  have hclosed : IsClosedSubmanifold n (C ∩ A.N) := by
    refine ⟨hC.1.1.inter hgeom.1.1, ?_⟩
    intro x hx
    obtain ⟨d, hd⟩ := hC.1.2 x hx.1
    exact ⟨d, CodimOneSupport.regularAtDim_of_eventually_mem_iff
      ((hnear x hx).mono fun _ h => h.symm) hd⟩
  have hcs : C ∩ A.N ⊆ A.cosupp := by
    intro x hx
    have hq := (remainder_actual_stalk_and_all_orders L k hN hI T hT x hx.2).2 L.d
    have hdA : A.d = L.d := d_geoTransformAlong _ T
    have hdB : B.d = L.d := d_geoTransformAlong L T
    change x ∈ cosupport n A.N A.ideal A.d
    rw [hdA]
    apply hq.mpr
    have hcx := hC.2.1 hx.1
    change x ∈ cosupport n B.N B.ideal B.d at hcx
    simpa only [hdB] using hcx
  have hncDrop : HasNormalCrossings n C (B.E.drop k) :=
    NormalCrossingsComparison.hasNormalCrossings_of_forall_mem hC.2.2
      (fun _ h => List.mem_of_mem_drop h)
  have hncClip : HasNormalCrossings n (C ∩ A.N) (B.E.drop k) := by
    apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
    exact fun x hx => ⟨C, hx.1, hnear x hx, hncDrop⟩
  have hncPad : HasNormalCrossings n (C ∩ A.N) (List.replicate k ∅ ++ B.E.drop k) := by
    apply hasNormalCrossings_of_forall_disjoint hncClip
    intro F hF hn
    rcases List.mem_append.mp hF with hF | hF
    · have hf : F = ∅ := List.eq_of_mem_replicate hF
      rw [hf]; exact disjoint_empty _
    · exact False.elim (hn hF)
  refine ⟨hclosed, hcs, ?_⟩
  change HasNormalCrossings n (C ∩ A.N) (geoTransformAlong (contactRemainderMarked L k) T).E
  rw [boundary L k hk T]
  exact hncPad

theorem remainder_all_literal_clipped_centres (L : MarkedIdeal n X) (k : ℕ)
    (hk : k ≤ L.E.length) (hN : IsClosedSubmanifold n L.N) (hI : L.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower L T →
      StageCentres (fun P C => (geoTransformAlong (contactRemainderMarked L k) P).IsAdmissibleCentre
        (C ∩ (geoTransformAlong (contactRemainderMarked L k) P).N)) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    exact ⟨remainder_all_literal_clipped_centres L k hk hN hI T hT.1,
      remainder_clipped_centre_isAdmissible L k hk hN hI T hT.1 C hT.2⟩

/-- This proposition abbreviates ONLY the produced conclusion. -/
private def clippedOutput (K : MarkedIdeal n X) (R : BlowupTower X Y) (p : Y) : Prop :=
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
      (∀ j : ℕ, let P := head Q j
        let χ := nestedDiffeo (openPreimage P V)
          (openPreimage (restrict V P) (nestedOpens V W)) (openPreimage P W)
          (mem_openPreimage_restrict_nestedOpens V W P) (openPreimage_mono P hW)
        let A := geoTransformAlong (contactRemainderMarked L K.E.length) (restrict V P)
        let B := geoTransformAlong L (restrict V P)
        IsInvDomain 2 A ∧
          MarkedIdeal.pullback χ (geoTransformAlong (StepOneValueMasked.lowerMarkedB K H p₀) (restrict W P)) =
            MarkedIdeal.pullback
              (Subtype.val : openPreimage (restrict V P) (nestedOpens V W) → openPreimage P V) A ∧
          ∀ x ∈ A.N,
            (∀ g : openPreimage P V → ℂ, A.ideal.mem x g ↔ B.ideal.mem x g) ∧
              ∀ q : ℕ, x ∈ cosupport n A.N A.ideal q ↔ x ∈ cosupport n B.N B.ideal q) ∧
      StageCentres (fun P C => (geoTransformAlong (contactRemainderMarked L K.E.length) P).IsAdmissibleCentre
        (C ∩ (geoTransformAlong (contactRemainderMarked L K.E.length) P).N)) (restrict V Q)

theorem exists_actual_zero_contact_clipped_centres (hn : 0 < n)
    (K : MarkedIdeal n X) (hK : IsInvDomain 3 K)
    (hmax : IsMaximalOrderAlong K.N K.ideal K.d) (R : BlowupTower X Y)
    (hcan : IsCanonical K (Seq.StepOneValueMasked.stepOneInvM (invFamily hn 2) K) R)
    (p : Y) (hp : p ∈ (geoTransformAlong K R).cosupp) (hns : ¬ IsSpecial K R p)
    (hl : level K R p = 0) : clippedOutput K R p := by
  obtain ⟨U, hU, hw, hW, hinit, hpref⟩ :=
    contactRemainder_actual_masked_prefix_eq hn K hK hmax R hcan p hp hns hl
  dsimp only [clippedOutput]
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let w := (tangentChoice K (H.proj p₀)).2
  let V := openPreimage H U
  let L := contactMarkedKept K w H V
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (invFamily hn 2)
    K hK hmax hn R hcan
  have ht : IsGeoTestTower (barMarked K) (H.append Q) := by
    dsimp only [H, Q]; rw [head_append_tail]; exact hb.1
  have hH := ((isGeoTestTower_append_iff _ H Q).mp ht).1
  have hHa := ((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
    hK.isWellFormed.isCoherent hK.one_le_d).2 H).1.mp hH
  have hLN : IsClosedSubmanifold n L.N := isClosedSubmanifold_strictAlong_stage_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H hHa V subset_rfl
  have hLI : L.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (isCoherent_restrictedCoeff K hK.isWellFormed.isCoherent hK.isWellFormed.isClosedSubmanifold_N w H hH)
  have htV : IsGeoTestTower L (restrict V Q) := (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
    hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H Q ht V subset_rfl).1
  have hk : K.E.length ≤ L.E.length := by
    change K.E.length ≤ ((geoTransformAlong (barMarked K) H).E.map
      ((Subtype.val : V → _) ⁻¹' ·)).length
    rw [List.length_map]
    exact length_E_le_length_E_geoTransformAlong (barMarked K) H
  refine ⟨U, hU, hw, hW, hinit, ?_, ?_⟩
  · intro j
    have htP : IsGeoTestTower L (restrict V (head Q j)) := by
      have hparent := ((isGeoTestTower_iff_head_tail _ _ j).mp
        ((isGeoTestTower_append_iff _ H Q).mp ht).2).1
      exact (ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le K
        hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d U hw H (head Q j)
        ((isGeoTestTower_append_iff _ H (head Q j)).mpr ⟨hH, hparent⟩) V subset_rfl).1
    exact ⟨(hpref j).1, (hpref j).2,
      fun x hx => remainder_actual_stalk_and_all_orders (X := CMfd.of (n := n) V)
        L K.E.length hLN hLI (restrict V (head Q j)) htP x hx⟩
  · exact remainder_all_literal_clipped_centres (X := CMfd.of (n := n) V)
      L K.E.length hk hLN hLI (restrict V Q) htV

theorem exists_actual_general_three_clipped_centres (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hns : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hl : level (companionAt m T x) (companionTailAt m T x) p = 0) :
    clippedOutput
      (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
      (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
      (companionAt m T x) (companionTailAt m T x) p := by
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  exact exists_actual_zero_contact_clipped_centres
    (X := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.maskAt m T x))
    (Y := CMfd.of (n := n) (HironakaGeneralThreeNonspecialAnalyticLoci.patchAt m T x))
    hn (companionAt m T x) hK hmax (companionTailAt m T x) hcanK p hp hns hl

end
end Hironaka.HironakaStepOneZeroContactClippedCentres
