/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalUntestedCompanionSmoothPullback
import Hironaka.Resolution.HironakaSmoothSubmersionCartesianTowerComposition
import Hironaka.Resolution.HironakaSmoothSubmersionCanonicalValueDimensionShift
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedGlobalTrace
/-! Whole original GENERAL values from true curve-reference geometry and
actual smooth codimension-one transport, without candidate TEST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalUntestedCurveSmoothValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCartesianTowerComposition HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionHistoricalControlledTail HironakaSmoothSubmersionOrderedGlobalTrace
  HironakaSmoothSubmersionRelativePartsCompanion HironakaSmoothSubmersionHistoricalCompanionMasks
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaSmoothSubmersionPositiveMemberHistory HironakaSmoothSubmersionAllBranchHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalUntestedControlledSmoothPullback
  HironakaOriginalUntestedCompanionSmoothPullback HironakaOriginalUntestedMemberCurveSpecial
  HironakaOriginalUntestedMemberCurveFullValues HironakaOriginalCurvePositiveEmptyWindow
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupRestrictOpen
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail CompanionRebase GeneralValue
  GeneralCanonicalTail GeneralCompare CompanionReductionAlong
  StepOneRegime StepOneValue StepOneLowerDomain StepOneValueMasked HomogenizedIdealAlong
  HomogenizedIdealAlongTower HironakaCoherentTransformExtension InvDomainCompanion
  InvDomainTowerAlong HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  InvDomainMemberRestriction NormalCrossings GermIdealOrder RelativePrincipalizationSpan
  CodimOneSupportAlong CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}
  {f : Y → X} {g : D' → D} {Q : BlowupTower Y D'} {T : BlowupTower X D}

/-- The actual literal open restriction is the genuine Cartesian history
over its actual open inclusion; every empty blowup remains a real step. -/
theorem open_inclusion_actual_tower (U : Opens X) (T : BlowupTower X D) :
    IsActualTowerPullback (Subtype.val : U → X) (restrict U T) T
      (Subtype.val : openPreimage T U → D) := by
  induction T with
  | refl => exact IsActualTowerPullback.refl (isSubmersion_val U)
  | @step Y Z T C π hπ ih =>
    let V := openPreimage T U
    let W := openPreimage (.step T C π hπ) U
    let πR : W → V := fun z => ⟨π z.val,z.property⟩
    have hπR : IsBlowupAlong n ((Subtype.val : V → Y) ⁻¹' C) πR :=
      isBlowupAlong_restrict hπ V (V.isOpen.preimage hπ.contMDiff.continuous)
    exact IsActualTowerPullback.step_of_actual_square (Z' := CMfd.of (n := n) W)
      (Z := Z) (π := π) (ρ := πR) ih (isSubmersion_val V)
      hπ hπR rfl (Subtype.val : W → Z) contMDiff_subtype_val rfl

/-- Restrict ONLY the actual source and retain the full original target
history; both genuine maps remain their literal composites. -/
theorem IsActualTowerPullback.restrict_source_open (h : IsActualTowerPullback f Q T g)
    (V : Opens Y) :
    IsActualTowerPullback (f ∘ (Subtype.val : V → Y)) (restrict V Q) T
      (g ∘ (Subtype.val : openPreimage Q V → D')) :=
  HironakaSmoothSubmersionCartesianTowerComposition.IsActualTowerPullback.comp h
    (open_inclusion_actual_tower V Q)

private theorem modeled_cosupport_off_boundary_iff (M B : MarkedIdeal n X)
    (hModel : ∀ {Z : CMfd.{u} n} (R : BlowupTower X Z),IsGeoTestTower M R →
      (geoTransformAlong B R).IsWellFormed) :
    ∀ {Z : CMfd.{u} n} (R : BlowupTower X Z),IsGeoTestTower M R → ∀ y : Z,
      y ∉ ⋃ F ∈ (geoTransformAlong B R).E,F →
      (y ∈ (geoTransformAlong B R).cosupp ↔ R.proj y ∈ B.cosupp)
  | _,.refl,_,_,_ => Iff.rfl
  | _,.step R C π hπ,hR,y,hy => by
    have hOff := HironakaStageCenters.notMem_boundary_geoTransform (geoTransformAlong B R) hy
    have hd := hModel R hR.1
    exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong B R)
      hd.isClosedSubmanifold_N.1
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hd.isCoherent hg) hπ hOff.1).trans
      (modeled_cosupport_off_boundary_iff M B hModel R hR.1 (π y) hOff.2)

/-- The SAME original order-run companion has independently constructed
current bar geometry and point before any source SPECIAL/value assertion. -/
theorem modeled_curve_run_companion_current_bar_data (hn : 0<n)
    (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain 1 (geoTransformAlong K R))
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) (y : D)
    (hy : y ∈ (geoTransformAlong K T).cosupp) (hpos : 0<nmOrd (geoTransformAlong K T) y) :
    let q := nmOrd (geoTransformAlong K T) y
    let r := regimeRun (OrdRegime K q) T y
    let H := head T r
    let S := tail T r
    let A := geoTransformAlong K H
    let W := ordMask A q
    let B := barMarked (companionOf n A q)
    let J := compAt K q H
    ∃ hp : S.proj y ∈ W,
      (∀ {V : CMfd.{u} n} (R : BlowupTower (split T r).1 V),
        IsGeoTestTower (geoTransformAlong M H) R → IsInvDomain 1 (geoTransformAlong B R)) ∧
      IsInvDomain 1 (geoTransformAlong B S) ∧ y ∈ (geoTransformAlong B S).cosupp ∧
      y ∉ ⋃ F ∈ (geoTransformAlong B S).E,F ∧
      barMarked J=MarkedIdeal.pullback (Subtype.val : W → _) B ∧
      geoTransformAlong (barMarked J) (restrict W S)=
        MarkedIdeal.pullback (Subtype.val : openPreimage S W → D) (geoTransformAlong B S) ∧
      IsInvDomain 1 (geoTransformAlong (barMarked J) (restrict W S)) ∧
      (⟨y,hp⟩ : openPreimage S W) ∈ (geoTransformAlong (barMarked J) (restrict W S)).cosupp := by
  let q := nmOrd (geoTransformAlong K T) y
  let r := regimeRun (OrdRegime K q) T y
  let H := head T r
  let S := tail T r
  let A := geoTransformAlong K H
  let W := ordMask A q
  let C := companionOf n A q
  let B := barMarked C
  let J := compAt K q H
  let mH := geoTransformAlong M H
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hT
  have hA : IsInvDomain 1 A := hModel H hH
  have hReg := regime_start (OrdRegime K q) T (y := y) ⟨hy,rfl⟩
  change S.proj y ∈ A.cosupp ∧ nmOrd A (S.proj y)=q at hReg
  have hMask : S.proj y ∈ W := by
    apply (mem_ordMask_iff hn hA.isWellFormed hA.isNonzeroAlongAt q _).mpr
    intro hh
    have hle := (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hReg.1.1 (q+1)).mp hh
    rw [hReg.2] at hle
    omega
  have hC : IsInvDomain 1 C := isInvDomain_companionAlong hn hA hpos
  have hB : IsInvDomain 1 B := isInvDomain_barMarked C hC
  have hBN : B.N=A.N := by simp only [B,C,barMarked_N,companionOf,companionAlong_N]
  have hBE : B.E=A.E := by simp only [B,C,barMarked_E,companionOf,companionAlong_E]
  have hTailModel : ∀ {V : CMfd.{u} n} (R : BlowupTower (split T r).1 V),
      IsGeoTestTower mH R → IsInvDomain 1 (geoTransformAlong A R) := by
    intro V R hR
    have hd := hModel (H.append R) ((isGeoTestTower_append_iff M H R).mpr ⟨hH,hR⟩)
    rwa [geoTransformAlong_append] at hd
  have hBModel : ∀ {V : CMfd.{u} n} (R : BlowupTower (split T r).1 V),
      IsGeoTestTower mH R → IsInvDomain 1 (geoTransformAlong B R) :=
    fun R hR => modeled_curve_candidate_domains mH A B hB hBN hBE hTailModel R hR
  have hBS := hBModel S hS
  have hJ : IsInvDomain 1 J := isInvDomain_compAt hn hpos H hA
  have hInitJ : (⟨S.proj y,hMask⟩ : W) ∈ J.cosupp := by
    exact (mem_cosupp_compAt_iff hn hA hpos .refl .refl trivial trivial trivial
      (⟨S.proj y,hMask⟩ : openPreimage (.refl : BlowupTower _ _) W)).mpr hReg
  have hJC : J=MarkedIdeal.pullback (Subtype.val : W → _) C := compAt_eq_pullback hn q H hA
  have hInitC : S.proj y ∈ C.cosupp := by
    rw [hJC,cosupp_pullback_val C (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hC.isWellFormed.isCoherent hg)] at hInitJ
    exact hInitJ
  have hInitB : S.proj y ∈ B.cosupp := by
    have he := coeff_homAlong_wEquiv C hC.isWellFormed.isClosedSubmanifold_N hC.isWellFormed.isCoherent hC.one_le_d
    change S.proj y ∈ (geoTransformAlong (barMarked C) (.refl : BlowupTower _ _)).cosupp
    rw [(he.2 .refl).2 trivial]
    exact hInitC
  have hyNoE : y ∉ ⋃ F ∈ (geoTransformAlong K T).E,F := by
    intro hh
    have hz := (curve_domain_nonmonomial_unit_on_boundary hn (geoTransformAlong K T) (hModel T hT) y hy.1 hh).2
    omega
  have hBSE : (geoTransformAlong B S).E=(geoTransformAlong K T).E :=
    (geoTransformAlong_E_eq_of_E_eq hBE S).trans (congrArg MarkedIdeal.E (geoTransformAlong_head_tail K T r).symm)
  have hyBNoE : y ∉ ⋃ F ∈ (geoTransformAlong B S).E,F := by rw [hBSE];exact hyNoE
  have hyB : y ∈ (geoTransformAlong B S).cosupp :=
    (modeled_cosupport_off_boundary_iff mH B (fun R hR => (hBModel R hR).isWellFormed) S hS y hyBNoE).mpr hInitB
  have hBarJ : barMarked J=MarkedIdeal.pullback (Subtype.val : W → _) B := by
    rw [hJC]
    exact ContactStageKept.barMarked_pullback_val W hC.isWellFormed.isCoherent hC.isWellFormed.isClosedSubmanifold_N hC.one_le_d
  have hWhole : geoTransformAlong (barMarked J) (restrict W S)=
      MarkedIdeal.pullback (Subtype.val : openPreimage S W → D) (geoTransformAlong B S) := by
    rw [hBarJ]
    exact (IsActualTowerPullback.modeled_controlled_dictionary (open_inclusion_actual_tower W S)
      mH B (fun R hR => (hBModel R hR).isWellFormed) hS).1
  have hCurrent : IsInvDomain 1 (geoTransformAlong (barMarked J) (restrict W S)) := by
    rw [hWhole]
    exact isInvDomain_pullback_val (openPreimage S W) hBS
  have hpBar : (⟨y,hMask⟩ : openPreimage S W) ∈ (geoTransformAlong (barMarked J) (restrict W S)).cosupp := by
    rw [hWhole,cosupp_pullback_val _ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hBS.isWellFormed.isCoherent hg)]
    exact hyB
  exact ⟨hMask,hBModel,hBS,hyB,hyBNoE,hBarJ,hWhole,hCurrent,hpBar⟩

/-- Actual codimension-one smooth geometry, not a source curve-dimension
assumption, proves the SOURCE original run companion's true SPECIAL leaf. -/
theorem modeled_curve_smooth_run_companion_value (hn : 0<n) (hm : 0<m) (k : ℕ)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain 1 (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (z : D')
    (hy : g z ∈ (geoTransformAlong K T).cosupp) (hpos : 0<nmOrd (geoTransformAlong K T) (g z)) :
    let q := nmOrd (geoTransformAlong K T) (g z)
    let r := regimeRun (OrdRegime K q) T (g z)
    let V := ordMask (geoTransformAlong (markedPullback (m := m) f K) (head Q r)) q
    ∃ hp : (tail Q r).proj z ∈ V,
      Seq.StepOneValueMasked.stepOneInvM (invFamily hm k)
        (compAt (markedPullback (m := m) f K) q (head Q r)) (restrict V (tail Q r))
        (⟨z,hp⟩ : openPreimage (tail Q r) V)=toLex (0,⊤) := by
  let q := nmOrd (geoTransformAlong K T) (g z)
  let r := regimeRun (OrdRegime K q) T (g z)
  let H := head T r
  let S := tail T r
  let A := geoTransformAlong K H
  let U := ordMask A q
  let B := barMarked (companionOf n A q)
  let J := compAt K q H
  let mH := geoTransformAlong M H
  let H' := head Q r
  let S' := tail Q r
  let V := ordMask (geoTransformAlong (markedPullback (m := m) f K) H') q
  let J' := compAt (markedPullback (m := m) f K) q H'
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T r).mp hT
  obtain ⟨a,hHead,hTail⟩ := HironakaSmoothSubmersionHistoricalCompanionMasks.IsActualTowerPullback.simultaneous_split h r
  obtain ⟨hMask,hBModel,hBS,hyB,hyNoE,hBarJ,_hWholeJ,_hCurrentJ,_hpJ⟩ :=
    modeled_curve_run_companion_current_bar_data hn M K hModel T hT (g z) hy hpos
  obtain ⟨p,hpSmooth,hpcoord,hComp⟩ :=
    IsActualTowerPullback.exists_modeled_masked_companion hn hHead M K hModel hH q
  have hV : (V : Set (split Q r).1)=a ⁻¹' (U : Set (split T r).1) :=
    IsActualTowerPullback.modeled_order_mask_dictionary hn hHead M K hModel hH q
  have hSourceMask : S'.proj z ∈ V := by
    change S'.proj z ∈ (V : Set (split Q r).1)
    rw [hV]
    change a (S'.proj z) ∈ U
    rw [←hTail.proj_comm z]
    exact hMask
  let zV : openPreimage S' V := ⟨z,hSourceMask⟩
  have hJ : IsInvDomain 1 J := isInvDomain_compAt hn hpos H (hModel H hH)
  have hBcoh : B.ideal.IsCoherent := (hBModel .refl trivial).isWellFormed.isCoherent
  have hInit : markedPullback (m := m) (a ∘ (Subtype.val : V → (split Q r).1)) B=barMarked J' := by
    change markedPullback (m := m) p J=J' at hComp
    have hh := congrArg (fun L : MarkedIdeal m V => barMarked (X := CMfd.of (n := m) V) L) hComp
    rw [←pullback_barMarked hpSmooth J hJ.isWellFormed,hBarJ] at hh
    change markedPullback (m := m) p
      (markedPullback (m := n) (Subtype.val : U → (split T r).1) B)=barMarked J' at hh
    rw [←whole_parameter_markedPullback_comp (X := (split T r).1) (Y := CMfd.of (n := n) U)
      (Z := CMfd.of (n := m) V) (f := (Subtype.val : U → (split T r).1)) (g := p)
      contMDiff_subtype_val hpSmooth.contMDiff B hBcoh] at hh
    have hBase : (Subtype.val : U → (split T r).1) ∘ p=a ∘ (Subtype.val : V → (split Q r).1) := by
      funext v
      exact hpcoord v
    rwa [hBase] at hh
  have hOpen := IsActualTowerPullback.restrict_source_open hTail V
  have hSourceWhole : geoTransformAlong (barMarked J') (restrict V S')=
      markedPullback (m := m) (g ∘ (Subtype.val : openPreimage S' V → D')) (geoTransformAlong B S) := by
    have hh := (IsActualTowerPullback.modeled_controlled_dictionary hOpen mH B
      (fun R hR => (hBModel R hR).isWellFormed) hS).1
    rwa [hInit] at hh
  obtain ⟨hNReg,hSReg⟩ := actual_curve_cosupport_regular_dimensions (geoTransformAlong B S) hBS (g z) hyB
  have hCodim : g z ∈ codimOnePartAlong (geoTransformAlong B S).N
      (geoTransformAlong B S).ideal (geoTransformAlong B S).d := ⟨0,hNReg,hSReg⟩
  have hSourceCodim : zV ∈ codimOnePartAlong (geoTransformAlong (barMarked J') (restrict V S')).N
      (geoTransformAlong (barMarked J') (restrict V S')).ideal (geoTransformAlong (barMarked J') (restrict V S')).d := by
    rw [hSourceWhole]
    change zV ∈ codimOnePartAlong ((g ∘ (Subtype.val : openPreimage S' V → D')) ⁻¹' (geoTransformAlong B S).N)
      (GermIdeal.pullback (m := m) (g ∘ (Subtype.val : openPreimage S' V → D')) (geoTransformAlong B S).ideal)
      (geoTransformAlong B S).d
    rw [codimOnePartAlong_preimage_eq hOpen.isSubmersion hBS.isWellFormed.isCoherent]
    exact hCodim
  have hSourceNoE : zV ∉ ⋃ F ∈ (geoTransformAlong (barMarked J') (restrict V S')).E,F := by
    rw [hSourceWhole]
    intro hzF
    obtain ⟨F,hF,hzF⟩ := mem_iUnion₂.mp hzF
    change F ∈ (geoTransformAlong B S).E.map
      ((g ∘ (Subtype.val : openPreimage S' V → D')) ⁻¹' ·) at hF
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hF
    exact hyNoE (mem_iUnion₂.mpr ⟨D,hD,hzF⟩)
  have hLevel : level J' (restrict V S') zV=0 := by
    unfold level BoundaryCount.boundaryCount
    apply Finset.card_eq_zero.mpr
    ext i
    constructor
    · intro hi
      have hPass := (Finset.mem_filter.mp hi).2
      have hMember : (origMembers J' (restrict V S')).get i ∈
          (geoTransformAlong (barMarked J') (restrict V S')).E :=
        List.mem_of_mem_take (List.get_mem _ i)
      exact (hSourceNoE (mem_iUnion₂.mpr ⟨_,hMember,hPass⟩)).elim
    · intro hi
      simp at hi
  have hSpecial : IsSpecial J' (restrict V S') zV := Or.inl ⟨hLevel,hSourceCodim⟩
  refine ⟨hSourceMask,?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hSpecial,hLevel]

/-- WHOLE unchanged original GENERAL values on actual modeled curve
histories, with arbitrary true source relative dimension and no lower TEST. -/
theorem modeled_curve_smooth_full_value (hn : 0<n) (hm : 0<m) (k : ℕ)
    (h : IsActualTowerPullback f Q T g) (M K : MarkedIdeal n X)
    (hModel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V),IsGeoTestTower M R →
      IsInvDomain 1 (geoTransformAlong K R)) (hT : IsGeoTestTower M T) (z : D')
    (hy : g z ∈ (geoTransformAlong K T).cosupp) :
    (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) f K) Q z=
      familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv K T (g z)) := by
  have hOrder : nmOrd (geoTransformAlong (markedPullback (m := m) f K) Q) z=
      nmOrd (geoTransformAlong K T) (g z) :=
    IsActualTowerPullback.modeled_orderAt_dictionary hn h M K hModel hT z
  have hWhole := (IsActualTowerPullback.modeled_controlled_dictionary h M K
    (fun R hR => (hModel R hR).isWellFormed) hT).1
  have hc := hModel T hT
  by_cases hz : nmOrd (geoTransformAlong K T) (g z)=0
  · have hSource0 := hOrder.trans hz
    have hGamma : MonomialCaseAlong.gammaAlong m
        (geoTransformAlong (markedPullback (m := m) f K) Q).N
        (geoTransformAlong (markedPullback (m := m) f K) Q).ideal
        (geoTransformAlong (markedPullback (m := m) f K) Q).E
        (geoTransformAlong (markedPullback (m := m) f K) Q).d z=
        dimensionValue (m-n) (MonomialCaseAlong.gammaAlong n (geoTransformAlong K T).N
          (geoTransformAlong K T).ideal (geoTransformAlong K T).E (geoTransformAlong K T).d (g z)) := by
      rw [hWhole]
      exact gammaAlong_preimage_dimension_shift h.isSubmersion hc.isWellFormed.isCoherent
        _ _ hc.isWellFormed.isSNCDivisor _ z
    change genInv (fun {A} J {B} S y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hm ((m-n)+k)) J (Y := B) S y)
        (markedPullback (m := m) f K) Q z=
      familyDimensionMap (m-n) (k+1) (genInv (fun {A} J {B} S y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hn k) J (Y := B) S y) K T (g z))
    unfold familyDimensionMap generalDimensionMap genInv genSecond
    rw [hSource0,hz]
    simp only [ite_true,ofLex_toLex,Sum.map_inl]
    rw [hGamma]
  · have hpos : 0<nmOrd (geoTransformAlong K T) (g z) := Nat.pos_of_ne_zero hz
    obtain ⟨hMask,hValue⟩ := modeled_curve_smooth_run_companion_value hn hm ((m-n)+k)
      h M K hModel hT z hy hpos
    have hRun := IsActualTowerPullback.modeled_fixed_order_run hn h M K hModel hT
      (nmOrd (geoTransformAlong K T) (g z)) z
    have hSourceValue : (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) f K) Q z=
        toLex (nmOrd (geoTransformAlong K T) (g z),toLex (Sum.inr
          ((toLex (0,(⊤ : WithTop (ValTy ((m-n)+k)))) : ℕ ×ₗ WithTop (ValTy ((m-n)+k))) :
            WithTop (ℕ ×ₗ WithTop (ValTy ((m-n)+k)))))) := by
      change genInv (fun {A} J {B} S y =>
        Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily hm ((m-n)+k)) J (Y := B) S y)
        (markedPullback (m := m) f K) Q z=_
      rw [genInv_of_nmOrd_ne_zero _ _ Q hOrder hz,hRun,genLowerValue_eq_of_mem _ _ hMask,hValue]
    rw [hSourceValue,modeled_curve_full_value_formula hn k M K hModel T hT (g z) hy,if_neg hz]
    simp only [familyDimensionMap,generalDimensionMap,stepDimensionMap,ofLex_toLex,
      Sum.map_inr,WithTop.map_coe,WithTop.map_top]
    rfl

/-- ONLY original DOMAIN2 member geometry supplies the genuine entire
reference family before full smooth values on ANY original upper TEST. -/
theorem original_member_untested_smooth_full_value (hn : 0<n) (hm : 0<m) (k : ℕ)
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X) (hM : IsInvDomain 2 M)
    (S : Finset (Fin M.E.length)) (hS : S.Nonempty) (hT : IsGeoTestTower M T) (z : D')
    (hy : g z ∈ (geoTransformAlong (memberRemainderMarked M S) T).cosupp) :
    (invFamily hm ((m-n)+k+1)).inv (markedPullback (m := m) f (memberRemainderMarked M S)) Q z=
      familyDimensionMap (m-n) (k+1) ((invFamily hn (k+1)).inv (memberRemainderMarked M S) T (g z)) := by
  exact modeled_curve_smooth_full_value hn hm k h M (memberRemainderMarked M S)
    (fun R hR => isInvDomain_geoTransformAlong_memberRemainder hn M hM.isWellFormed
      hM.one_le_d hM.dimLE S hS R hR) hT z hy

end
end Hironaka.HironakaOriginalUntestedCurveSmoothValues
