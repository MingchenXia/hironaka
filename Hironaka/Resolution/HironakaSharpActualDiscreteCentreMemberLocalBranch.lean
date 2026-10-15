/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveExceptionalPointExponent

/-! Genuine local incidence branches for actual discrete centres and true
ambient strict-member traces. No global centre-in-every-member assumption. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualDiscreteCentreMemberLocalBranch
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  RelativePrincipalizationSpan RestrictedIdealExtension MarkedIdealRestrictOpen BlowupRestrictOpen
  HironakaSharpActualFirstAmbientStrictTraceFactor PositiveDimensionalComponent
  NormalCrossings DivisorExponentAlong MonomialPartAlong InvertibleIdealQuotient
  HironakaOneDimensionalCanonicalSuperlevels HironakaSharpOriginalFirstMemberRelativeStrict
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual discrete centre isolation supplies the true source-open incidence
branches, before any restricted blowup or factor is selected. -/
theorem exists_actual_discrete_centre_member_open_branch {C H : Set X}
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0) (hH : IsClosed H)
    {p : X} (hpC : p ∈ C) :
    ∃ (U : Opens X) (hpU : p ∈ U),(Subtype.val : U → X) ⁻¹' C={⟨p,hpU⟩} ∧
      (p ∈ H → (Subtype.val : U → X) ⁻¹' C ⊆ (Subtype.val : U → X) ⁻¹' H) ∧
      (p ∉ H → (Subtype.val : U → X) ⁻¹' H=∅) := by
  obtain ⟨O,hO,hpO,hIso⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero (hrC p hpC)
  have hEq (U : Opens X) (hpU : p ∈ U) (hUO : (U : Set X) ⊆ O) :
      (Subtype.val : U → X) ⁻¹' C={⟨p,hpU⟩} := by
    ext x
    constructor
    · intro hx
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      exact hIso ⟨hx,hUO x.property⟩
    · intro hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      exact hpC
  by_cases hpH : p ∈ H
  · let U : Opens X := ⟨O,hO⟩
    have hpU : p ∈ U := hpO
    refine ⟨U,hpU,hEq U hpU subset_rfl,?_,fun h => (h hpH).elim⟩
    intro _ x hx
    have he : (x : X)=p := hIso ⟨hx,x.property⟩
    change (x : X) ∈ H
    rw [he]
    exact hpH
  · let U : Opens X := ⟨O \ H,hO.sdiff hH⟩
    have hpU : p ∈ U := ⟨hpO,hpH⟩
    refine ⟨U,hpU,hEq U hpU (fun _ hx => hx.1),fun h => (hpH h).elim,?_⟩
    intro _
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact x.property.2 hx

/-- Both genuine open vanishing-ideal directions BEFORE actual relative-span
normalization give the complete original trace germ dictionary. -/
theorem actual_normalized_vanishing_open_germ_iff {N H : Set Y}
    (hH : IsClosedSubmanifold n H) (U : Opens Y) (x : U) (g : U → ℂ) :
    (restrictOn n ((Subtype.val : U → Y) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' H))).mem x g ↔
      (restrictOn n N (vanishingIdeal (n := n) H)).mem x.val (extendOpens U g) := by
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hLocal : vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' H)=
      GermIdeal.pullback (m := n) (Subtype.val : U → Y) (vanishingIdeal (n := n) H) := by
    ext y a
    exact (vanishingIdeal_opens_mem_iff U).trans (mem_pullback_val_iff U hcH).symm
  rw [hLocal]
  exact restrictOn_pullback_val_iff U hcH

/-- The actual nonincident source open makes EVERY genuine ambient strict
trace germ a unit germ on the ENTIRE preimage open, along ANY carrier. -/
theorem exists_actual_nonincident_discrete_member_trace_unit_open {N C H : Set X}
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0) (hH : IsClosed H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {p : X} (hpC : p ∈ C) (hpH : p ∉ H) :
    ∃ U : Opens X,p ∈ U ∧ ∀ z : Y,π z ∈ U → ∀ g,
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N)
        (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))).mem z g ↔
          HolomorphicAt n g z := by
  obtain ⟨U,hpU,_hCU,_hCH,hHU⟩ := exists_actual_discrete_centre_member_open_branch hrC hH hpC
  have hEmpty := hHU hpH
  refine ⟨U,hpU,?_⟩
  intro z hzU g
  have hzH : z ∉ BlowupStrictSubmanifold.geoStrictTransform π C H := by
    intro hzH
    have hb : π z ∈ H := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH hzH
    have hp : (⟨π z,hzU⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' H := hb
    rw [hEmpty] at hp
    exact hp
  constructor
  · exact fun hg => hg.1
  · intro hg
    have hgH : (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)).mem z g := by
      refine ⟨hg,?_⟩
      filter_upwards [(isClosed_closure : IsClosed (BlowupStrictSubmanifold.geoStrictTransform π C H)).isOpen_compl.mem_nhds hzH]
        with y hy hyH
      exact (hy hyH).elim
    exact ⟨hg,IsInSpanAt.restrict (isInSpanAt_self hgH hg)⟩

/-- A genuine incident source branch supplies the SAME restricted blowup,
true local factor, BOTH actual strict-set restrictions and full original germs. -/
theorem exists_actual_incident_discrete_member_restricted_factor (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {p : X} (hpC : p ∈ C) (hpH : p ∈ H) :
    ∃ U : Opens X,p ∈ U ∧
      let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
      let ρ : V → U := fun z => ⟨π z,z.property⟩
      let NU : Set U := (Subtype.val : U → X) ⁻¹' N
      let HU : Set U := (Subtype.val : U → X) ⁻¹' H
      let CU : Set U := (Subtype.val : U → X) ⁻¹' C
      let N' := BlowupStrictSubmanifold.geoStrictTransform ρ CU NU
      let H' := BlowupStrictSubmanifold.geoStrictTransform ρ CU HU
      let I' := restrictOn n N' (vanishingIdeal (n := n) H')
      let J' := firstRelativeStrictMemberIdeal (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) NU HU CU ρ
      let D' := monomialPartAlong n N' I' [ρ ⁻¹' CU]
      IsBlowupAlong n CU ρ ∧
        N'=(Subtype.val : V → Y) ⁻¹' BlowupStrictSubmanifold.geoStrictTransform π C N ∧
        H'=(Subtype.val : V → Y) ⁻¹' BlowupStrictSubmanifold.geoStrictTransform π C H ∧
        I'.IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' I' z) ∧
        nonmonomialPartAlong n N' I' [ρ ⁻¹' CU]=J' ∧ I'=restrictOn n N' (D'.mul J') ∧
        ∀ (z : V) (g : V → ℂ),I'.mem z g ↔
          (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N)
            (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))).mem z.val (extendOpens V g) := by
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  obtain ⟨U,hpU,_hCU,hCH,_hAvoid⟩ := exists_actual_discrete_centre_member_open_branch hrC hHc.1 hpC
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun z => ⟨π z,z.property⟩
  let NU : Set U := (Subtype.val : U → X) ⁻¹' N
  let HU : Set U := (Subtype.val : U → X) ⁻¹' H
  let CU : Set U := (Subtype.val : U → X) ⁻¹' C
  have hρ : IsBlowupAlong n CU ρ := isBlowupAlong_restrict hπ U V.isOpen
  have hNU : IsClosedSubmanifold n NU := isClosedSubmanifold_preimage_val hN U
  have hHU : IsSNCDivisor n [HU] := by
    simpa only [List.map_singleton] using NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val U) continuous_subtype_val hH
  have hCN_U : CU ⊆ NU := fun _ hx => hCN hx
  have hCH_U : CU ⊆ HU := hCH hpH
  have hDenseU : NU ⊆ closure (NU \ HU) := by
    intro x hx
    have hcl : x ∈ (Subtype.val : U → X) ⁻¹' closure (N \ H) := hdense hx
    have hEq := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (N \ H)
    exact (Set.ext_iff.mp hEq x).mp hcl
  obtain ⟨hcI,hnzI,_hcD,_hnzD,_hmD,hNm,hFactor⟩ := actual_first_ambient_strict_trace_factor_dictionary
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) hn hNU hHU hDenseU hρ hCN_U hCH_U
  have hNEq := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen N
  have hHEq := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen H
  have hNC : HasNormalCrossings n C [H] := by
    apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
    intro x hx
    obtain ⟨O,hO,hxO,hIso⟩ := exists_isOpen_inter_subset_singleton_of_regularAtDim_zero (hrC x hx)
    refine ⟨{x},mem_singleton x,?_,hasNormalCrossings_singleton x hH⟩
    filter_upwards [hO.mem_nhds hxO] with y hy
    exact ⟨fun hyC => hIso ⟨hyC,hy⟩,fun hyx => by rw [mem_singleton_iff.mp hyx]; exact hx⟩
  have hAmbient := SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hH hNC
  have hHstrict : IsClosedSubmanifold n (BlowupStrictSubmanifold.geoStrictTransform π C H) :=
    MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  refine ⟨U,hpU,hρ,hNEq,hHEq,hcI,hnzI,hNm,hFactor,?_⟩
  intro z g
  rw [hNEq,hHEq]
  exact actual_normalized_vanishing_open_germ_iff hHstrict V z g

end
end Hironaka.HironakaSharpActualDiscreteCentreMemberLocalBranch
