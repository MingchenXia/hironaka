/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualAccumulatedTraceResidual
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

/-! Higher-dimensional actual incident-centre trace continuation.  Centres may
have arbitrary dimension; local incident containment replaces point isolation.
Whole relative restrictions and all accumulated exceptional members are retained.
No full modified-invariant strict decrease or sharp termination is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualIncidentCentreTraceResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualAccumulatedTraceResidual HironakaSharpActualMixedDiscreteTraceResidual
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProduct
  HironakaSharpActualRawMemberOpenStrict
  HironakaSharpActualStrictTraceOpenNonmonomial HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaSharpActualDiscreteCentreMemberLocalBranch HironakaSharpActualFirstAmbientStrictTraceFactor
  HironakaSharpOriginalAllBoundaryCentre HironakaSharpOriginalFirstMemberRelativeStrict
  HironakaSharpOriginalFirstMemberWholeFactor HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpActualChronologicalStrictStep HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient MarkedIdealRestrictOpen BlowupRestrictOpen
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  InvertibleIdealQuotient GermIdealOrder NonmonomialTransformAlong RestrictLeCalculus
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem incident_open {C H : Set X} {p : X} (hp : p ∈ C) (hpH : p ∈ H)
    (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H) :
    ∃ U : Opens X,p ∈ U ∧ (Subtype.val : U → X) ⁻¹' C ⊆ (Subtype.val : U → X) ⁻¹' H := by
  obtain ⟨U,hU,hUo,hpU⟩ := mem_nhds_iff.mp (hlocal p hp hpH)
  exact ⟨⟨U,hUo⟩,hpU,fun q hq => hU q.property hq⟩

/-- ONLY original actual SNC/density and a locally incident centre of arbitrary dimension internally
produce WHOLE true next trace geometry, including real new density. -/
theorem actual_incident_centre_whole_strict_trace_geometry (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
    let I' := restrictOn n N' (vanishingIdeal (n := n) H')
    IsClosedSubmanifold n N' ∧ IsSNCDivisor n [H',π ⁻¹' C] ∧
      I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      N' ⊆ closure (N' \ H') ∧
      ∀ y ∈ N',∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,I'.mem y g ↔
        HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N' (·=f) y g := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
  let I' := restrictOn n N' (vanishingIdeal (n := n) H')
  let M0 : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hNC : HasNormalCrossings n C [H] :=
    hasNormalCrossings_of_eventually_incident_containment hπ.1 hH (by
      intro p hp i hi
      have he : [H].get i=H := by simp
      rw [he] at hi ⊢
      exact hlocal p hp hi)
  have hAmbient := SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hH hNC
  have hH' : IsClosedSubmanifold n H' := MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  have hcI : I'.IsCoherent := isCoherent_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hH')
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  have hRaw : (M0.geoTransform C π).ideal=P := geoTransform_zeroMark_ideal_eq_restricted_total M0 rfl C π
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hRaw]
    exact isNonzeroAlongAt_geoTransform_without_admissibility M0 hN hcH hπ hCN hnzH
  have hLe := actual_pullback_vanishing_le_strict_vanishing hHc.1 hπ
  have hPI : P.Le I' := by
    intro y g hg
    exact ⟨hg.1,IsInSpanOnAt.mono (fun a ha => hLe y a ha) hg.2⟩
  have hnzI : ∀ y ∈ N',IsNonzeroAlongAt N' I' y := by
    intro y hy
    obtain ⟨g,hg,hfreq⟩ := hnzP y hy
    exact ⟨g,hPI y g hg,hfreq⟩
  refine ⟨hN',by simpa only [List.map_singleton,List.singleton_append] using hAmbient,
    hcI,hnzI,actual_density_of_nonzero_normalized_vanishing hnzI,?_⟩
  intro y _hy
  obtain ⟨f,hf,hgen⟩ := exists_originalMember_principal hn hAmbient (H := H') (by simp [H']) y
  exact ⟨f,hf,fun g => and_congr_right fun _ => restricted_span_iff_principal hf hgen g⟩

/-- A genuine incident source branch supplies the SAME restricted blowup,
true local factor, BOTH actual strict-set restrictions and full original germs. -/
private theorem exists_actual_incident_member_restricted_factor (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H)
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
  obtain ⟨U,hpU,hCH⟩ := incident_open hpC hpH hlocal
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
  have hCH_U : CU ⊆ HU := hCH
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
  have hNC : HasNormalCrossings n C [H] :=
    hasNormalCrossings_of_eventually_incident_containment hπ.1 hH (by
      intro p hp i hi
      have he : [H].get i=H := by simp
      rw [he] at hi ⊢
      exact hlocal p hp hi)
  have hAmbient := SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hH hNC
  have hHstrict : IsClosedSubmanifold n (BlowupStrictSubmanifold.geoStrictTransform π C H) :=
    MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  refine ⟨U,hpU,hρ,hNEq,hHEq,hcI,hnzI,hNm,hFactor,?_⟩
  intro z g
  rw [hNEq,hHEq]
  exact actual_normalized_vanishing_open_germ_iff hHstrict V z g

/-- ONLY original locally incident-centre geometry supplies the true next trace
and part geometry before BOTH full open germ directions on EVERY real open. -/
private theorem actual_incident_strict_trace_open_nonmonomial_iff (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H))
    (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (V : Opens Y) (z : V) (g : V → ℂ) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
    let I' := restrictOn n N' (vanishingIdeal (n := n) H')
    (nonmonomialPartAlong n ((Subtype.val : V → Y) ⁻¹' N')
      (restrictOn n ((Subtype.val : V → Y) ⁻¹' N')
        (vanishingIdeal (n := n) ((Subtype.val : V → Y) ⁻¹' H')))
      [(Subtype.val : V → Y) ⁻¹' (π ⁻¹' C)]).mem z g ↔
        (nonmonomialPartAlong n N' I' [π ⁻¹' C]).mem z.val (extendOpens V g) := by
  obtain ⟨hN',hAmbient,hcI,hnzI,_hDense,_hPr⟩ :=
    actual_incident_centre_whole_strict_trace_geometry hn hN hH hdense hlocal hπ hCN
  have hH' : IsClosedSubmanifold n (BlowupStrictSubmanifold.geoStrictTransform π C H) :=
    MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length))
  obtain ⟨hNewE,hNewT⟩ := actual_accumulated_exceptional_geometry hN hcH isSNCDivisor_nil
    (isTransverse_nil_of_isClosedSubmanifold hN) hπ hCN
    (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
  have hE : IsSNCDivisor n [π ⁻¹' C] := by simpa only [List.map_nil,List.nil_append] using hNewE
  have hTrans : IsTransverse n (BlowupStrictSubmanifold.geoStrictTransform π C N) [π ⁻¹' C] := by
    change IsTransverse n (BlowupStrictSubmanifold.geoStrictTransform π C N)
      ([].map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hNewT
    simpa only [List.map_nil,List.nil_append] using hNewT
  have hOpen := actual_normalized_trace_whole_open_pullback hN' hH' V
  change (nonmonomialPartAlong n _ _ _).mem z g ↔ _
  rw [hOpen]
  simpa only [List.map_singleton] using actual_nonmonomial_open_germ_iff hn hN' hE hTrans hcI hnzI V z g

private theorem actual_raw_geometry {N C : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let P := restrictOn n N' (GermIdeal.pullback (m := n) π I)
    IsClosedSubmanifold n N' ∧ IsSNCDivisor n [π ⁻¹' C] ∧ IsTransverse n N' [π ⁻¹' C] ∧
      P.IsCoherent ∧ ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  have hw : M.IsWellFormed := ⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hC : M.IsAdmissibleCentre C := by
    refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
    change C ⊆ cosupport n N I 0
    rw [cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCN
  have hNew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  have hNZ := isNonzeroAlongAt_geoTransform_without_admissibility M hN hI hπ hCN hnz
  have hRaw := geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π
  change (M.geoTransform C π).ideal=restrictOn n
    (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I) at hRaw
  refine ⟨hNew.isClosedSubmanifold_N,?_,?_,?_,?_⟩
  · have h := hNew.isSNCDivisor
    change IsSNCDivisor n [π ⁻¹' C] at h
    exact h
  · have h := hNew.isTransverse
    change IsTransverse n (BlowupStrictSubmanifold.geoStrictTransform π C N) [π ⁻¹' C] at h
    exact h
  · rw [←hRaw]; exact hNew.isCoherent
  · rw [←hRaw]; exact hNZ


/-- True incident source incident containment and independent local raw STRICT identify
BOTH SAME global residual germs on an ENTIRE actual preimage open. -/
private theorem exists_incident_global_residual_open_dictionary (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {p : X} (hpC : p ∈ C) (hpH : p ∈ H) :
    ∃ U : Opens X,p ∈ U ∧
      let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
      let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
      let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
      ∀ (z : V) (g : V → ℂ),
        (nonmonomialPartAlong n N' (restrictOn n N' (vanishingIdeal (n := n) H')) [π ⁻¹' C]).mem z.val (extendOpens V g) ↔
        (nonmonomialPartAlong n N' (restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))) [π ⁻¹' C]).mem z.val (extendOpens V g) := by
  obtain ⟨U,hpU,hρ,hNEq,hHEq,_hcL,_hnzL,hNmL,_hFactor,_hGerms⟩ :=
    exists_actual_incident_member_restricted_factor hn hN hH hdense hlocal hπ hCN hpC hpH
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun z => ⟨π z,z.property⟩
  let NU := (Subtype.val : U → X) ⁻¹' N
  let HU := (Subtype.val : U → X) ⁻¹' H
  let CU := (Subtype.val : U → X) ⁻¹' C
  have hNU := isClosedSubmanifold_preimage_val hN U
  have hHU : IsSNCDivisor n [HU] := by
    simpa only [List.map_singleton] using NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val U) continuous_subtype_val hH
  have hDenseU : NU ⊆ closure (NU \ HU) := by
    intro x hx
    have hcl : x ∈ (Subtype.val : U → X) ⁻¹' closure (N \ H) := hdense hx
    have he := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val (N \ H)
    exact (Set.ext_iff.mp he x).mp hcl
  have hRawLocal := actual_any_member_raw_nonmonomial_eq_relative_strict
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) hn hNU hHU hDenseU hρ (fun _ hx => hCN hx)
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  refine ⟨U,hpU,?_⟩
  dsimp only
  intro z g
  have hRawOpen := actual_raw_total_open_nonmonomial_iff hn hN hcH hnzH hπ hCN U z g
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal U H] at hRawOpen
  have hTraceOpen := actual_incident_strict_trace_open_nonmonomial_iff hn hN hH hdense hlocal hπ hCN V z g
  dsimp only at hTraceOpen hRawLocal
  rw [←hNEq,←hHEq] at hTraceOpen
  change (nonmonomialPartAlong n _ _ [ρ ⁻¹' CU]).mem z g ↔ _ at hTraceOpen
  rw [hNmL] at hTraceOpen
  rw [hRawLocal] at hRawOpen
  exact hTraceOpen.symm.trans hRawOpen

private theorem actual_nonmonomial_unit_germ_iff {N : Set Y} {E : List (Set Y)}
    {I : GermIdeal n Y} (hcI : I.IsCoherent) {x : Y} (h1 : I.mem x (1 : Y → ℂ)) (g : Y → ℂ) :
    (nonmonomialPartAlong n N I E).mem x g ↔ HolomorphicAt n g x := by
  constructor
  · exact fun hg => hg.1
  · intro hg
    have hgI : I.mem x g := HomogenizedIdeal.mem_of_isInSpanAt hcI
      (isInSpanAt_of_eq_mul h1 hg hg (Eventually.of_forall fun _ => by simp))
    exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hcI x g hgI

private theorem actual_normalized_nonmonomial_off_member_iff {N D : Set Y}
    (I : GermIdeal n Y) {x : Y} (hx : x ∉ D) (g : Y → ℂ) :
    (nonmonomialPartAlong n N (restrictOn n N I) [D]).mem x g ↔ (restrictOn n N I).mem x g := by
  have h1 : (monomialPartAlong n N (restrictOn n N I) [D]).mem x (1 : Y → ℂ) := by
    refine ⟨holomorphicAt_const 1,?_⟩
    intro i _hiN hiD
    have he : [D].get i=D := by simpa only [List.mem_singleton] using List.get_mem [D] i
    exact (hx (he ▸ hiD)).elim
  constructor
  · intro hg
    have hr : (restrictOn n N (restrictOn n N I)).mem x g := by
      simpa only [Pi.one_apply,one_mul] using hg.2 (1 : Y → ℂ) h1
    exact ⟨hr.1,IsInSpanOnAt.trans (fun a ha => ha.2) hr.2⟩
  · intro hg
    refine ⟨hg.1,fun a ha => ?_⟩
    have hprod := restrictOn_mul_left ha.1 hg
    exact ⟨hprod.1,IsInSpanAt.restrict (isInSpanAt_self hprod hprod.1)⟩

private theorem actual_raw_strict_vanishing_off_iff {H C : Set X} (hH : IsClosed H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {x : Y} (hx : π x ∉ C) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)).mem x g ↔
      (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H)).mem x g := by
  constructor
  · exact actual_pullback_vanishing_le_strict_vanishing hH hπ x g
  · intro hg
    apply (BlowupStrictIdeal.mem_pullback_vanishingIdeal_iff_of_notMem hπ H hx g).mpr
    refine ⟨hg.1,?_⟩
    filter_upwards [hg.2,(hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hx] with y hy hyC hyH
    exact hy ((BlowupStrictSubmanifold.mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hH hyC).mpr hyH)

private theorem actual_coherent_germ_congr {I : GermIdeal n Y} (hI : I.IsCoherent)
    {x : Y} {g g' : Y → ℂ} (hg : I.mem x g) (he : g =ᶠ[𝓝 x] g') : I.mem x g' := by
  have hh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  apply isInSpanAt_of_eq_mul hg (hh.congr he) (holomorphicAt_const 1)
  filter_upwards [he] with y hy
  rw [←hy,one_mul]

/-- ONLY original locally incident-centre inputs prove a WHOLE equality with
independently defined raw ALL-power STRICT, preserving the true exceptional factor. -/
theorem actual_incident_trace_nonmonomial_eq_relative_strict (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    nonmonomialPartAlong n N' I' [π ⁻¹' C]=firstRelativeStrictMemberIdeal N H C π := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let H' := BlowupStrictSubmanifold.geoStrictTransform π C H
  let I' := restrictOn n N' (vanishingIdeal (n := n) H')
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  let R := nonmonomialPartAlong n N' I' [π ⁻¹' C]
  let S := nonmonomialPartAlong n N' P [π ⁻¹' C]
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  obtain ⟨hN',_hAmbient,hcI,hnzI,_hDense,_hPr⟩ :=
    actual_incident_centre_whole_strict_trace_geometry hn hN hH hdense hlocal hπ hCN
  obtain ⟨_hNG,hE,hTrans,hcP,hnzP⟩ := actual_raw_geometry hN hcH hnzH hπ hCN
  have hcR : R.IsCoherent := isCoherent_nonmonomialPartAlong hn hN' hE hTrans hcI hnzI
  have hcS : S.IsCoherent := isCoherent_nonmonomialPartAlong hn hN' hE hTrans hcP hnzP
  have hWhole : R=S := by
    ext x g
    by_cases hxC : π x ∈ C
    · by_cases hxH : π x ∈ H
      · obtain ⟨U,hxU,hDict⟩ := exists_incident_global_residual_open_dictionary hn hN hH hdense hlocal hπ hCN hxC hxH
        let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
        let z : V := ⟨x,hxU⟩
        have he : extendOpens V (g ∘ (Subtype.val : V → Y)) =ᶠ[𝓝 x] g := by
          filter_upwards [V.isOpen.mem_nhds hxU] with y hy
          exact extendOpens_val V (g ∘ (Subtype.val : V → Y)) ⟨y,hy⟩
        have hR : R.mem x (extendOpens V (g ∘ (Subtype.val : V → Y))) ↔ R.mem x g :=
          ⟨fun h => actual_coherent_germ_congr hcR h he,
            fun h => actual_coherent_germ_congr hcR h he.symm⟩
        have hS : S.mem x (extendOpens V (g ∘ (Subtype.val : V → Y))) ↔ S.mem x g :=
          ⟨fun h => actual_coherent_germ_congr hcS h he,
            fun h => actual_coherent_germ_congr hcS h he.symm⟩
        exact hR.symm.trans ((hDict z (g ∘ (Subtype.val : V → Y))).trans hS)
      · have h1Old : (vanishingIdeal (n := n) H).mem (π x) (1 : X → ℂ) := by
          refine ⟨holomorphicAt_const 1,?_⟩
          filter_upwards [hHsm.1.isOpen_compl.mem_nhds hxH] with y hy hyH
          exact (hy hyH).elim
        have h1Pull : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)).mem x (1 : Y → ℂ) := by
          have h : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)).mem x ((1 : X → ℂ) ∘ π) :=
            GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨(1 : X → ℂ),h1Old,rfl⟩ (holomorphicAt_const 1))
          exact h
        have h1P : P.mem x (1 : Y → ℂ) :=
          ⟨holomorphicAt_const 1,IsInSpanAt.restrict (isInSpanAt_self h1Pull (holomorphicAt_const 1))⟩
        have hxH' : x ∉ H' := fun hx => hxH
          (BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hHsm.1 hx)
        have h1H' : (vanishingIdeal (n := n) H').mem x (1 : Y → ℂ) := by
          refine ⟨holomorphicAt_const 1,?_⟩
          filter_upwards [(isClosed_closure : IsClosed H').isOpen_compl.mem_nhds hxH'] with y hy hyH
          exact (hy hyH).elim
        have h1I : I'.mem x (1 : Y → ℂ) :=
          ⟨holomorphicAt_const 1,IsInSpanAt.restrict (isInSpanAt_self h1H' (holomorphicAt_const 1))⟩
        exact (actual_nonmonomial_unit_germ_iff hcI h1I g).trans
          (actual_nonmonomial_unit_germ_iff hcP h1P g).symm
    · have hI : R.mem x g ↔ I'.mem x g := actual_normalized_nonmonomial_off_member_iff
        (N := N') (D := π ⁻¹' C) (vanishingIdeal (n := n) H') (x := x) hxC g
      have hP : S.mem x g ↔ P.mem x g := actual_normalized_nonmonomial_off_member_iff
        (N := N') (D := π ⁻¹' C) (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) (x := x) hxC g
      apply hI.trans
      apply Iff.trans _ hP.symm
      have hAmb := actual_raw_strict_vanishing_off_iff hHsm.1 hπ hxC
      refine and_congr_right (fun _ => ?_)
      exact ⟨fun hg => IsInSpanOnAt.mono (fun a ha => (hAmb a).mpr ha) hg,
        fun hg => IsInSpanOnAt.mono (fun a ha => (hAmb a).mp ha) hg⟩
  exact hWhole.trans (actual_any_member_raw_nonmonomial_eq_relative_strict hn hN hH hdense hπ hCN)

/-- Actual parts geometry precedes true WHOLE normalized I'=D'*J' with
independent raw STRICT for arbitrary locally incident centres, not only incident centres. -/
theorem actual_incident_trace_greatest_factor_dictionary (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    let D' := monomialPartAlong n N' I' [π ⁻¹' C]
    D'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' D' y) ∧ IsMonomialAlong n N' D' [π ⁻¹' C] ∧
      I'=restrictOn n N' (D'.mul (firstRelativeStrictMemberIdeal N H C π)) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  obtain ⟨hN',_hAmbient,hcI,hnzI,_hDense,_hPr⟩ :=
    actual_incident_centre_whole_strict_trace_geometry hn hN hH hdense hlocal hπ hCN
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  obtain ⟨_hN,hE,hT,_hcP,_hnzP⟩ := actual_raw_geometry hN hcH hnzH hπ hCN
  obtain ⟨_hcR,hcD,hnzD,hmD,_hNo,_hnzR,hFactor⟩ := parts_hypotheses hn
    (⟨N',[π ⁻¹' C],I',0⟩ : MarkedIdeal n Y) ⟨hN',hcI,hE,hT⟩ hnzI
  have hNm := actual_incident_trace_nonmonomial_eq_relative_strict hn hN hH hdense hlocal hπ hCN
  have hWhole := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN'.1 hFactor.le hFactor.ge
  change restrictOn n N' I'=restrictOn n N' ((nonmonomialPartAlong n N' I' [π ⁻¹' C]).mul
    (monomialPartAlong n N' I' [π ⁻¹' C])) at hWhole
  rw [hNm,mul_comm' (firstRelativeStrictMemberIdeal N H C π) (monomialPartAlong n N' I' [π ⁻¹' C])] at hWhole
  have hNorm : restrictOn n N' I'=I' := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  exact ⟨hcD,hnzD,hmD,hNorm.symm.trans hWhole⟩

/-- ONLY original locally incident-centre data give true ALL-old-E geometry
and WHOLE trace versus actual raw TOTAL residual equality for the SAME Enew. -/
theorem actual_incident_accumulated_trace_nonmonomial_eq_total (hn : 0 < n)
    {N H C : Set X} {E : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hlocal : ∀ p ∈ C,p ∈ H → ∀ᶠ q in 𝓝 p,q ∈ C → q ∈ H)
    (hCborn : HasNormalCrossings n C E)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
    IsSNCDivisor n E' ∧ IsTransverse n N' E' ∧ nonmonomialPartAlong n N' I' E'=nonmonomialPartAlong n N' P E' := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let E' := E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  let J := HironakaSharpOriginalFirstMemberRelativeStrict.firstRelativeStrictMemberIdeal N H C π
  let Dt := monomialPartAlong n N' I' [π ⁻¹' C]
  let Dr := monomialPartAlong n N' P [π ⁻¹' C]
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hNC := hCborn
  obtain ⟨hENew,hTNew⟩ := actual_accumulated_exceptional_geometry hN hcH hE hT hπ hCN hNC
  change IsTransverse n N' E' at hTNew
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hcP : P.IsCoherent := isCoherent_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcH)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  let M0 : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  have hRaw := geoTransform_zeroMark_ideal_eq_restricted_total M0 rfl C π
  change (M0.geoTransform C π).ideal=P at hRaw
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hRaw]
    exact isNonzeroAlongAt_geoTransform_without_admissibility M0 hN hcH hπ hCN hnzH
  obtain ⟨hESingle,hTSingle⟩ := actual_accumulated_exceptional_geometry hN hcH isSNCDivisor_nil
    (isTransverse_nil_of_isClosedSubmanifold hN) hπ hCN (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
  change IsSNCDivisor n [π ⁻¹' C] at hESingle
  change IsTransverse n N' [π ⁻¹' C] at hTSingle
  obtain ⟨hcR,hcDr,hnzDr,hmDr,_hNo,hnzR,hFactor⟩ := parts_hypotheses hn
    (⟨N',[π ⁻¹' C],P,0⟩ : MarkedIdeal n Y) ⟨hN',hcP,hESingle,hTSingle⟩ hnzP
  have hRJ : nonmonomialPartAlong n N' P [π ⁻¹' C]=J :=
    actual_any_member_raw_nonmonomial_eq_relative_strict hn hN hH hdense hπ hCN
  have hcJ : J.IsCoherent := hRJ ▸ hcR
  have hnzJ : ∀ y ∈ N',IsNonzeroAlongAt N' J y := hRJ ▸ hnzR
  have hFRaw := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN'.1 hFactor.le hFactor.ge
  change restrictOn n N' P=restrictOn n N' ((nonmonomialPartAlong n N' P [π ⁻¹' C]).mul Dr) at hFRaw
  rw [hRJ,mul_comm' J Dr] at hFRaw
  have hNorm : restrictOn n N' P=P := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  have hPRaw : P=restrictOn n N' (Dr.mul J) := hNorm.symm.trans hFRaw
  obtain ⟨hcDt,hnzDt,hmDt,hPTrace⟩ := actual_incident_trace_greatest_factor_dictionary hn hN hH hdense hlocal hπ hCN
  have hSub : ∀ A ∈ [π ⁻¹' C],A ∈ E' := by
    intro A hA
    exact List.mem_append_right _ hA
  have hmDrAll : IsMonomialAlong n N' Dr E' := actual_isMonomialAlong_of_family_subset hSub hmDr
  have hmDtAll : IsMonomialAlong n N' Dt E' := actual_isMonomialAlong_of_family_subset hSub hmDt
  have hRawEq := actual_normalized_monomial_product_nonmonomial_eq hn hN' hENew hTNew hcDr hcJ hnzDr hnzJ hmDrAll
  have hTraceEq := actual_normalized_monomial_product_nonmonomial_eq hn hN' hENew hTNew hcDt hcJ hnzDt hnzJ hmDtAll
  change nonmonomialPartAlong n N' (restrictOn n N' (Dr.mul J)) E'=nonmonomialPartAlong n N' J E' at hRawEq
  change nonmonomialPartAlong n N' (restrictOn n N' (Dt.mul J)) E'=nonmonomialPartAlong n N' J E' at hTraceEq
  rw [←hPRaw] at hRawEq
  change I'=restrictOn n N' (Dt.mul J) at hPTrace
  rw [←hPTrace] at hTraceEq
  exact ⟨hENew,hTNew,hTraceEq.trans hRawEq.symm⟩

end
end Hironaka.HironakaSharpActualIncidentCentreTraceResidual
