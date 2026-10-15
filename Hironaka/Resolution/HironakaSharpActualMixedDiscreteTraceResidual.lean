/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualRawMemberOpenStrict

/-! Actual whole mixed-discrete-centre ambient trace residual comparison.
The greatest exceptional factor is retained; chronological tauD remains separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualMixedDiscreteTraceResidual
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualRawMemberOpenStrict HironakaSharpActualStrictTraceOpenNonmonomial
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry HironakaSharpActualDiscreteCentreMemberLocalBranch
  HironakaSharpOriginalFirstMemberRelativeStrict HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpActualChronologicalStrictStep HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension MarkedIdealRestrictOpen BlowupRestrictOpen
  MonomialPartAlong DivisorExponentAlong NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  InvertibleIdealQuotient GermIdealOrder NonmonomialTransformAlong RestrictLeCalculus
variable {n : ℕ} {X Y : CMfd.{u} n}

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

/-- Actual raw TOTAL whole open equality and independent real part geometry
supply BOTH full original extended-germ directions on the SAME restricted map. -/
theorem actual_raw_total_open_nonmonomial_iff (hn : 0 < n) {N C : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (U : Opens X) :
    let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V → U := fun z => ⟨π z,z.property⟩
    let CU := (Subtype.val : U → X) ⁻¹' C
    let NU := (Subtype.val : U → X) ⁻¹' N
    let NL := BlowupStrictSubmanifold.geoStrictTransform ρ CU NU
    let NG := BlowupStrictSubmanifold.geoStrictTransform π C N
    ∀ (z : V) (g : V → ℂ),
      (nonmonomialPartAlong n NL (restrictOn n NL
        (GermIdeal.pullback (m := n) ρ (GermIdeal.pullback (m := n) (Subtype.val : U → X) I))) [ρ ⁻¹' CU]).mem z g ↔
        (nonmonomialPartAlong n NG (restrictOn n NG (GermIdeal.pullback (m := n) π I)) [π ⁻¹' C]).mem z.val (extendOpens V g) := by
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  obtain ⟨hNG,hE,hTrans,hP,hNZ⟩ := actual_raw_geometry hN hI hnz hπ hCN
  have hOpen := actual_raw_total_whole_open_pullback hN hI hπ hCN U
  have hStrict := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen N
  dsimp only
  intro z g
  rw [hOpen,hStrict]
  simpa only [List.map_singleton,Set.preimage_preimage,Function.comp_def] using
    actual_nonmonomial_open_germ_iff hn hNG hE hTrans hP hNZ V z g

/-- True incident source isolation and independent local raw STRICT identify
BOTH SAME global residual germs on an ENTIRE actual preimage open. -/
theorem exists_actual_incident_global_residual_open_dictionary (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
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
    exists_actual_incident_discrete_member_restricted_factor hn hN hH hdense hrC hπ hCN hpC hpH
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
  have hTraceOpen := actual_mixed_discrete_strict_trace_open_nonmonomial_iff hn hN hH hdense hrC hπ hCN V z g
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

/-- ONLY original mixed discrete-centre inputs prove a WHOLE equality with
independently defined raw ALL-power STRICT, preserving the true exceptional factor. -/
theorem actual_mixed_discrete_trace_nonmonomial_eq_relative_strict (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
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
    actual_mixed_discrete_centre_whole_strict_trace_geometry hn hN hH hdense hrC hπ hCN
  obtain ⟨_hNG,hE,hTrans,hcP,hnzP⟩ := actual_raw_geometry hN hcH hnzH hπ hCN
  have hcR : R.IsCoherent := isCoherent_nonmonomialPartAlong hn hN' hE hTrans hcI hnzI
  have hcS : S.IsCoherent := isCoherent_nonmonomialPartAlong hn hN' hE hTrans hcP hnzP
  have hWhole : R=S := by
    ext x g
    by_cases hxC : π x ∈ C
    · by_cases hxH : π x ∈ H
      · obtain ⟨U,hxU,hDict⟩ := exists_actual_incident_global_residual_open_dictionary hn hN hH hdense hrC hπ hCN hxC hxH
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
independent raw STRICT for arbitrary mixed discrete centres, not only incident centres. -/
theorem actual_mixed_discrete_trace_greatest_factor_dictionary (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    let D' := monomialPartAlong n N' I' [π ⁻¹' C]
    D'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' D' y) ∧ IsMonomialAlong n N' D' [π ⁻¹' C] ∧
      I'=restrictOn n N' (D'.mul (firstRelativeStrictMemberIdeal N H C π)) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
  obtain ⟨hN',_hAmbient,hcI,hnzI,_hDense,_hPr⟩ :=
    actual_mixed_discrete_centre_whole_strict_trace_geometry hn hN hH hdense hrC hπ hCN
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  obtain ⟨_hN,hE,hT,_hcP,_hnzP⟩ := actual_raw_geometry hN hcH hnzH hπ hCN
  obtain ⟨_hcR,hcD,hnzD,hmD,_hNo,_hnzR,hFactor⟩ := parts_hypotheses hn
    (⟨N',[π ⁻¹' C],I',0⟩ : MarkedIdeal n Y) ⟨hN',hcI,hE,hT⟩ hnzI
  have hNm := actual_mixed_discrete_trace_nonmonomial_eq_relative_strict hn hN hH hdense hrC hπ hCN
  have hWhole := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN'.1 hFactor.le hFactor.ge
  change restrictOn n N' I'=restrictOn n N' ((nonmonomialPartAlong n N' I' [π ⁻¹' C]).mul
    (monomialPartAlong n N' I' [π ⁻¹' C])) at hWhole
  rw [hNm,mul_comm' (firstRelativeStrictMemberIdeal N H C π) (monomialPartAlong n N' I' [π ⁻¹' C])] at hWhole
  have hNorm : restrictOn n N' I'=I' := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  exact ⟨hcD,hnzD,hmD,hNorm.symm.trans hWhole⟩

end
end Hironaka.HironakaSharpActualMixedDiscreteTraceResidual
