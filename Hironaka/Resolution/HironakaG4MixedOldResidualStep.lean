import Hironaka.Resolution.HironakaG4TransverseOldResidualStep
import Hironaka.Resolution.HironakaSharpActualAccumulatedTraceResidual
import Hironaka.Resolution.HironakaSharpActualFirstAmbientStrictTraceFactor
import Hironaka.Resolution.HironakaSharpNormalCrossingsOpenLocus

set_option autoImplicit false

/-! Actual mixed old-row residual on the SAME blowup and ENTIRE born list.
Complete source-first chapter: hironaka-g4-mixed-old-residual-step.tex.
No arbitrary-centre order-one persistence or future history is asserted. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4MixedOldResidualStep
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings NormalCrossingsComparison
  NormalCrossingsInvariance HironakaSharpNormalCrossingsOpenLocus
  HironakaG4TransverseBoundaryStrictPullback HironakaG4PreparedCentreCoordinates
  HironakaSharpActualAccumulatedTraceResidual HironakaSharpActualMixedDiscreteTraceResidual
  HironakaSharpActualRawMemberOpenStrict HironakaSharpActualStrictTraceOpenNonmonomial
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaSharpActualFirstAmbientStrictTraceFactor
  HironakaSharpActualCompositeTotalResidual HironakaSharpActualTotalNonmonomialTransport
  HironakaSharpActualTotalAccumulatedResidual HironakaSharpActualChronologicalStrictStep
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  MonomialPartAlong NonmonomialTransformAlong GermIdealOrder DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen BlowupRestrictOpen

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem singleton_family_preimage {C H : Set X} {p : X}
    {S₀ : Finset (Fin n)} {S : Fin [H].length → Finset (Fin n)}
    (hF : IsCoordinateFamilyAt n
      (fun o : Option (Fin [H].length) => o.elim C fun i => [H].get i)
      (fun o => o.elim S₀ S) p) (U : Opens X) (hp : p ∈ U) :
    IsCoordinateFamilyAt n
      (fun o : Option (Fin [((Subtype.val : U → X) ⁻¹' H)].length) =>
        o.elim ((Subtype.val : U → X) ⁻¹' C)
          fun i => [((Subtype.val : U → X) ⁻¹' H)].get i)
      (fun o => o.elim S₀ S) (⟨p,hp⟩ : U) := by
  have hA : (fun o : Option (Fin [H].length) => (Subtype.val : U → X) ⁻¹'
      (o.elim C fun i => [H].get i))=
      (fun o : Option (Fin [((Subtype.val : U → X) ⁻¹' H)].length) =>
        o.elim ((Subtype.val : U → X) ⁻¹' C)
          fun i => [((Subtype.val : U → X) ⁻¹' H)].get i) := by
    funext o
    cases o <;> simp
  rw [←hA]
  exact isCoordinateFamilyAt_preimage_val_iff.mpr hF

/-- Literal NC coordinates internally yield actual contained or transverse
source windows, including every point outside either original set. -/
theorem exists_source_open_contained_or_transverse {C H : Set X}
    (hC : IsClosed C) (hH : IsClosed H) (hNC : HasNormalCrossings n C [H]) (p : X) :
    ∃ U : Opens X,p ∈ U ∧
      ((Subtype.val : U → X) ⁻¹' C ⊆ (Subtype.val : U → X) ⁻¹' H ∨
        IsTransverse n ((Subtype.val : U → X) ⁻¹' C) [((Subtype.val : U → X) ⁻¹' H)]) := by
  by_cases hpC : p ∈ C
  · by_cases hpH : p ∈ H
    · obtain ⟨S₀,S,hF,hcard⟩ := hNC p hpC
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard (0 : Fin [H].length) hpH)
      by_cases haS : a ∈ S₀
      · obtain ⟨Φ,hsrc,h0,hflat⟩ := hF
        let e := (complexChartAt (n := n) p).val
        let V := e.source ∩ e ⁻¹' Φ.source
        have hVo : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source Φ.isOpen_source
        have hpV : p ∈ V := ⟨mem_complexChartAt_source p,Φ.center_mem_source⟩
        let U : Opens X := ⟨V,hVo⟩
        refine ⟨U,hpV,Or.inl ?_⟩
        intro q hqC
        apply (hflat (some (0 : Fin [H].length)) hpH q.property.1 q.property.2).mpr
        change Φ.toFun (e q) ∈ coordSubspace (S 0)
        rw [ha]
        intro j hj
        rw [Finset.mem_singleton.mp hj]
        exact ((hflat none hpC q.property.1 q.property.2).mp hqC) a haS
      · have hclosed : ∀ o : Option (Fin [H].length),
            IsClosed ((fun o : Option (Fin [H].length) => o.elim C fun i => [H].get i) o) := by
          rintro (_ | i)
          · exact hC
          · simpa using hH
        obtain ⟨V,hV,hVo,hpV⟩ := mem_nhds_iff.mp (eventually_coordinateFamilyAt hclosed hF)
        let U : Opens X := ⟨V,hVo⟩
        refine ⟨U,hpV,Or.inr ?_⟩
        intro q _hqC
        refine ⟨S₀,S,singleton_family_preimage (hV q.property) U q.property,?_⟩
        intro i _hi
        have hi : i=(0 : Fin [H].length) := by
          apply Fin.ext
          change i.val=0
          have hlt := i.isLt
          simp only [List.length_singleton] at hlt
          omega
        subst i
        refine ⟨by rw [ha]; exact Finset.card_singleton a,?_⟩
        rw [ha,Finset.disjoint_singleton_left]
        exact haS
    · let U : Opens X := ⟨Hᶜ,hH.isOpen_compl⟩
      refine ⟨U,hpH,Or.inr ?_⟩
      intro q hqC
      obtain ⟨S₀,S,hF,_hcard⟩ := hNC q hqC
      refine ⟨S₀,S,singleton_family_preimage hF U q.property,?_⟩
      intro i hi
      have hiH : (q : X) ∈ H := by simpa using hi
      exact (q.property hiH).elim
  · let U : Opens X := ⟨Cᶜ,hC.isOpen_compl⟩
    refine ⟨U,hpC,Or.inr ?_⟩
    intro q hqC
    exact (q.property hqC).elim

private theorem nc_trace_geometry (hn : 0 < n) {N H C : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hNC : HasNormalCrossings n C [H])
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := geoStrictTransform π C N
    let H' := geoStrictTransform π C H
    let I' := restrictOn n N' (vanishingIdeal (n := n) H')
    let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
    IsClosedSubmanifold n N' ∧ IsClosedSubmanifold n H' ∧
      IsSNCDivisor n [π ⁻¹' C] ∧ IsTransverse n N' [π ⁻¹' C] ∧
      I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      P.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' P y) := by
  let N' := geoStrictTransform π C N
  let H' := geoStrictTransform π C H
  let I' := restrictOn n N' (vanishingIdeal (n := n) H')
  let M : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) H,0⟩
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  have hHsm : IsClosedSubmanifold n H :=
    MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hAmbient := SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hH hNC
  have hH' : IsClosedSubmanifold n H' := MonomialPart.isClosedSubmanifold_get hn hAmbient ⟨0,by simp⟩
  have hcI : I'.IsCoherent := isCoherent_restrictOn (VanishingIdealCoherent.isCoherent_vanishingIdeal hH')
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  have hRaw : (M.geoTransform C π).ideal=P := geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π
  have hcP : P.IsCoherent := isCoherent_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcH)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hRaw]
    exact isNonzeroAlongAt_geoTransform_without_admissibility M hN hcH hπ hCN hnzH
  have hLe := actual_pullback_vanishing_le_strict_vanishing hHsm.1 hπ
  have hPI : P.Le I' := fun y g hg =>
    ⟨hg.1,IsInSpanOnAt.mono (fun a ha => hLe y a ha) hg.2⟩
  have hnzI : ∀ y ∈ N',IsNonzeroAlongAt N' I' y := by
    intro y hy
    obtain ⟨g,hg,hfreq⟩ := hnzP y hy
    exact ⟨g,hPI y g hg,hfreq⟩
  obtain ⟨hENew,hTNew⟩ := actual_accumulated_exceptional_geometry hN hcH isSNCDivisor_nil
    (isTransverse_nil_of_isClosedSubmanifold hN) hπ hCN
    (hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
  change IsTransverse n N'
    ([].map (geoStrictTransform π C) ++ [π ⁻¹' C]) at hTNew
  exact ⟨hN',hH',by simpa only [List.map_nil,List.nil_append] using hENew,
    by simpa only [List.map_nil,List.nil_append] using hTNew,hcI,hnzI,hcP,hnzP⟩

/-- Genuine singleton centre NC, with arbitrary incidence, produces the WHOLE
strict-trace/raw-total residual identity on the SAME actual blowup. -/
theorem actual_nc_trace_nonmonomial_eq_raw (hn : 0 < n) {N H C : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) (hNC : HasNormalCrossings n C [H])
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    let N' := geoStrictTransform π C N
    let I' := restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C H))
    let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
    I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      nonmonomialPartAlong n N' I' [π ⁻¹' C]=nonmonomialPartAlong n N' P [π ⁻¹' C] := by
  let N' := geoStrictTransform π C N
  let H' := geoStrictTransform π C H
  let I' := restrictOn n N' (vanishingIdeal (n := n) H')
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
  let R := nonmonomialPartAlong n N' I' [π ⁻¹' C]
  let S := nonmonomialPartAlong n N' P [π ⁻¹' C]
  obtain ⟨hN',hH',hE,hT,hcI,hnzI,hcP,hnzP⟩ := nc_trace_geometry hn hN hH hdense hNC hπ hCN
  have hHsm : IsClosedSubmanifold n H :=
    MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hcR : R.IsCoherent := isCoherent_nonmonomialPartAlong hn hN' hE hT hcI hnzI
  have hcS : S.IsCoherent := isCoherent_nonmonomialPartAlong hn hN' hE hT hcP hnzP
  refine ⟨hcI,hnzI,?_⟩
  change R=S
  ext y g
  obtain ⟨U,hyU,hCase⟩ := exists_source_open_contained_or_transverse hπ.1.1 hHsm.1 hNC (π y)
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun z => ⟨π z,z.property⟩
  let NU := (Subtype.val : U → X) ⁻¹' N
  let HU := (Subtype.val : U → X) ⁻¹' H
  let CU := (Subtype.val : U → X) ⁻¹' C
  let NL := geoStrictTransform ρ CU NU
  let HL := geoStrictTransform ρ CU HU
  let IL := restrictOn n NL (vanishingIdeal (n := n) HL)
  let PL := restrictOn n NL (GermIdeal.pullback (m := n) ρ (vanishingIdeal (n := n) HU))
  let z : V := ⟨y,hyU⟩
  have hρ : IsBlowupAlong n CU ρ := isBlowupAlong_restrict hπ U V.isOpen
  have hNU : IsClosedSubmanifold n NU := isClosedSubmanifold_preimage_val hN U
  have hHU : IsSNCDivisor n [HU] := by
    simpa only [List.map_singleton] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U) continuous_subtype_val hH
  have hCNU : CU ⊆ NU := fun _ hx => hCN hx
  have hDenseU : NU ⊆ closure (NU \ HU) := by
    intro x hx
    have hcl : x ∈ (Subtype.val : U → X) ⁻¹' closure (N \ H) := hdense hx
    have he := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (N \ H)
    exact (Set.ext_iff.mp he x).mp hcl
  have hLocal : nonmonomialPartAlong n NL IL [ρ ⁻¹' CU]=
      nonmonomialPartAlong n NL PL [ρ ⁻¹' CU] := by
    rcases hCase with hContained | hTransverse
    · obtain ⟨_hcIL,_hnzIL,_hcD,_hnzD,_hmD,hNm,_hFactor⟩ :=
        actual_first_ambient_strict_trace_factor_dictionary
          (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V)
          hn hNU hHU hDenseU hρ hCNU hContained
      have hRaw := actual_any_member_raw_nonmonomial_eq_relative_strict
        (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V)
        hn hNU hHU hDenseU hρ hCNU
      exact hNm.trans hRaw.symm
    · change nonmonomialPartAlong n NL IL [ρ ⁻¹' CU]=
        nonmonomialPartAlong n NL (restrictOn n NL (GermIdeal.pullback (m := n) ρ
          (vanishingIdeal (n := n) HU))) [ρ ⁻¹' CU]
      rw [pullback_vanishingIdeal_eq_strict_of_transverse
        (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) hn hHU hTransverse hρ]
  have hNEq := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen N
  have hHEq := geoStrictTransform_restrict (C := C) (π := π) U V.isOpen H
  have hTraceOpen := actual_nonmonomial_open_germ_iff hn hN' hE hT hcI hnzI
    V z (g ∘ (Subtype.val : V → Y))
  have hTracePull := actual_normalized_trace_whole_open_pullback hN' hH' V
  rw [←hTracePull] at hTraceOpen
  rw [←hNEq,←hHEq] at hTraceOpen
  change (nonmonomialPartAlong n NL IL [ρ ⁻¹' CU]).mem z
    (g ∘ (Subtype.val : V → Y)) ↔ R.mem y (extendOpens V (g ∘ (Subtype.val : V → Y))) at hTraceOpen
  have hRawOpen := actual_raw_total_open_nonmonomial_iff hn hN hcH hnzH hπ hCN
    U z (g ∘ (Subtype.val : V → Y))
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal U H] at hRawOpen
  change (nonmonomialPartAlong n NL PL [ρ ⁻¹' CU]).mem z
    (g ∘ (Subtype.val : V → Y)) ↔ S.mem y (extendOpens V (g ∘ (Subtype.val : V → Y))) at hRawOpen
  rw [hLocal] at hTraceOpen
  have he : extendOpens V (g ∘ (Subtype.val : V → Y)) =ᶠ[𝓝 y] g := by
    filter_upwards [V.isOpen.mem_nhds hyU] with q hq
    exact extendOpens_val V (g ∘ (Subtype.val : V → Y)) ⟨q,hq⟩
  have hR : R.mem y (extendOpens V (g ∘ (Subtype.val : V → Y))) ↔ R.mem y g :=
    ⟨fun hg => HomogenizedIdeal.mem_congr hcR hg he,
      fun hg => HomogenizedIdeal.mem_congr hcR hg he.symm⟩
  have hS : S.mem y (extendOpens V (g ∘ (Subtype.val : V → Y))) ↔ S.mem y g :=
    ⟨fun hg => HomogenizedIdeal.mem_congr hcS hg he,
      fun hg => HomogenizedIdeal.mem_congr hcS hg he.symm⟩
  exact hR.symm.trans (hTraceOpen.symm.trans (hRawOpen.trans hS))

/-- Every real original old row has its actual chronological strict residual
on the SAME blowup and ENTIRE accumulated born list. Full actual centre NC
internally supplies both incidence branches; no old-transversality input. -/
theorem actual_mixed_old_residual_step (hn : 0 < n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hCNC : HasNormalCrossings n C (old ++ born)) :
    let N' := geoStrictTransform π C N
    let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    let I' := restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))
    I'.IsCoherent ∧ (∀ y ∈ N',IsNonzeroAlongAt N' I' y) ∧
      nonmonomialPartAlong n N' I' born'=
        nextRelativeStrict N (oldResidualPart N old born i) C π := by
  let I := oldTraceIdeal N old i
  let J := oldResidualPart N old born i
  let N' := geoStrictTransform π C N
  let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  let I' := restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (old.get i)))
  let Q := nextTotalMarked N I C π
  let R := nonmonomialPartAlong n N' P [π ⁻¹' C]
  let Dr := monomialPartAlong n N' P [π ⁻¹' C]
  let Dt := monomialPartAlong n N' I' [π ⁻¹' C]
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hSingle : IsSNCDivisor n [old.get i] := isSNCDivisor_of_sublist hOld (by simp)
  have hCSingle : HasNormalCrossings n C [old.get i] := by
    apply hasNormalCrossings_of_forall_mem hCNC
    intro H hH
    have he : H=old.get i := List.mem_singleton.mp hH
    rw [he]
    exact List.mem_append_left born (List.get_mem old i)
  have hCborn : HasNormalCrossings n C born :=
    hasNormalCrossings_of_forall_mem hCNC fun _ h => List.mem_append_right old h
  have hDenseH : N ⊆ closure (N \ old.get i) := by
    apply Set.Subset.trans hdense
    apply closure_mono
    intro x hx
    exact ⟨hx.1,fun hxH => hx.2 (mem_iUnion₂.mpr
      ⟨old.get i,List.mem_append_left born (List.get_mem old i),hxH⟩)⟩
  obtain ⟨hcI',hnzI',hNm⟩ := actual_nc_trace_nonmonomial_eq_raw hn hN hSingle hDenseH hCSingle hπ hCN
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hOld i)
  obtain ⟨hcI,hnzI,hcJ,hnzJ,_hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hRaw : Q.ideal=restrictOn n N' (GermIdeal.pullback (m := n) π I) :=
    geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],I,0⟩ : MarkedIdeal n X) rfl C π
  have hQP : Q.ideal=P := by
    rw [hRaw]
    change restrictOn n N' (GermIdeal.pullback (m := n) π
      (restrictOn n N (vanishingIdeal (n := n) (old.get i))))=P
    exact actual_normalized_pullback_restrictOn hN hN'.1 hcH hπ.contMDiff
      (fun _ hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)
  have hcP : P.IsCoherent := by
    rw [←hQP]
    exact isCoherent_geoTransform_ideal_without_inclusion (⟨N,[],I,0⟩ : MarkedIdeal n X)
      hN hcI hπ hCN
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hQP]
    exact isNonzeroAlongAt_geoTransform_without_admissibility (⟨N,[],I,0⟩ : MarkedIdeal n X)
      hN hcI hπ hCN hnzI
  obtain ⟨hENew,hTNew⟩ := actual_accumulated_exceptional_geometry hN hcI hBorn hTr hπ hCN hCborn
  change IsSNCDivisor n born' at hENew
  change IsTransverse n N' born' at hTNew
  have hESingle : IsSNCDivisor n [π ⁻¹' C] :=
    isSNCDivisor_of_sublist hENew (List.sublist_append_right _ _)
  have hTSingle : IsTransverse n N' [π ⁻¹' C] :=
    isTransverse_of_forall_mem hTNew fun _ h => List.mem_append_right _ h
  obtain ⟨hcR,hcDr,hnzDr,hmDr,_hNoR,hnzR,hFactorR⟩ := parts_hypotheses hn
    (⟨N',[π ⁻¹' C],P,0⟩ : MarkedIdeal n Y) ⟨hN',hcP,hESingle,hTSingle⟩ hnzP
  obtain ⟨_hcRt,hcDt,hnzDt,hmDt,_hNoT,_hnzRt,hFactorT⟩ := parts_hypotheses hn
    (⟨N',[π ⁻¹' C],I',0⟩ : MarkedIdeal n Y) ⟨hN',hcI',hESingle,hTSingle⟩ hnzI'
  have hNorm (A : GermIdeal n Y) : restrictOn n N' (restrictOn n N' A)=restrictOn n N' A := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  have hPRaw : P=restrictOn n N' (Dr.mul R) := by
    have hF := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN'.1 hFactorR.le hFactorR.ge
    change restrictOn n N' P=restrictOn n N' (R.mul Dr) at hF
    rw [RestrictLeCalculus.mul_comm' R Dr] at hF
    exact (hNorm (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (old.get i)))).symm.trans hF
  have hPTrace : I'=restrictOn n N' (Dt.mul R) := by
    have hF := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN'.1 hFactorT.le hFactorT.ge
    change restrictOn n N' I'=restrictOn n N'
      ((nonmonomialPartAlong n N' I' [π ⁻¹' C]).mul Dt) at hF
    change nonmonomialPartAlong n N' I' [π ⁻¹' C]=R at hNm
    rw [hNm,RestrictLeCalculus.mul_comm' R Dt] at hF
    exact (hNorm (vanishingIdeal (n := n) (geoStrictTransform π C (old.get i)))).symm.trans hF
  have hSub : ∀ A ∈ [π ⁻¹' C],A ∈ born' := fun _ h => List.mem_append_right _ h
  have hmDrAll : IsMonomialAlong n N' Dr born' := actual_isMonomialAlong_of_family_subset hSub hmDr
  have hmDtAll : IsMonomialAlong n N' Dt born' := actual_isMonomialAlong_of_family_subset hSub hmDt
  have hRawEq := actual_normalized_monomial_product_nonmonomial_eq hn hN' hENew hTNew
    hcDr hcR hnzDr hnzR hmDrAll
  have hTraceEq := actual_normalized_monomial_product_nonmonomial_eq hn hN' hENew hTNew
    hcDt hcR hnzDt hnzR hmDtAll
  change nonmonomialPartAlong n N' (restrictOn n N' (Dr.mul R)) born'=
    nonmonomialPartAlong n N' R born' at hRawEq
  change nonmonomialPartAlong n N' (restrictOn n N' (Dt.mul R)) born'=
    nonmonomialPartAlong n N' R born' at hTraceEq
  rw [←hPRaw] at hRawEq
  rw [←hPTrace] at hTraceEq
  have hActual : nonmonomialPartAlong n N' I' born'=nonmonomialPartAlong n N' P born' :=
    hTraceEq.trans hRawEq.symm
  have hprJ : ∀ x ∈ N,∃ c : X → ℂ,HolomorphicAt n c x ∧
      ∀ g,J.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=c) x g := by
    intro x hx
    obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hOld (List.get_mem old i) x
    have hIgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g :=
      fun g => and_congr_right fun _ =>
        HironakaSharpOriginalMemberProduct.restricted_span_iff_principal hf hF g
    obtain ⟨_m,c,_hm,_hmD,hc,_hfc,hJgen⟩ :=
      exists_actual_relative_principal_residual hn hN hBorn hTr hcI hnzI hx f hf hIgen
    exact ⟨c,GermIdeal.IsCoherent.holomorphicAt_mem hcJ hc,hJgen⟩
  obtain ⟨_hcJ,_hcM,_hnzM,_hmM,hNoBorn,_hnzJ,_hFactor⟩ :=
    parts_hypotheses hn (⟨N,born,I,0⟩ : MarkedIdeal n X) ⟨hN,hcI,hBorn,hTr⟩ hnzI
  have hTransport := actual_whole_total_nonmonomial_parts_transport hn hN hBorn hTr
    hcI hnzI hπ hCN hCborn
  have hStrict := nextTotal_accumulated_nonmonomial_eq_nextStrict hn hN hBorn hTr
    hcJ hnzJ hprJ hπ hCN hCborn hNoBorn
  change nonmonomialPartAlong n N' Q.ideal born'=
    nonmonomialPartAlong n N' (nextTotalMarked N J C π).ideal born' at hTransport
  change nonmonomialPartAlong n N' (nextTotalMarked N J C π).ideal born'=
    nextRelativeStrict N J C π at hStrict
  rw [hQP] at hTransport
  exact ⟨hcI',hnzI',hActual.trans (hTransport.trans hStrict)⟩

end
end Hironaka.HironakaG4MixedOldResidualStep
