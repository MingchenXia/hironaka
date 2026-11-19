import Hironaka.Resolution.HironakaG4LowerPreparedNeighborhood
import Hironaka.Resolution.HironakaG4ProtectedResidualEndpoint
import Hironaka.Resolution.HironakaG4PreparedMixedSelectedStep
import Hironaka.Resolution.HironakaG4SmoothSubcarrierResidualStep
import Hironaka.Resolution.HironakaActualCleanupDensityCompactness

/-! Local geometry for a genuinely chosen lower monomial step. No global
extension of an endpoint open or whole lower canonical consumer is asserted.
Source-first mathematics: hironaka-actual-protected-other-row-local-step.tex. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaActualProtectedOtherRowLocalStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower BlowupStrictSubmanifold NormalCrossings
  NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  BlowupFlatCoordinates MemberInterAlong HironakaG4PreparedCentreCoordinates
  HironakaG4ProtectedResidualEndpoint HironakaG4RecordedTowerResidualCompatibility
  HironakaG4OriginalSelectedResidualTail HironakaG4SmoothSubcarrierResidualStep
  HironakaG4LowerPreparedNeighborhood HironakaG4PreparedMixedSelectedStep
  HironakaG4MonomialFamilyInvariant HironakaG4ResidualInductionInputs
  HironakaActualCleanupDensityCompactness HironakaG4TransverseBoundaryStrictPullback
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualTraceIncidence
  HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpActualMixedCentreWholeStrictTraceGeometry
  HironakaSharpActualCompositeTotalResidual HironakaSharpActualControlledRelativeSaturation
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualStrictTraceOpenNonmonomial MonomialPartEtale
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaSharpOriginalFirstMemberRelativeStrict
  HironakaSharpActualPrincipalOrderOneTrace MarkedIdealBiholomorphism BlowupSNCTransform
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder
  NonmonomialTransformAlong MonomialPartAlong DivisorExponentAlong
  InvertibleIdealQuotient IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen BlowupRestrictOpen DerivativeIdealAlongEtale
  GermIdealPullbackCalculus BoundaryCount MarkedIdealTowerTransport

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem transverse_trace_reduced (hn : 0 < n) {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hTr : IsTransverse n N [H]) :
    IsClosedSubmanifold n (N ∩ H) ∧
      restrictOn n N (vanishingIdeal (n := n) H)=vanishingIdeal (n := n) (N ∩ H) := by
  obtain ⟨hc,hnz,_hpr,hOne⟩ := actual_normalized_transverse_member_geometry hn hN hH hTr
  have hd : N ⊆ closure (N \ H) := actual_density_of_nonzero_normalized_vanishing hnz
  have hOrd : ∀ x ∈ N,ordinaryTraceOrder N (restrictOn n N (vanishingIdeal (n := n) H)) x ≤ 1 := by
    intro x hxN
    by_cases hxH : x ∈ H
    · exact (hOne x ⟨hxN,hxH⟩).le
    · have hunit : (restrictOn n N (vanishingIdeal (n := n) H)).mem x 1 := by
        apply le_restrictOn (W := N) (VanishingIdealCoherent.isCoherent_vanishingIdeal
          (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)))
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [(hH.1 H (by simp)).isOpen_compl.mem_nhds hxH] with y hy hyH
        exact (hy hyH).elim
      by_contra hgt
      have hcos := (ordinaryTraceOrder_cosupport_iff hN hc hnz hxN 1).mpr (by omega)
      exact one_ne_zero ((vanishesToOrderOn_one_iff hxN (holomorphicAt_const 1)).mp (hcos.2 1 hunit))
  have hd' : N ⊆ closure (N \ ⋃ K ∈ [H],K) := by simpa using hd
  obtain ⟨hS,hWhole,_hTail⟩ := actual_original_selected_residual_tail hn hN hH hd'
    (0 : Fin [H].length) (BlowupTower.refl (X := X)) trivial hOrd
  have hHsmooth := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsmooth
  have hSet : N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus=N ∩ H := by
    ext x
    constructor
    · rintro ⟨hxN,hxJ⟩
      refine ⟨hxN,?_⟩
      have hxH := (zeroLocus_restrictOn_iff hcH hxN).mp hxJ
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1] at hxH
    · rintro ⟨hxN,hxH⟩
      refine ⟨hxN,(zeroLocus_restrictOn_iff hcH hxN).mpr ?_⟩
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1]
  change IsClosedSubmanifold n (N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus) at hS
  change restrictOn n N (vanishingIdeal (n := n) H)=
    vanishingIdeal (n := n) (N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus) at hWhole
  rw [hSet] at hS hWhole
  exact ⟨hS,hWhole⟩

private theorem transverse_slice_remaining (hn : 0 < n) {N H : Set X}
    {F : List (Set X)} (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F)) : IsTransverse n (N ∩ H) F := by
  intro x hx
  obtain ⟨_kC,kN,Φ,s,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hE hTr hTr.hasNormalCrossings hx.1
  let z : Fin (H :: F).length := ⟨0,by simp⟩
  let c : Fin F.length → Fin (H :: F).length := fun a =>
    ⟨a.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using a.isLt⟩
  have hz : (H :: F).get z=H := rfl
  have hc (a : Fin F.length) : (H :: F).get (c a)=F.get a := by
    simp [c,List.get_eq_getElem]
  have hxH : x ∈ (H :: F).get z := by rw [hz];exact hx.2
  let Q : Finset (Fin n) := Finset.univ.filter fun t => kN ≤ t.val
  refine ⟨Q ∪ {s z},fun a => {s (c a)},?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | a) hxa y hy hyΦ
    · change y ∈ N ∩ H ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace (Q ∪ {s z})
      rw [ExceptionalPushforwardAlong.coordSubspace_union]
      change (y ∈ N ∧ y ∈ H) ↔
        (Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s z})
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      rw [show coordSubspace Q=complexCoordinatePlane n kN by
        simp only [Q,coordSubspace_eq_complexCoordinatePlane]]
      exact and_congr (by simpa only [complexChartAt] using (hflat hy hyΦ).2.1)
        (by simpa only [hz,complexChartAt] using (hflat hy hyΦ).2.2 z hxH)
    · change y ∈ F.get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace {s (c a)}
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have ha : x ∈ (H :: F).get (c a) := by rw [hc];exact hxa
      simpa only [hc,complexChartAt] using (hflat hy hyΦ).2.2 (c a) ha
  · intro a hxa
    have ha : x ∈ (H :: F).get (c a) := by rw [hc];exact hxa
    refine ⟨by simp,Finset.disjoint_singleton_left.mpr ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hQ | heq
    · have hge := (Finset.mem_filter.mp hQ).2
      exact Nat.not_lt_of_ge hge (hs (c a) ha)
    · have he : c a=z := hinj ha hxH (Finset.mem_singleton.mp heq)
      have hv := congrArg Fin.val he
      dsimp [c,z] at hv
      omega

theorem transverse_slice_step (hn : 0 < n) {N H C : Set X}
    {F : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (H :: F)) (hTr : IsTransverse n N (H :: F))
    (hCN : C ⊆ N) (hCNC : HasNormalCrossings n C (H :: F))
    (hCH : IsTransverse n C [H]) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    let Z := N ∩ H
    let Z' := geoStrictTransform π C Z
    let F' := F.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    IsClosedSubmanifold n Z' ∧
      nextRelativeStrict N (vanishingIdeal (n := n) Z) C π=vanishingIdeal (n := n) Z' ∧
      HasNormalCrossings n Z' F' ∧ Z' ⊆ closure (Z' \ ⋃ K ∈ F',K) := by
  let Z := N ∩ H
  let Z' := geoStrictTransform π C Z
  let N' := geoStrictTransform π C N
  let H' := geoStrictTransform π C H
  let D := π ⁻¹' C
  let F' := F.map (geoStrictTransform π C) ++ [D]
  have hH : IsSNCDivisor n [H] := isSNCDivisor_of_sublist hE (by simp)
  have hNH : IsTransverse n N [H] :=
    isTransverse_of_forall_mem hTr (by intro K hK;rw [List.mem_singleton.mp hK];simp)
  have hWhole := (transverse_trace_reduced hn hN hH hNH).2
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hE' : IsSNCDivisor n (H' :: F') := by
    simpa only [List.map_cons,List.cons_append] using
      isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hE hCNC
  have hTr' : IsTransverse n N' (H' :: F') := by
    simpa only [List.map_cons,List.cons_append] using
      isTransverse_geoTransformE_of_hasNormalCrossings hπ hN.1 hCN hE hTr hCNC
  have hZeq : Z'=N' ∩ H' := by
    change geoStrictTransform π C (N ∩ H)=N' ∩ H'
    calc
      _ = geoStrictTransform π C (H ∩ N) := congrArg _ (inter_comm N H)
      _ = H' ∩ N' :=
        ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hπ hN.1 hCN hE hTr hCNC
          (0 : Fin (H :: F).length)
      _ = N' ∩ H' := inter_comm _ _
  have hH' : IsSNCDivisor n [H'] := isSNCDivisor_of_sublist hE' (by simp)
  have hNH' : IsTransverse n N' [H'] :=
    isTransverse_of_forall_mem hTr' (by intro K hK;rw [List.mem_singleton.mp hK];simp)
  have hSlice := transverse_trace_reduced hn hN' hH' hNH'
  have hZ' : IsClosedSubmanifold n Z' := by rw [hZeq];exact hSlice.1
  have hZF : IsTransverse n Z' F' := by
    rw [hZeq]
    exact transverse_slice_remaining hn hE' hTr'
  have hFE : IsSNCDivisor n F' := isSNCDivisor_of_sublist hE' (List.tail_sublist (H' :: F'))
  have hDensity : Z' ⊆ closure (Z' \ ⋃ K ∈ F',K) := by
    simpa only [List.nil_append] using actual_cleanup_source_full_density
      (O := []) (B := F') hn hZ' (by simpa using hFE) hZF (by simpa using (subset_closure : Z' ⊆ closure Z'))
  have hDensityD : Z' ⊆ closure (Z' \ D) := by
    apply hDensity.trans (closure_mono ?_)
    rintro z ⟨hz,hOff⟩
    exact ⟨hz,fun hzD => hOff (mem_iUnion₂.mpr
      ⟨D,List.mem_append_right _ (List.mem_singleton_self D),hzD⟩)⟩
  have hZsub : Z' ⊆ N' := by rw [hZeq];exact inter_subset_left
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length))
  change (vanishingIdeal (n := n) H).IsCoherent at hcH
  let M : MarkedIdeal n X := ⟨N,[],vanishingIdeal (n := n) Z,0⟩
  have hRaw : (M.geoTransform C π).ideal=vanishingIdeal (n := n) Z' := by
    rw [geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π]
    change restrictOn n N' (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) Z))=_
    rw [←hWhole,actual_normalized_pullback_restrictOn hN hN'.1 hcH hπ.contMDiff
      (fun _ hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy),
      pullback_vanishingIdeal_eq_strict_of_transverse hn hH hCH hπ,hSlice.2,hZeq]
  have hSat := geoTransform_relativeExceptionalSaturation_eq hn M hπ
  change relativeExceptionalSaturation N' (M.geoTransform C π).ideal D=
    nextRelativeStrict N (vanishingIdeal (n := n) Z) C π at hSat
  rw [hRaw] at hSat
  have hSatIdeal := relativeExceptionalSaturation_vanishingIdeal_eq hn
    (BlowupSNCTransform.isSNCDivisor_preimage_centre hπ) hZsub hDensityD
  exact ⟨hZ',hSat.symm.trans hSatIdeal,hZF.hasNormalCrossings,hDensity⟩


/-- Internal coordinate ingredients follow the existing lower-neighborhood
proof because its corresponding helpers are private. No separate achievement
is assigned to these reused source-coordinate arguments. -/
private theorem member_index_lt_of_dense {C : Set X} {E : List (Set X)}
    (hdense : C ⊆ closure (C \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ C)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (k : ℕ) (s : Fin E.length → Fin n)
    (hC : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k))
    (hH : ∀ i,x ∈ E.get i → ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s i)=0)) :
    ∀ i,x ∈ E.get i → (s i).val < k := by
  intro i hi
  by_contra hnot
  have hge : k ≤ (s i).val := Nat.le_of_not_gt hnot
  let e := (complexChartAt (n := n) x).val
  have hU : IsOpen (e.source ∩ e ⁻¹' Φ.source) :=
    e.continuousOn.isOpen_inter_preimage e.open_source Φ.isOpen_source
  have hxU : x ∈ e.source ∩ e ⁻¹' Φ.source :=
    ⟨mem_complexChartAt_source x,Φ.center_mem_source⟩
  obtain ⟨y,hyU,hyC,hyE⟩ := mem_closure_iff.mp (hdense hx) _ hU hxU
  have hyCoord := (hC hyU.1 hyU.2).mp hyC
  have hyH : y ∈ E.get i := (hH i hi hyU.1 hyU.2).mpr (hyCoord (s i) hge)
  exact hyE (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hyH⟩)

private theorem bounded_order_one_dimensions {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hc : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) {x : X}
    (hx : x ∈ N ∩ I.zeroLocus)
    (hpr : ∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hOrd : ordinaryTraceOrder N I x=1)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (kC kN : ℕ)
    (hCflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ∩ I.zeroLocus ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kC))
    (hNflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kN)) :
    min kN n=min kC n+1 := by
  have hRegN : RegularAtDim (n := n) N x (min kN n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun hy hyΦ => by rw [BoundaryCount.complexCoordinatePlane_min];exact hNflat hy hyΦ)
      hx.1 (mem_complexChartAt_source x) Φ.center_mem_source
  have hRegC : RegularAtDim (n := n) (N ∩ I.zeroLocus) x (min kC n) :=
    RegularPatchNeighborhood.regularAtDim_of_flattening (min_le_right _ _) Φ
      (fun hy hyΦ => by rw [BoundaryCount.complexCoordinatePlane_min];exact hCflat hy hyΦ)
      hx (mem_complexChartAt_source x) Φ.center_mem_source
  have hPos : 0 < min kN n := by
    by_contra hnot
    have he : min kN n=0 := by omega
    rw [he] at hRegN
    obtain ⟨O,hOo,hxO,hIso⟩ :=
      PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hRegN
    obtain ⟨g,hg,hFreq⟩ := hnz x hx.1
    obtain ⟨y,⟨hyN,hgy⟩,hyO⟩ := (hFreq.and_eventually (hOo.mem_nhds hxO)).exists
    have hyx : y=x := Set.mem_singleton_iff.mp (hIso ⟨hyN,hyO⟩)
    apply hgy
    rw [hyx]
    exact hx.2 g hg
  obtain ⟨f,hf,hgen⟩ := hpr
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,_hRed,k,hNk,hCk⟩ :=
    HironakaSharpActualPrincipalOrderOneTrace.actual_orderOne_relative_reduced_trace
      hN hc hnz hx.1 f hf hgen hOrd
  have hk : k=min kN n := RegularPointDimension.eq_of_regularAtDim hNk hRegN
  have hCdim : min kC n=k-1 := RegularPointDimension.eq_of_regularAtDim hRegC hCk
  omega

private theorem exists_centered_nested_chart_from_transverse_window (hn : 0 < n)
    {C N : Set X} {E : List (Set X)} (hCN : C ⊆ N)
    (hE : IsSNCDivisor n E) (hCNC : HasNormalCrossings n C E)
    {x : X} (hx : x ∈ C) (U : Opens X) (hxU : x ∈ U)
    (hTrU : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))) :
    ∃ (kC kN : ℕ)
      (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
      (s : Fin E.length → Fin n),
      kC ≤ n ∧ kN ≤ n ∧ Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x)=0 ∧
      (∀ i,x ∈ E.get i → (s i).val < kN) ∧ Set.InjOn s {i | x ∈ E.get i} ∧
      ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kC) ∧
        (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n kN) ∧
        ∀ i,x ∈ E.get i →
          (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s i)=0) := by
  let u : U := ⟨x,hxU⟩
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let c : Fin E.length → Fin EU.length := Fin.cast (List.length_map _).symm
  have hget (i : Fin E.length) : EU.get (c i)=(Subtype.val : U → X) ⁻¹' E.get i := by
    simp [EU,c,List.get_eq_getElem]
  have hEU : IsSNCDivisor n EU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hCNCU := hasNormalCrossings_preimage (pullsBackCoordinates_val U) hCNC
  obtain ⟨a,b,Ψ,s₀,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (preimage_mono hCN) hEU hTrU hCNCU (x := u) hx
  let QC : Finset (Fin n) := Finset.univ.filter fun t : Fin n => a ≤ t.val
  let QN : Finset (Fin n) := Finset.univ.filter fun t : Fin n => b ≤ t.val
  let A : Option (Option (Fin E.length)) → Set X :=
    fun o => o.elim C (fun p => p.elim N E.get)
  let S : Option (Option (Fin E.length)) → Finset (Fin n) :=
    fun o => o.elim QC (fun p => p.elim QN (fun i => {s₀ (c i)}))
  have hFamilyFlat : ∀ o,u ∈ (Subtype.val : U → X) ⁻¹' A o → ∀ {z : U},
      z ∈ (complexChartAt (n := n) u).val.source →
      (complexChartAt (n := n) u).val z ∈ Ψ.source →
      (z ∈ (Subtype.val : U → X) ⁻¹' A o ↔
        Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace (S o)) := by
    rintro (_ | (_ | i)) hi z hz hzΨ
    · change (z.val ∈ C ↔ Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace QC)
      simp only [QC,coordSubspace_eq_complexCoordinatePlane]
      exact (hflat hz hzΨ).1
    · change (z.val ∈ N ↔ Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace QN)
      simp only [QN,coordSubspace_eq_complexCoordinatePlane]
      exact (hflat hz hzΨ).2.1
    · change (z.val ∈ E.get i ↔
        Ψ.toFun ((complexChartAt (n := n) u).val z) ∈ coordSubspace {s₀ (c i)})
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have hiU : u ∈ EU.get (c i) := by rw [hget];exact hi
      have hh := (hflat hz hzΨ).2.2 (c i) hiU
      rw [hget] at hh
      exact hh
  have hFamilyU : IsCoordinateFamilyAt n
      (fun o => (Subtype.val : U → X) ⁻¹' A o) S u :=
    coordinateFamilyAt_of_flattening Ψ hFamilyFlat
      (mem_complexChartAt_source u) Ψ.center_mem_source (fun _ hi => hi)
  have hFamilyX : IsCoordinateFamilyAt n A S x := isCoordinateFamilyAt_preimage_val_iff.mp hFamilyU
  obtain ⟨Φ,hΦsrc,hΦ0,hΦ⟩ := hFamilyX
  refine ⟨min a n,min b n,Φ,(fun i => s₀ (c i)),min_le_right _ _,min_le_right _ _,
    hΦsrc,hΦ0,?_,?_,?_⟩
  · intro i hi
    have hiU : u ∈ EU.get (c i) := by rw [hget];exact hi
    exact lt_min (hs (c i) hiU) (s₀ (c i)).isLt
  · intro i hi j hj heq
    have hiU : u ∈ EU.get (c i) := by rw [hget];exact hi
    have hjU : u ∈ EU.get (c j) := by rw [hget];exact hj
    have hc := hinj hiU hjU heq
    exact Fin.ext (by simpa [c] using congrArg Fin.val hc)
  · intro y hy hyΦ
    refine ⟨?_,?_,?_⟩
    · rw [BoundaryCount.complexCoordinatePlane_min]
      have hh := hΦ none hx hy hyΦ
      change (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QC) at hh
      simpa only [QC,coordSubspace_eq_complexCoordinatePlane] using hh
    · rw [BoundaryCount.complexCoordinatePlane_min]
      have hh := hΦ (some none) (hCN hx) hy hyΦ
      change (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QN) at hh
      simpa only [QN,coordSubspace_eq_complexCoordinatePlane] using hh
    · intro i hi
      have hh := hΦ (some (some i)) hi hy hyΦ
      change (y ∈ E.get i ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s₀ (c i)}) at hh
      simpa only [BlowupSNCTransform.mem_coordSubspace_singleton] using hh

private theorem actual_processed_nested_chart
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    {x : Y} (hx : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
      (s : Fin F.length → Fin n),
      k+1 ≤ n ∧ Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x)=0 ∧
      (∀ a,x ∈ F.get a → (s a).val < k) ∧ Set.InjOn s {a | x ∈ F.get a} ∧
      ∀ {y : Y},y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ S ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k) ∧
        (y ∈ A.N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n (k+1)) ∧
        ∀ a,x ∈ F.get a →
          (y ∈ F.get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s a)=0) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let S := A.N ∩ I.zeroLocus
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
  obtain ⟨hNi,_hEi,_hdi,hwi,hnzi,hpri⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  rw [hNi] at hOrd hx hnzi hpri
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hRecorded.2.1
    ((List.eraseIdx_sublist (E.map (strictAlong T)) i.val).append (List.Sublist.refl A.E))
  obtain ⟨_hS,_hWhole,hWindows,_hLocal,_hDisjoint⟩ :=
    actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull hOrd hNC hDenseS
  obtain ⟨U,hxU,_hEU,hTransU⟩ := hWindows x hx
  obtain ⟨kC,kN,Φ,s,hkC,hkN,hsrc,h0,_hsN,hinj,hflat⟩ :=
    exists_centered_nested_chart_from_transverse_window hn inter_subset_left hF hNC hx U hxU hTransU
  have hCflat := fun {y : Y} hy hyΦ => (hflat (y := y) hy hyΦ).1
  have hNflat := fun {y : Y} hy hyΦ => (hflat (y := y) hy hyΦ).2.1
  have hHflat := fun a ha {y : Y} hy hyΦ => (hflat (y := y) hy hyΦ).2.2 a ha
  have hcos : x ∈ cosupport n A.N I 1 := by
    rw [GermIdealOrder.cosupport_one (fun _ _ hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem hwi.isCoherent hg)]
    exact hx
  have hLower := (ordinaryTraceOrder_cosupport_iff hN hwi.isCoherent hnzi hx.1 1).mp hcos
  have hOne : ordinaryTraceOrder A.N I x=1 := (hOrd x hx.1).antisymm hLower
  have hDim := bounded_order_one_dimensions hN hwi.isCoherent hnzi hx (hpri x hx.1)
    hOne Φ kC kN hCflat hNflat
  simp only [min_eq_left hkC,min_eq_left hkN] at hDim
  have hsC := member_index_lt_of_dense hDenseS hx Φ kC s hCflat hHflat
  refine ⟨kC,Φ,s,by omega,hsrc,h0,hsC,hinj,?_⟩
  intro y hy hyΦ
  rw [←hDim]
  exact hflat hy hyΦ



private theorem isClosed_actual_flat_lift {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ) (q : Fin n) :
    IsClosed {a : U | flatCoord Φ q a.val = 0} := by
  have hc : Continuous (fun a : U => flatCoord Φ q a.val) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (holomorphicAt_flatCoord Φ q (hU a.property)).continuousAt.comp
      continuous_subtype_val.continuousAt
  exact isClosed_eq hc continuous_const

private theorem actual_partial_flat_frame {m : ℕ} {x : X} {R : Set X} (hx : x ∈ R)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ)
    (P : Fin m → Prop) (p : Fin m → Fin n) (Q : Finset (Fin n))
    (hR : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ R ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q)) :
    let E : List (Set U) := List.ofFn fun k =>
      if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
    let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
    ∀ a : U,IsCoordinateFamilyAt n
      (fun o : Option (Fin E.length) => o.elim ((Subtype.val : U → X) ⁻¹' R) E.get)
      (fun o => o.elim Q (fun i => {p (c i)})) a := by
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
  let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
  change ∀ a : U,IsCoordinateFamilyAt n
    (fun o : Option (Fin E.length) => o.elim ((Subtype.val : U → X) ⁻¹' R) E.get)
    (fun o => o.elim Q (fun i => {p (c i)})) a
  have hget (i : Fin E.length) : E.get i=
      if P (c i) then {a : U | flatCoord Φ (p (c i)) a.val=0} else ∅ := by
    simp only [E,List.get_eq_getElem,List.getElem_ofFn,c]
  let A : Option (Fin m) → Set X := fun o =>
    o.elim R (fun k => if P k then {y | flatCoord Φ (p k) y=0} else ∅)
  let T : Option (Fin m) → Finset (Fin n) := fun o => o.elim Q (fun k => {p k})
  intro a
  have hflat : ∀ o,x ∈ A o → ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ A o ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (T o)) := by
    rintro (_ | k) hi y hy hyΦ
    · exact hR hy hyΦ
    · by_cases hk : P k
      · simp only [A,T,Option.elim,if_pos hk,Set.mem_ofPred_eq,flatCoord,
          coordSubspace,Finset.mem_singleton,forall_eq]
        rfl
      · simp only [A,Option.elim,if_neg hk,mem_empty_iff_false] at hi
  have hseen : ∀ o,a.val ∈ A o → x ∈ A o := by
    rintro (_ | k) hi
    · exact hx
    · by_cases hk : P k
      · change x ∈ if P k then {y | flatCoord Φ (p k) y=0} else ∅
        rw [if_pos hk]
        change Φ.toFun ((complexChartAt (n := n) x).val x) (p k)=0
        rw [h0]
        rfl
      · simp only [A,Option.elim,if_neg hk,mem_empty_iff_false] at hi
  have hfX := coordinateFamilyAt_of_flattening Φ hflat
    (hU a.property).1 (hU a.property).2 hseen
  have hfU := isCoordinateFamilyAt_preimage_val_iff.mpr hfX
  apply IsCoordinateFamilyAt.reindex hfU (Option.map c)
  · rintro (_ | i)
    · rfl
    · change E.get i=(Subtype.val : U → X) ⁻¹' A (some (c i))
      rw [hget]
      by_cases hi : P (c i) <;> simp only [A,Option.elim,hi,if_pos,if_neg,
        preimage_empty,not_false_eq_true]
      rfl
  · rintro (_ | i) <;> rfl


private theorem actual_partial_flat_snc {m : ℕ} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ)
    (P : Fin m → Prop) (p : Fin m → Fin n) (hinj : Set.InjOn p {k | P k}) :
    IsSNCDivisor n (List.ofFn fun k =>
      if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅) := by
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
  let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
  have hget (i : Fin E.length) : E.get i=
      if P (c i) then {a : U | flatCoord Φ (p (c i)) a.val=0} else ∅ := by
    simp only [E,List.get_eq_getElem,List.getElem_ofFn,c]
  have hP {a : U} {i : Fin E.length} (hi : a ∈ E.get i) : P (c i) := by
    rw [hget] at hi
    by_contra hnot
    simp only [if_neg hnot,mem_empty_iff_false] at hi
  refine ⟨?_,fun a => ?_⟩
  · intro H hH
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hH
    by_cases hk : P k
    · rw [if_pos hk]
      exact isClosed_actual_flat_lift Φ U hU _
    · rw [if_neg hk]
      exact isClosed_empty
  · have hR : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ (univ : Set X) ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace ∅) := by
      intro y _hy _hyΦ
      simp [coordSubspace]
    have hf := actual_partial_flat_frame (mem_univ x) Φ h0 U hU P p ∅ hR a
    refine ⟨fun i => {p (c i)},?_,fun _ _ => Finset.card_singleton _,?_⟩
    · exact IsCoordinateFamilyAt.reindex hf some (fun _ => rfl) (fun _ => rfl)
    · intro i hi j hj he
      have hij := hinj (hP hi) (hP hj) (Finset.singleton_injective he)
      exact Fin.ext (show i.val=j.val from congrArg (fun k : Fin m => k.val) hij)

private theorem actual_partial_flat_transverse {m : ℕ} {x : X} {R : Set X}
    (hx : x ∈ R)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ)
    (P : Fin m → Prop) (p : Fin m → Fin n) (Q : Finset (Fin n))
    (hR : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ R ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q))
    (hfree : ∀ k,P k → p k ∉ Q) :
    IsTransverse n ((Subtype.val : U → X) ⁻¹' R) (List.ofFn fun k =>
      if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅) := by
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
  let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
  intro a _ha
  refine ⟨Q,fun i => {p (c i)},actual_partial_flat_frame hx Φ h0 U hU P p Q hR a,?_⟩
  intro i hi
  have hget : E.get i=if P (c i) then {a : U | flatCoord Φ (p (c i)) a.val=0} else ∅ := by
    simp only [E,List.get_eq_getElem,List.getElem_ofFn,c]
  have hP : P (c i) := by
    change a ∈ E.get i at hi
    rw [hget] at hi
    by_contra hn
    simp only [if_neg hn,mem_empty_iff_false] at hi
  refine ⟨Finset.card_singleton _,Finset.disjoint_left.mpr ?_⟩
  intro j hj hjQ
  rw [Finset.mem_singleton.mp hj] at hjQ
  exact hfree _ hP hjQ


private theorem open_parts_pullback (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X) (i : Fin old.length) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let IU := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
    monomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldMonomialPart N old born i) ∧
    nonmonomialPartAlong n NU IU bornU = GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (oldResidualPart N old born i) := by
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  obtain ⟨hcI,_hnzI,hcJ,_hnzJ,hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hIU := actual_normalized_trace_whole_open_pullback hN
    (MonomialPart.isClosedSubmanifold_get hn hOld i) U
  dsimp only
  rw [hIU]
  exact ⟨(pullback_monomialPartAlong
    (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)).symm,
    (pullback_nonmonomialPartAlong
      (fun y : U => ⟨openInv U y,isLocalInverseAt_val U y⟩) hcI hcD hcJ).symm⟩

private theorem open_full_density {N : Set X} {E : List (Set X)}
    (hdense : N ⊆ closure (N \ ⋃ H ∈ E,H)) (U : Opens X) :
    (Subtype.val : U → X) ⁻¹' N ⊆ closure ((Subtype.val : U → X) ⁻¹' N \
      ⋃ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
  intro y hy
  have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (N \ ⋃ H ∈ E,H) := hdense hy
  erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (N \ ⋃ H ∈ E,H)] at hp
  convert hp using 1
  congr 1
  ext z
  simp

private theorem current_prepared_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ y ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hPrepared : ∀ y ∈ N,IsPreparedResidualSNCAt N old born y) (U : Opens X) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    (∀ y ∈ NU,∀ i,ordinaryTraceOrder NU
      (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) y ≤ 1) ∧
    ∀ y ∈ NU,IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) NU oldU bornU y := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let cO : Fin oldU.length → Fin old.length := Fin.cast (by simp [oldU])
  let cB : Fin bornU.length → Fin born.length := Fin.cast (by simp [bornU])
  let c : Fin oldU.length ⊕ Fin bornU.length → Fin old.length ⊕ Fin born.length := Sum.map cO cB
  have hO (i : Fin oldU.length) : oldU.get i = (Subtype.val : U → X) ⁻¹' old.get (cO i) :=
    get_map_preimage old i
  have hB (i : Fin bornU.length) : bornU.get i = (Subtype.val : U → X) ⁻¹' born.get (cB i) :=
    get_map_preimage born i
  have hJ (i : Fin oldU.length) :
      oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i =
        GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born (cO i)) := by
    change nonmonomialPartAlong n NU (restrictOn n NU (vanishingIdeal (n := n) (oldU.get i))) bornU = _
    rw [hO]
    exact (open_parts_pullback hn hN hE hTr hdense U (cO i)).2
  have hNU := isClosedSubmanifold_preimage_val hN U
  have hFullU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ oldU ++ bornU,H) := by
    simpa only [List.map_append] using open_full_density hdense U
  have hPartsU := fun i => actual_old_parts_geometry (X := CMfd.of (n := n) U)
    hn hNU hFullU hTrU hDenseU i
  have hParts := fun i => actual_old_parts_geometry hn hN hE hTr hdense i
  refine ⟨?_,?_⟩
  · intro y hy i
    by_contra ho
    have hTwo : 2 ≤ ordinaryTraceOrder NU
        (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) y :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge ho)
    have hMem := (ordinaryTraceOrder_cosupport_iff hNU (hPartsU i).2.2.1
      (hPartsU i).2.2.2.1 hy 2).mpr hTwo
    rw [hJ,cosupport_pullback_of_local
      (fun z : U => ⟨openInv U z,isLocalInverseAt_val U z⟩)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hParts (cO i)).2.2.1 hg)] at hMem
    have hLower := (ordinaryTraceOrder_cosupport_iff hN (hParts (cO i)).2.2.1
      (hParts (cO i)).2.2.2.1 hy 2).mp hMem
    have hUpper := hOrd y.val hy (cO i)
    omega
  · intro y hy
    have hSupport (a : Fin oldU.length ⊕ Fin bornU.length) :
        preparedSupport (X := CMfd.of (n := n) U) NU oldU bornU a =
          (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c a) := by
      cases a with
      | inl i =>
        simp only [preparedSupport,Sum.elim_inl,c,Sum.map_inl]
        rw [hJ,BlowupExceptionalDivisor.zeroLocus_pullback
          contMDiff_subtype_val (hParts (cO i)).2.2.1]
        rfl
      | inr i =>
        simp only [preparedSupport,Sum.elim_inr,c,Sum.map_inr]
        rw [hB]
        rfl
    have hcInj : Function.Injective c := by
      intro a b hab
      cases a <;> cases b <;> simp_all [c,cO,cB,Fin.ext_iff]
    obtain ⟨S₀,p,hFam,hFree,hInj⟩ := hPrepared y.val hy
    refine ⟨S₀,p ∘ c,?_,?_,?_⟩
    · apply IsCoordinateFamilyAt.reindex (isCoordinateFamilyAt_preimage_val_iff.mpr hFam)
        (Option.map c)
      · rintro (_ | a)
        · rfl
        · exact hSupport a
      · rintro (_ | a) <;> rfl
    · intro a ha
      apply hFree (c a)
      exact show y ∈ (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c a) from
        (hSupport a) ▸ ha
    · intro a ha b hb hab
      apply hcInj
      have ha' : (y : X) ∈ preparedSupport N old born (c a) := by
        change y ∈ (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c a)
        rw [←hSupport]
        exact ha
      have hb' : (y : X) ∈ preparedSupport N old born (c b) := by
        change y ∈ (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c b)
        rw [←hSupport]
        exact hb
      exact hInj ha' hb' hab


private def innerOpen (U V : Opens X) : Opens U :=
  ⟨(Subtype.val : U → X) ⁻¹' V,V.isOpen.preimage continuous_subtype_val⟩

private def innerOpenEquiv (U V : Opens X) (hVU : (V : Set X) ⊆ U) :
    innerOpen U V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V where
  toFun a := ⟨a.val.val,a.property⟩
  invFun a := ⟨⟨a.val,hVU a.property⟩,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      ((Subtype.val : U → X) ∘ (Subtype.val : innerOpen U V → U))
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (innerOpen U V) _).mp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact contMDiff_subtype_val

private theorem actual_vanishingIdeal_open (Z : Set X)
    (hZ : IsClosedSubmanifold n Z) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) Z)=
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' Z) := by
  have hZU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hZ U
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) Z
  rw [BlowupControlledTransform.pullback_id
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hZU)] at h
  exact h.symm

private theorem protected_slice_from_nested_chart
    {N S : Set X} {F : List (Set X)} (hF : IsSNCDivisor n F)
    {x : X} (hxN : x ∈ N) (O : Opens X) (hxO : x ∈ O)
    (G : Set X) (hG : G ∈ 𝓝 x)
    (k : ℕ) (hkn : k+1 ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (s : Fin F.length → Fin n)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x)=0)
    (hs : ∀ a,x ∈ F.get a → (s a).val < k)
    (hinj : Set.InjOn s {a | x ∈ F.get a})
    (hflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ S ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k) ∧
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n (k+1)) ∧
      ∀ a,x ∈ F.get a →
        (y ∈ F.get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (s a)=0)) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ O ∧ (U : Set X) ⊆ G ∧ ∃ H : Set U,
      IsSNCDivisor n (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
        (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (Subtype.val : U → X) ⁻¹' S=((Subtype.val : U → X) ⁻¹' N) ∩ H := by
  classical
  have hData : ∀ᶠ y in 𝓝 x,y ∈ flatDomain Φ ∧
      (∀ a : Fin F.length,y ∈ F.get a → x ∈ F.get a) ∧
      y ∈ G := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),
      eventually_incident_subset F.get (fun a => hF.1 _ (List.get_mem F a)) x,hG]
      with y hy hseen hloc
    exact ⟨hy,hseen,hloc⟩
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hData
  let U : Opens X := ⟨V ∩ O,hVo.inter O.isOpen⟩
  have hU : (U : Set X) ⊆ flatDomain Φ := fun y hy => (hV hy.1).1
  let r : Fin n := ⟨k,by omega⟩
  let H : Set U := {y | flatCoord Φ r y.val=0}
  let P : Fin (F.length+1) → Prop := Fin.cases True (fun a => x ∈ F.get a)
  let p : Fin (F.length+1) → Fin n := Fin.cases r s
  have hInjective : Set.InjOn p {a | P a} := by
    intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro _ha b
      refine Fin.cases ?_ (fun b => ?_) b
      · intro _hb _he
        rfl
      · intro hb he
        have hb' : x ∈ F.get b := hb
        have hbLt := hs b hb'
        have hv := congrArg Fin.val he
        change k=(s b).val at hv
        omega
    · intro ha b
      refine Fin.cases ?_ (fun b => ?_) b
      · intro _hb he
        have ha' : x ∈ F.get a := ha
        have haLt := hs a ha'
        have hv := congrArg Fin.val he
        change (s a).val=k at hv
        omega
      · intro hb he
        have hab : a=b := hinj ha hb he
        exact congrArg Fin.succ hab
  let Flat : List (Set U) := List.ofFn fun a =>
    if P a then {y : U | flatCoord Φ (p a) y.val=0} else ∅
  have hFlatE : IsSNCDivisor n Flat := actual_partial_flat_snc Φ h0 U hU P p hInjective
  let Q : Finset (Fin n) := Finset.univ.filter fun a => k+1 ≤ a.val
  have hNflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q) := by
    intro y hy hyΦ
    rw [show coordSubspace Q=complexCoordinatePlane n (k+1) by
      simp only [Q,coordSubspace_eq_complexCoordinatePlane]]
    exact (hflat hy hyΦ).2.1
  have hFree : ∀ a,P a → p a ∉ Q := by
    intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro _ha hmem
      have hk := (Finset.mem_filter.mp hmem).2
      change k+1 ≤ k at hk
      omega
    · intro ha hmem
      have hge := (Finset.mem_filter.mp hmem).2
      have hlt := hs a ha
      change k+1 ≤ (s a).val at hge
      omega
  have hFlatTr : IsTransverse n ((Subtype.val : U → X) ⁻¹' N) Flat :=
    actual_partial_flat_transverse hxN Φ h0 U hU P p Q hNflat hFree
  have hTail (a : Fin F.length) :
      (if x ∈ F.get a then {y : U | flatCoord Φ (s a) y.val=0} else ∅)=
        (Subtype.val : U → X) ⁻¹' F.get a := by
    ext y
    by_cases ha : x ∈ F.get a
    · rw [if_pos ha]
      exact ((hflat (hU y.property).1 (hU y.property).2).2.2 a ha).symm
    · rw [if_neg ha]
      exact iff_of_false (by simp) (fun hy => ha ((hV y.property.1).2.1 a hy))
  have hFlatEq : Flat=H :: F.map ((Subtype.val : U → X) ⁻¹' ·) := by
    change List.ofFn (fun a => if P a then {y : U | flatCoord Φ (p a) y.val=0} else ∅)=_
    rw [List.ofFn_succ]
    have hP0 : P 0 := trivial
    rw [if_pos hP0]
    change H :: List.ofFn (fun a => if P a.succ then
      {y : U | flatCoord Φ (p a.succ) y.val=0} else ∅)=_
    congr 1
    have hTail' (a : Fin F.length) :
        (if P a.succ then {y : U | flatCoord Φ (p a.succ) y.val=0} else ∅)=
          (Subtype.val : U → X) ⁻¹' F.get a := by
      by_cases ha : x ∈ F.get a
      · have hPa : P a.succ := ha
        rw [if_pos hPa]
        simpa only [if_pos ha,p,Fin.cases_succ] using hTail a
      · have hPa : ¬P a.succ := ha
        rw [if_neg hPa]
        simpa only [if_neg ha] using hTail a
    rw [show (fun a : Fin F.length => if P a.succ then
      {y : U | flatCoord Φ (p a.succ) y.val=0} else ∅)=
        (fun a => (Subtype.val : U → X) ⁻¹' F.get a) from funext hTail']
    simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map F
      ((Subtype.val : U → X) ⁻¹' ·)
  have hSEq : (Subtype.val : U → X) ⁻¹' S=((Subtype.val : U → X) ⁻¹' N) ∩ H := by
    ext y
    have hf := hflat (hU y.property).1 (hU y.property).2
    change y.val ∈ S ↔ y.val ∈ N ∧ flatCoord Φ r y.val=0
    rw [hf.1,hf.2.1]
    constructor
    · intro hy
      exact ⟨fun a ha => hy a (by omega),hy r le_rfl⟩
    · rintro ⟨hy,hr⟩ a ha
      by_cases hak : a.val=k
      · have he : a=r := Fin.ext hak
        simpa only [he,flatCoord,complexChartAt] using hr
      · exact hy a (by omega)
  exact ⟨U,⟨hxV,hxO⟩,fun _ hy => hy.2,fun _ hy => (hV hy.1).2.2,H,
    hFlatEq ▸ hFlatE,hFlatEq ▸ hFlatTr,hSEq⟩

/-- A prepared smooth codimension-one support can be realized on a smaller
window by an auxiliary ambient divisor transverse to the carrier and the
same remaining ordered boundary. -/
theorem exists_protected_slice_window_of_relative_support
    (hn : 0 < n) {N S : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hSN : S ⊆ N) (hF : IsSNCDivisor n F)
    (hDenseN : N ⊆ closure (N \ ⋃ D ∈ F, D)) (hNC : HasNormalCrossings n S F)
    (hDenseS : S ⊆ closure (S \ ⋃ D ∈ F, D))
    {x : X} (hx : x ∈ S) {d : ℕ} (hRegN : RegularAtDim (n := n) N x (d+1))
    (hRegS : RegularAtDim (n := n) S x d) (O : Opens X) (hxO : x ∈ O) :
    ∃ U : Opens X, x ∈ U ∧ U ≤ O ∧ ∃ H : Set U,
      IsSNCDivisor n (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
        (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (Subtype.val : U → X) ⁻¹' S=((Subtype.val : U → X) ⁻¹' N) ∩ H := by
  have hPoint := HironakaSharpNestedNormalCrossingsInheritance.actual_normalCrossingsAt_of_nested_density
    hn hSN hN hDenseS hx (hNC x hx)
  obtain ⟨V,hxV,_,hTrV⟩ := exists_actual_original_transverse_neighborhood hN.1 hF hDenseN hPoint
  obtain ⟨kS,kN,Φ,s,hkS,hkN,_,h0,_,hinj,hflat⟩ :=
    exists_centered_nested_chart_from_transverse_window hn hSN hF hNC hx V hxV hTrV
  have hsFlat := fun {y : X} hy hyΦ => (hflat (y := y) hy hyΦ).1
  have hnFlat := fun {y : X} hy hyΦ => (hflat (y := y) hy hyΦ).2.1
  have hFflat := fun a ha {y : X} hy hyΦ => (hflat (y := y) hy hyΦ).2.2 a ha
  have hRS : RegularAtDim (n := n) S x kS :=
    RegularPatchNeighborhood.regularAtDim_of_flattening hkS Φ
      (fun hy hyΦ => by simpa only [coordSubspace_eq_complexCoordinatePlane] using hsFlat hy hyΦ)
      hx (mem_complexChartAt_source x) Φ.center_mem_source
  have hRN : RegularAtDim (n := n) N x kN :=
    RegularPatchNeighborhood.regularAtDim_of_flattening hkN Φ
      (fun hy hyΦ => by simpa only [coordSubspace_eq_complexCoordinatePlane] using hnFlat hy hyΦ)
      (hSN hx) (mem_complexChartAt_source x) Φ.center_mem_source
  have hEqS := RegularPointDimension.eq_of_regularAtDim hRS hRegS
  have hEqN := RegularPointDimension.eq_of_regularAtDim hRN hRegN
  have hFree := member_index_lt_of_dense hDenseS hx Φ kS s hsFlat hFflat
  have hk : kS+1 = kN := by omega
  rw [←hk] at hflat
  obtain ⟨U,hxU,hUO,_,H,hE,hTr,hSlice⟩ :=
    protected_slice_from_nested_chart hF (hSN hx) O hxO univ Filter.univ_mem kS
      (hk.trans_le hkN) Φ s h0 hFree hinj hflat
  exact ⟨U,hxU,hUO,H,hE,hTr,hSlice⟩

/-- The selected actual retained residual is the whole ideal of its
closed smooth support once its order is at most one on the carrier. -/
theorem native_row_globally_reduced (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (i : Fin old.length)
    (hOrd : ∀ x ∈ N, ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1) :
    let S := N ∩ (oldResidualPart N old born i).zeroLocus
    IsClosedSubmanifold n S ∧ oldResidualPart N old born i = vanishingIdeal (n := n) S := by
  obtain ⟨hcI,_,hcJ,hnzJ,_,_,_,_⟩ := actual_old_parts_geometry hn hN hFull hTr hDense i
  have hNormal : (vanishingIdeal (n := n) N).Le (oldResidualPart N old born i) := by
    intro x g hg
    exact le_nonmonomialPartAlong_self hcI x g (vanishingIdeal_le_restrictOn x g hg)
  exact actual_relative_row_globally_reduced hN _ hcJ hnzJ
    (fun _ hx => actual_residual_principal_native hn hN hFull hTr hDense i hx) hNormal hOrd

/-- The protected source window of a single prepared native row, including
the whole residual on the literal open. -/
theorem native_prepared_source_slice_window (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born, D))
    (i : Fin old.length)
    (hOrd : ∀ x ∈ N, ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hNC : HasNormalCrossings n (N ∩ (oldResidualPart N old born i).zeroLocus)
      (old.eraseIdx i.val ++ born))
    (hDenseS : N ∩ (oldResidualPart N old born i).zeroLocus ⊆
      closure ((N ∩ (oldResidualPart N old born i).zeroLocus) \ ⋃ D ∈ old.eraseIdx i.val ++ born,D))
    {x : X} (hx : x ∈ N ∩ (oldResidualPart N old born i).zeroLocus)
    (O : Opens X) (hxO : x ∈ O) :
    let S := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := old.eraseIdx i.val ++ born
    ∃ U : Opens X, x ∈ U ∧ U ≤ O ∧ ∃ H : Set U,
      IsSNCDivisor n (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' N) (H :: F.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (Subtype.val : U → X) ⁻¹' S = ((Subtype.val : U → X) ⁻¹' N) ∩ H ∧
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) =
        vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' S) := by
  let F := old.eraseIdx i.val ++ born
  have hSub : F.Sublist (old ++ born) :=
    (List.eraseIdx_sublist old i.val).append (List.Sublist.refl born)
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hFull hSub
  have hDenseF : N ⊆ closure (N \ ⋃ D ∈ F, D) :=
    hDense.trans (closure_mono (fun _ hz => ⟨hz.1, fun h =>
      let ⟨D,hD,hzD⟩ := mem_iUnion₂.mp h
      hz.2 (mem_iUnion₂.mpr ⟨D,hSub.subset hD,hzD⟩)⟩))
  have hDim := (actual_residual_support_local_geometry_of_row_order hn hN hFull hTr hDense i hOrd).2.2
  obtain ⟨d,hRegN,hRegS⟩ := (hDim x hx).2.2
  obtain ⟨U,hxU,hUO,H,hSNC,hTrans,hSlice⟩ :=
    exists_protected_slice_window_of_relative_support hn hN inter_subset_left hF
      hDenseF hNC hDenseS hx hRegN hRegS O hxO
  obtain ⟨hS,hI⟩ := native_row_globally_reduced hn hN hFull hTr hDense i hOrd
  refine ⟨U,hxU,hUO,H,hSNC,hTrans,hSlice,?_⟩
  exact (congrArg (GermIdeal.pullback (m := n) (Subtype.val : U → X)) hI).trans
    (actual_vanishingIdeal_open _ hS U)

theorem protected_slice_window (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    {x : Y} (hx : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (O : Opens Y) (hxO : x ∈ O) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
    ∃ U : Opens Y,x ∈ U ∧ (U : Set Y) ⊆ O ∧ ∃ H : Set U,
      IsSNCDivisor n (H :: F.map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → Y) ⁻¹' A.N)
        (H :: F.map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
      (Subtype.val : U → Y) ⁻¹' Si=((Subtype.val : U → Y) ⁻¹' A.N) ∩ H ∧
      GermIdeal.pullback (m := n) (Subtype.val : U → Y)
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal=
          vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' Si) ∧
      ∀ h : Fin E.length,h ≠ i →
        GermIdeal.pullback (m := n) (Subtype.val : U → Y)
          (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal=
            restrictOn n ((Subtype.val : U → Y) ⁻¹' A.N)
              (vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h))) ∧
        (Subtype.val : U → Y) ⁻¹' (A.N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal.zeroLocus)=
            ((Subtype.val : U → Y) ⁻¹' A.N) ∩
              ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h)) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let J := fun h : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let I := fun h : Fin E.length =>
    restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get h)))
  let Si := A.N ∩ (J i).zeroLocus
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ A.E
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hRecorded.2.1
    ((List.eraseIdx_sublist (E.map (strictAlong T)) i.val).append (List.Sublist.refl A.E))
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  have hxSi : x ∈ Si := by simpa only [hNi] using hx
  have hOrdA : ∀ y ∈ A.N,ordinaryTraceOrder A.N (J i) y ≤ 1 := by
    simpa only [hNi] using hOrd
  have hProtect := actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull
    hOrdA hNC hDenseS
  have hSi : IsClosedSubmanifold n Si := hProtect.1
  have hWhole : J i=vanishingIdeal (n := n) Si := hProtect.2.1
  obtain ⟨k,Φ,s,hkn,_,h0,hs,hinj,hflat⟩ :=
    actual_processed_nested_chart hn hW hE hdense i T hT hFull hOrd hNC hDenseS hx
  have hLocal : ∀ᶠ y in 𝓝 x,∀ h : Fin E.length,h ≠ i → ∀ g,(I h).mem y g ↔ (J h).mem y g := by
    apply eventually_all.mpr
    intro h
    by_cases he : h=i
    · exact Eventually.of_forall fun _ hne => (hne he).elim
    · filter_upwards [hProtect.2.2.2.1 h he x hxSi] with y hy
      exact fun _ => hy.2
  let G : Set Y := {y | ∀ h : Fin E.length,h ≠ i → ∀ g,(I h).mem y g ↔ (J h).mem y g}
  obtain ⟨U,hxU,hUO,hUG,H,hWindowE,hWindowTr,hSiEq⟩ :=
    protected_slice_from_nested_chart hF hxSi.1 O hxO G hLocal k hkn Φ s h0 hs hinj hflat
  have hJOpen : GermIdeal.pullback (m := n) (Subtype.val : U → Y) (J i)=
      vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' Si) := by
    rw [hWhole]
    exact actual_vanishingIdeal_open Si hSi U
  refine ⟨U,hxU,hUO,H,hWindowE,hWindowTr,hSiEq,hJOpen,?_⟩
  intro h hne
  have hRows := hRecorded.2.2.2.2 h
  have hcJ : (J h).IsCoherent := by
    obtain ⟨_hN,_hE,_hd,hw,_hnz,_hpr⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense h T hT
    exact hw.isCoherent
  have hOld : IsSNCDivisor n (E.map (strictAlong T)) :=
    isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left _ _)
  let a : Fin (E.map (strictAlong T)).length :=
    ⟨h.val,by simpa only [List.length_map] using h.isLt⟩
  have hHsmooth : IsClosedSubmanifold n (strictAlong T (E.get h)) := by
    have hh := MonomialPart.isClosedSubmanifold_get hn hOld a
    simpa [a] using hh
  have hOpen : GermIdeal.pullback (m := n) (Subtype.val : U → Y) (J h)=
      restrictOn n ((Subtype.val : U → Y) ⁻¹' A.N)
        (vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' strictAlong T (E.get h))) := by
    rw [HironakaSharpActualStrictTraceOpenNonmonomial.actual_normalized_trace_whole_open_pullback
      hN hHsmooth U]
    ext y g
    rw [MarkedIdealRestrictOpen.mem_pullback_val_iff U hcJ,
      MarkedIdealRestrictOpen.mem_pullback_val_iff U hRows.1]
    exact (hUG y.property h hne _).symm
  refine ⟨hOpen,?_⟩
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsmooth
  ext y
  change (y.val ∈ A.N ∧ y.val ∈ (J h).zeroLocus) ↔
    (y.val ∈ A.N ∧ y.val ∈ strictAlong T (E.get h))
  constructor
  · rintro ⟨hyN,hyJ⟩
    refine ⟨hyN,?_⟩
    have hyI : y.val ∈ (I h).zeroLocus :=
      fun g hg => hyJ g ((hUG y.property h hne g).mp hg)
    have hyH := (zeroLocus_restrictOn_iff hcH hyN).mp hyI
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1] at hyH
  · rintro ⟨hyN,hyH⟩
    refine ⟨hyN,?_⟩
    have hyI : y.val ∈ (I h).zeroLocus := by
      apply (zeroLocus_restrictOn_iff hcH hyN).mpr
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1]
    exact fun g hg => hyI g ((hUG y.property h hne g).mpr hg)

private theorem nonunit_pullback_restrict {Z : CMfd.{u} n} {I : GermIdeal n X}
    (hI : I.IsCoherent) {f : Z → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    {L : Set Z} {z : Z} (hz : z ∈ L) (hnot : ¬I.mem (f z) 1) :
    ¬(restrictOn n L (GermIdeal.pullback (m := n) f I)).mem z 1 := by
  have hzI : f z ∈ I.zeroLocus := by
    intro g hg
    by_contra hne
    exact hnot (CompanionReduction.one_mem_of_apply_ne_zero hI hg hne)
  have hPull := BlowupExceptionalDivisor.zeroLocus_pullback hf hI
  have hzPull : z ∈ (GermIdeal.pullback (m := n) f I).zeroLocus := by
    rw [hPull]
    exact hzI
  have hzRes := (zeroLocus_restrictOn_iff (isCoherent_pullback hf hI) hz).mpr hzPull
  exact fun hunit => one_ne_zero (hzRes 1 hunit)

private theorem divExpAlong_zero_of_notMem {N H : Set X} {I : GermIdeal n X}
    (hNH : IsClosed (N ∩ H)) {z : X} (hz : z ∉ H) : divExpAlong n N I H z = 0 := by
  have hnot : ¬ ∃ e, ¬ IsDivNearAlong n N I H (e + 1) z := by
    rintro ⟨e,he⟩
    exact he (isDivNearAlong_of_notMem hNH (fun h => hz h.2) (e+1))
  rw [divExpAlong,dif_neg hnot]

private theorem incident_selection_feasible {N : Set X} {B : List (Set X)}
    (hN : IsClosed N) (hB : ∀ H ∈ B,IsClosed H)
    {r : ℕ} (D : Fin r → GermIdeal n X) (x : X)
    (hActive : (properRows (fun i b => divExpAlong n N (D i) (B.get b) x)).Nonempty) :
    let S := Finset.univ.filter fun b : Fin B.length => x ∈ B.get b
    S.Nonempty ∧ ∀ i ∈ properRows (fun i b => divExpAlong n N (D i) (B.get b) x),
      1 ≤ ∑ b ∈ S,divExpAlong n N (D i) (B.get b) x := by
  let A : Fin r → Fin B.length → ℕ := fun i b => divExpAlong n N (D i) (B.get b) x
  let S := Finset.univ.filter fun b : Fin B.length => x ∈ B.get b
  have hOff (i : Fin r) (b : Fin B.length) (hb : b ∉ S) : A i b=0 := by
    apply divExpAlong_zero_of_notMem (hN.inter (hB _ (List.get_mem B b)))
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hb
  have hSum (i : Fin r) : (∑ b ∈ S,A i b)=∑ b,A i b := by
    exact Finset.sum_subset (Finset.subset_univ S) (fun b _hb hbS => hOff i b hbS)
  have hFeasible (i : Fin r) (hi : i ∈ properRows A) : 1 ≤ ∑ b ∈ S,A i b := by
    rw [hSum]
    exact (Finset.mem_filter.mp hi).2
  refine ⟨?_,hFeasible⟩
  obtain ⟨i,hi⟩ := hActive
  have hPos := hFeasible i hi
  by_contra hEmpty
  have hS : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
  rw [hS,Finset.sum_empty] at hPos
  omega

private theorem transverse_stratum_omitted (hn : 0 < n) {N H : Set X}
    {F : List (Set X)} (hE : IsSNCDivisor n (H :: F))
    (hTr : IsTransverse n N (H :: F)) (S : Finset (Fin F.length)) :
    IsTransverse n (N ∩ memberInter F S) [H] := by
  intro x hx
  obtain ⟨_kC,kN,Φ,s,_hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hE hTr hTr.hasNormalCrossings hx.1
  let z : Fin (H :: F).length := ⟨0,by simp⟩
  let c : Fin F.length → Fin (H :: F).length := fun a =>
    ⟨a.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using a.isLt⟩
  have hz : (H :: F).get z=H := rfl
  have hc (a : Fin F.length) : (H :: F).get (c a)=F.get a := by
    simp [c,List.get_eq_getElem]
  let QN : Finset (Fin n) := Finset.univ.filter fun t => kN ≤ t.val
  let QF : Finset (Fin n) := S.biUnion fun a => {s (c a)}
  refine ⟨QN ∪ QF,fun _ => {s z},?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | a) hxa y hy hyΦ
    · change y ∈ N ∩ memberInter F S ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (QN ∪ QF)
      rw [ExceptionalPushforwardAlong.coordSubspace_union]
      change (y ∈ N ∧ ∀ b ∈ S,y ∈ F.get b) ↔
        (Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QN ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QF)
      refine and_congr ?_ ?_
      · rw [show coordSubspace QN=complexCoordinatePlane n kN by
          simp only [QN,coordSubspace_eq_complexCoordinatePlane]]
        simpa only [complexChartAt] using (hflat hy hyΦ).2.1
      · rw [show coordSubspace QF=coordSubspace (S.biUnion fun b => {s (c b)}) by rfl,
          BoundaryCount.mem_coordSubspace_biUnion]
        apply forall₂_congr
        intro b hb
        rw [BlowupSNCTransform.mem_coordSubspace_singleton]
        have hxb : x ∈ (H :: F).get (c b) := by rw [hc];exact hx.2 b hb
        simpa only [hc,complexChartAt] using (hflat hy hyΦ).2.2 (c b) hxb
    · have ha : [H].get a=H := by fin_cases a;rfl
      change x ∈ [H].get a at hxa
      change (y ∈ [H].get a ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s z})
      rw [ha] at hxa ⊢
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have hxh : x ∈ (H :: F).get z := by rw [hz];exact hxa
      simpa only [hz,complexChartAt] using (hflat hy hyΦ).2.2 z hxh
  · intro a hxa
    have ha : [H].get a=H := by fin_cases a;rfl
    rw [ha] at hxa
    have hxh : x ∈ (H :: F).get z := by rw [hz];exact hxa
    refine ⟨by simp,Finset.disjoint_singleton_left.mpr ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hQN | hQF
    · have hge := (Finset.mem_filter.mp hQN).2
      exact Nat.not_lt_of_ge hge (hs z hxh)
    · obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp hQF
      have hxb : x ∈ (H :: F).get (c b) := by rw [hc];exact hx.2 b hb
      have hidx := hinj hxh hxb (Finset.mem_singleton.mp he)
      have hv := congrArg Fin.val hidx
      dsimp [z,c] at hv
      omega

private theorem stratum_slice_step (hn : 0 < n) {N H : Set X}
    {F : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (H :: F)) (hTr : IsTransverse n N (H :: F))
    (S : Finset (Fin F.length)) {π : Y → X}
    (hπ : IsBlowupAlong n (N ∩ memberInter F S) π) :
    let C := N ∩ memberInter F S
    let Z := N ∩ H
    let Z' := geoStrictTransform π C Z
    let F' := F.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    IsClosedSubmanifold n Z' ∧
      nextRelativeStrict N (vanishingIdeal (n := n) Z) C π=vanishingIdeal (n := n) Z' ∧
      HasNormalCrossings n Z' F' ∧ Z' ⊆ closure (Z' \ ⋃ K ∈ F',K) := by
  let e : Fin F.length ↪ Fin (H :: F).length :=
    ⟨Fin.succ,fun a b he => Fin.ext (Nat.succ.inj (congrArg Fin.val he))⟩
  have hget (a : Fin F.length) : (H :: F).get (e a)=F.get a := by
    change (H :: F).get a.succ=F.get a
    rfl
  have hInter : memberInter (H :: F) (S.map e)=memberInter F S := by
    ext y
    constructor
    · intro hy a ha
      have hh := hy (e a) (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
      simpa only [hget] using hh
    · intro hy a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
      simpa only [hget] using hy b hb
  have hCNC := hasNormalCrossings_inter_memberInter hTr (S.map e)
  rw [hInter] at hCNC
  exact transverse_slice_step hn hN hE hTr inter_subset_left hCNC
    (transverse_stratum_omitted hn hE hTr S) hπ

private theorem full_boundary_nc_of_lower {C : Set X} {old born : List (Set X)}
    (hE : IsSNCDivisor n (old ++ born)) (j : Fin old.length)
    (hOwn : C ⊆ old.get j)
    (hSmall : HasNormalCrossings n C (old.eraseIdx j.val ++ born)) :
    HasNormalCrossings n C (old ++ born) := by
  apply hasNormalCrossings_of_forall_notMem hE hSmall
  intro H hH hNot
  rcases List.mem_append.mp hH with hOld | hBorn
  · obtain ⟨a,ha⟩ := List.mem_iff_get.mp hOld
    have haj : a.val=j.val := by
      by_contra hne
      exact hNot (List.mem_append_left born
        (List.mem_eraseIdx_iff_getElem.mpr ⟨a.val,a.isLt,hne,ha⟩))
    have he : a=j := Fin.ext haj
    rw [he] at ha
    rw [←ha]
    exact hOwn
  · exact False.elim (hNot (List.mem_append_right _ hBorn))


private theorem choose_local_protected_monomial_step (hn : 0 < n)
    {N H Sj : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ K ∈ old ++ born,K))
    (i j : Fin old.length) (hne : j ≠ i)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born)))
    (hAuxTr : IsTransverse n N (H :: (old.eraseIdx i.val ++ born)))
    (hSj : IsClosedSubmanifold n Sj) (hSjTrace : Sj=N ∩ old.get j)
    (hSjSupport : Sj=N ∩ (oldResidualPart N old born j).zeroLocus)
    (hSjTr : IsTransverse n Sj born)
    (hSjDense : Sj ⊆ closure (Sj \ ⋃ K ∈ old.eraseIdx j.val ++ born,K))
    (hLowerOrd : ∀ y ∈ Sj,∀ a,ordinaryTraceOrder Sj
      (oldResidualPart Sj (old.eraseIdx j.val) born a) y ≤ 1)
    (hLowerPrepared : ∀ y ∈ Sj,IsPreparedResidualSNCAt Sj (old.eraseIdx j.val) born y)
    {x : X} (hx : x ∈ (N ∩ H) ∩ Sj)
    (hActive : (properRows (fun (a : Fin (old.eraseIdx j.val).length) (b : Fin born.length) =>
      divExpAlong n Sj (oldMonomialPart Sj (old.eraseIdx j.val) born a) (born.get b) x)).Nonempty) :
    ∃ (U : Opens X) (Z : CMfd.{u} n) (C : Set U) (π : Z → U) (hπ : IsBlowupAlong n C π),
      x ∈ U ∧
      let NU := (Subtype.val : U → X) ⁻¹' N
      let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
      let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
      let SiU := (Subtype.val : U → X) ⁻¹' (N ∩ H)
      let SjU := (Subtype.val : U → X) ⁻¹' Sj
      let F := oldU.eraseIdx i.val ++ bornU
      let R : BlowupTower (CMfd.of (n := n) U) Z := .step .refl C π hπ
      ∃ S : Finset (Fin bornU.length),S.Nonempty ∧
        C=SjU ∩ memberInter bornU S ∧ (∃ c ∈ C,c.val=x) ∧ interior C=∅ ∧
        HasNormalCrossings n C (oldU ++ bornU) ∧
        C ⊆ originalSharpBadLocus (n := n) SjU (oldU.eraseIdx j.val ++ bornU) ∧
        C ⊆ originalSharpBadLocus (n := n) NU (oldU ++ bornU) ∧
        IsGeoTestTower (geometricTemplate NU bornU) R ∧
        IsGeoTestTower (geometricTemplate (univ : Set U) (oldU ++ bornU)) R ∧
        IsClosedSubmanifold n (geoStrictTransform π C SiU) ∧
        nextRelativeStrict (X := CMfd.of (n := n) U) (Y := Z)
          NU (vanishingIdeal (n := n) SiU) C π=
          vanishingIdeal (n := n) (geoStrictTransform π C SiU) ∧
        HasNormalCrossings n (geoStrictTransform π C SiU)
          (F.map (geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
        geoStrictTransform π C SiU ⊆ closure (geoStrictTransform π C SiU \
          ⋃ K ∈ F.map (geoStrictTransform π C) ++ [π ⁻¹' C],K) := by
  let lo := old.eraseIdx j.val
  have hLowerFull : IsSNCDivisor n (lo ++ born) := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  let S := Finset.univ.filter fun b : Fin born.length => x ∈ born.get b
  obtain ⟨hS,hFeasible⟩ := incident_selection_feasible hSj.1
    (fun K hK => hFull.1 _ (List.mem_append_right old hK))
      (oldMonomialPart Sj lo born) x hActive
  have hChosen := exists_prepared_mixed_selected_strict_trace_step hn hSj hLowerFull
    hSjTr hSjDense hLowerOrd hLowerPrepared hx.2 hActive S hS (Finset.Subset.refl S) hFeasible
  dsimp only at hChosen
  obtain ⟨U,hxU,Z,π,hStep⟩ := hChosen
  obtain ⟨hπ,_hOriginalC,hxC,_hC,hThin,hSmall,hLowerBad,_hRest⟩ := hStep
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let SiU := (Subtype.val : U → X) ⁻¹' (N ∩ H)
  let SjU := (Subtype.val : U → X) ⁻¹' Sj
  let eU : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
  let SU := S.map eU
  let C := SjU ∩ memberInter bornU SU
  change IsBlowupAlong n C π at hπ
  change (⟨x,hxU⟩ : U) ∈ C at hxC
  change interior C=∅ at hThin
  let F := oldU.eraseIdx i.val ++ bornU
  let iU : Fin oldU.length := ⟨i.val,by simpa only [oldU,List.length_map] using i.isLt⟩
  let jU : Fin oldU.length := ⟨j.val,by simpa only [oldU,List.length_map] using j.isLt⟩
  have hGetj : oldU.get jU=(Subtype.val : U → X) ⁻¹' old.get j := by
    simp [oldU,jU,List.get_eq_getElem]
  have hNU : IsClosedSubmanifold n NU := isClosedSubmanifold_preimage_val hN U
  have hFullU : IsSNCDivisor n (oldU ++ bornU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U) continuous_subtype_val hFull
  have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ K ∈ oldU ++ bornU,K) := by
    simpa only [List.map_append] using open_full_density hdense U
  have hSjTraceU : SjU=NU ∩ oldU.get jU := by
    rw [hGetj]
    change (Subtype.val : U → X) ⁻¹' Sj=(Subtype.val : U → X) ⁻¹' (N ∩ old.get j)
    rw [hSjTrace]
  have hCN : C ⊆ NU := inter_subset_left.trans (hSjTraceU ▸ inter_subset_left)
  have hOwn : C ⊆ oldU.get jU := inter_subset_left.trans (hSjTraceU ▸ inter_subset_right)
  have hSmallU : HasNormalCrossings n C (oldU.eraseIdx j.val ++ bornU) := by
    simpa only [oldU,lo,List.eraseIdx_map] using hSmall
  have hCNC : HasNormalCrossings n C (oldU ++ bornU) :=
    full_boundary_nc_of_lower (X := CMfd.of (n := n) U) hFullU jU hOwn hSmallU
  have hLowerBadU : C ⊆ originalSharpBadLocus (n := n) SjU
      (oldU.eraseIdx j.val ++ bornU) := by
    simpa only [oldU,lo,List.eraseIdx_map] using hLowerBad
  have hJOpen : oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU jU=
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born j) := by
    change nonmonomialPartAlong n NU
      (restrictOn n NU (vanishingIdeal (n := n) (oldU.get jU))) bornU=_
    rw [hGetj]
    exact (open_parts_pullback hn hN hFull hTr hdense U j).2
  have hcJ := (actual_old_parts_geometry hn hN hFull hTr hdense j).2.2.1
  have hSupportU : NU ∩ (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU jU).zeroLocus=SjU := by
    rw [hJOpen,BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hcJ]
    change (Subtype.val : U → X) ⁻¹' (N ∩ (oldResidualPart N old born j).zeroLocus)=_
    rw [←hSjSupport]
  have hUpperBad : C ⊆ originalSharpBadLocus (n := n) NU (oldU ++ bornU) := by
    have hb := originalSharpBadLocus_residual_subset (X := CMfd.of (n := n) U)
      hn hNU hFullU hTrU hDenseU jU
    rw [hSupportU] at hb
    exact hLowerBadU.trans hb
  let HU := (Subtype.val : U → X) ⁻¹' H
  have hFmap : (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)=F := by
    rw [List.map_append,←List.eraseIdx_map]
  have hAuxU : IsSNCDivisor n (HU :: F) := by
    simpa only [List.map_cons,hFmap] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U) continuous_subtype_val hAux
  have hAuxTrU : IsTransverse n NU (HU :: F) := by
    simpa only [List.map_cons,hFmap] using
      isTransverse_preimage (pullsBackCoordinates_val U) hAuxTr
  have hMemj : oldU.get jU ∈ F := by
    apply List.mem_append_left
    exact List.mem_eraseIdx_iff_getElem.mpr
      ⟨jU.val,jU.isLt,(fun he => hne (Fin.ext he)),rfl⟩
  obtain ⟨a,ha⟩ := List.mem_iff_get.mp hMemj
  let eb : Fin bornU.length ↪ Fin F.length :=
    ⟨fun b => ⟨(oldU.eraseIdx i.val).length+b.val,by
      simp only [F,List.length_append]
      omega⟩,
      fun a b he => Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))⟩
  have hGetBorn (b : Fin bornU.length) : F.get (eb b)=bornU.get b := by
    change (oldU.eraseIdx i.val ++ bornU).get
      ⟨(oldU.eraseIdx i.val).length+b.val,by
        simpa only [List.length_append,Nat.add_lt_add_iff_left] using b.isLt⟩=bornU.get b
    simp only [List.get_eq_getElem,List.getElem_append_right (by omega :
      (oldU.eraseIdx i.val).length ≤ (oldU.eraseIdx i.val).length+b.val),Nat.add_sub_cancel_left]
  let Q := insert a (SU.map eb)
  have hInter : memberInter F Q=oldU.get jU ∩ memberInter bornU SU := by
    ext y
    constructor
    · intro hy
      refine ⟨?_,?_⟩
      · rw [←ha]
        exact hy a (Finset.mem_insert_self _ _)
      · intro b hb
        rw [←hGetBorn b]
        exact hy (eb b) (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨b,hb,rfl⟩))
    · rintro ⟨hyj,hyB⟩ b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rw [ha]
        exact hyj
      · obtain ⟨c,hc,rfl⟩ := Finset.mem_map.mp hb
        rw [hGetBorn]
        exact hyB c hc
  have hCstratum : C=NU ∩ memberInter F Q := by
    change SjU ∩ memberInter bornU SU=_
    rw [hSjTraceU,hInter,inter_assoc]
  have hπ' : IsBlowupAlong n (NU ∩ memberInter F Q) π := by rw [←hCstratum];exact hπ
  have hProtect := stratum_slice_step (X := CMfd.of (n := n) U) (Y := Z)
    hn hNU hAuxU hAuxTrU Q hπ'
  have hSi : NU ∩ HU=SiU := rfl
  dsimp only at hProtect
  rw [←hCstratum,hSi] at hProtect
  have hCborn : HasNormalCrossings n C bornU :=
    hasNormalCrossings_of_forall_mem hCNC (fun K hK => List.mem_append_right oldU hK)
  have hCarrierTest : IsGeoTestTower (geometricTemplate NU bornU)
      (.step (.refl (X := CMfd.of (n := n) U)) C π hπ) := by
    refine ⟨trivial,hπ.1,?_,hCborn⟩
    change C ⊆ cosupport n NU (unitIdeal n U) 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem isCoherent_unitIdeal hg)]
    exact hCN
  have hAmbientTest : IsGeoTestTower (geometricTemplate (univ : Set U) (oldU ++ bornU))
      (.step (.refl (X := CMfd.of (n := n) U)) C π hπ) := by
    refine ⟨trivial,hπ.1,?_,hCNC⟩
    change C ⊆ cosupport n univ (unitIdeal n U) 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem isCoherent_unitIdeal hg)]
    exact subset_univ C
  refine ⟨U,Z,C,π,hπ,hxU,SU,?_,rfl,⟨⟨x,hxU⟩,hxC,rfl⟩,hThin,hCNC,
    hLowerBadU,hUpperBad,hCarrierTest,hAmbientTest,hProtect.1,hProtect.2.1,
    hProtect.2.2.1,hProtect.2.2.2⟩
  obtain ⟨b,hb⟩ := hS
  exact ⟨eU b,Finset.mem_map.mpr ⟨b,hb,rfl⟩⟩


private theorem nonunit_pullback {Z : CMfd.{u} n} {I : GermIdeal n X}
    (hI : I.IsCoherent) {f : Z → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    {z : Z} (hnot : ¬I.mem (f z) 1) : ¬(GermIdeal.pullback (m := n) f I).mem z 1 := by
  have hzI : f z ∈ I.zeroLocus := by
    intro g hg
    by_contra hne
    exact hnot (CompanionReduction.one_mem_of_apply_ne_zero hI hg hne)
  have hzPull : z ∈ (GermIdeal.pullback (m := n) f I).zeroLocus := by
    rw [BlowupExceptionalDivisor.zeroLocus_pullback hf hI]
    exact hzI
  exact fun hunit => one_ne_zero (hzPull 1 hunit)

private theorem open_residual_support (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (U : Opens X) (j : Fin old.length) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let jU : Fin oldU.length := ⟨j.val,by simpa only [oldU,List.length_map] using j.isLt⟩
    (Subtype.val : U → X) ⁻¹' (N ∩ (oldResidualPart N old born j).zeroLocus)=
      NU ∩ (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU jU).zeroLocus := by
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let jU : Fin oldU.length := ⟨j.val,by simpa only [oldU,List.length_map] using j.isLt⟩
  have hGet : oldU.get jU=(Subtype.val : U → X) ⁻¹' old.get j := by
    simp [oldU,jU,List.get_eq_getElem]
  have hJ : oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU jU=
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born j) := by
    change nonmonomialPartAlong n NU (restrictOn n NU (vanishingIdeal (n := n) (oldU.get jU))) bornU=_
    rw [hGet]
    exact (open_parts_pullback hn hN hE hTr hdense U j).2
  have hcJ := (actual_old_parts_geometry hn hN hE hTr hdense j).2.2.1
  change (Subtype.val : U → X) ⁻¹' (N ∩ (oldResidualPart N old born j).zeroLocus)=
    NU ∩ (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU jU).zeroLocus
  rw [hJ,BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hcJ]
  rfl

theorem exists_actual_local_other_row_monomial_protection (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i j : Fin E.length) (hne : j ≠ i) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    {x : Y}
    (hxi : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hxj : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)
    (hNonunit : let A := geoTransformAlong (geometricTemplate W []) T
      ¬(monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E).mem x 1) :
    ∃ (U₀ : Opens Y) (U₁ : Opens U₀) (U₂ : Opens U₁)
      (Z : CMfd.{u} n) (C : Set U₂) (π : Z → U₂) (hπ : IsBlowupAlong n C π),
      let f : U₂ → Y := fun a => a.val.val.val
      let A := geoTransformAlong (geometricTemplate W []) T
      let N := (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹'
        ((Subtype.val : U₀ → Y) ⁻¹' A.N))
      let old := (((E.map (strictAlong T)).map ((Subtype.val : U₀ → Y) ⁻¹' ·)).map
        ((Subtype.val : U₁ → U₀) ⁻¹' ·)).map ((Subtype.val : U₂ → U₁) ⁻¹' ·)
      let born := ((A.E.map ((Subtype.val : U₀ → Y) ⁻¹' ·)).map
        ((Subtype.val : U₁ → U₀) ⁻¹' ·)).map ((Subtype.val : U₂ → U₁) ⁻¹' ·)
      let Si := (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹'
        ((Subtype.val : U₀ → Y) ⁻¹' (A.N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)))
      let Sj := (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹'
        ((Subtype.val : U₀ → Y) ⁻¹' (A.N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus)))
      let F := old.eraseIdx i.val ++ born
      let M := MarkedIdeal.pullback (Subtype.val : U₂ → U₁)
        (MarkedIdeal.pullback (Subtype.val : U₁ → U₀)
          (MarkedIdeal.pullback (Subtype.val : U₀ → Y)
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T)))
      let R : BlowupTower (CMfd.of (n := n) U₂) Z := .step .refl C π hπ
      ∃ S : Finset (Fin born.length),S.Nonempty ∧
        C=Sj ∩ memberInter born S ∧ (∃ c ∈ C,f c=x) ∧ interior C=∅ ∧
        HasNormalCrossings n C (old ++ born) ∧
        C ⊆ originalSharpBadLocus (n := n) Sj (old.eraseIdx j.val ++ born) ∧
        C ⊆ originalSharpBadLocus (n := n) N (old ++ born) ∧
        IsGeoTestTower (geometricTemplate N born) R ∧
        IsGeoTestTower (geometricTemplate (univ : Set U₂) (old ++ born)) R ∧
        M.N=N ∧ M.E=born ∧ M.d=0 ∧
        IsClosedSubmanifold n (geoStrictTransform π C Si) ∧
        (chronologicalMarked M R).ideal=vanishingIdeal (n := n) (geoStrictTransform π C Si) ∧
        HasNormalCrossings n (geoStrictTransform π C Si)
          (F.map (geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
        geoStrictTransform π C Si ⊆ closure (geoStrictTransform π C Si \
          ⋃ H ∈ F.map (geoStrictTransform π C) ++ [π ⁻¹' C],H) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let born := A.E
  let J := fun h : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  let Sj := A.N ∩ (J j).zeroLocus
  let Di := monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) born
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hN : IsClosedSubmanifold n A.N := hRecorded.1
  have hFullCurrent : IsSNCDivisor n (old ++ born) := hRecorded.2.1
  have hTrCurrent : IsTransverse n A.N born := hRecorded.2.2.1
  have hDenseCurrent : A.N ⊆ closure (A.N \ ⋃ H ∈ old ++ born,H) := hRecorded.2.2.2.1
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N=A.N at hNj
  have hxiA : x ∈ Si := by simpa only [hNi] using hxi
  have hxjA : x ∈ Sj := by simpa only [hNj] using hxj
  have hOrdA : ∀ y ∈ A.N,ordinaryTraceOrder A.N (J i) y ≤ 1 := by simpa only [hNi] using hOrd
  have hProtect := actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull
    hOrdA hNC hDenseS
  have hSi : IsClosedSubmanifold n Si := hProtect.1
  have hWholeSi : J i=vanishingIdeal (n := n) Si := hProtect.2.1
  have hLower := actual_original_lower_prepared_neighborhood hn hW hE hdense i T hT hFull
    hOrd hNC hDenseS j hne hxi hxj
  obtain ⟨U₀,hx₀,hLN,hLE,hLT,hLD,hLRows,hLP⟩ := hLower
  let N₀ := (Subtype.val : U₀ → Y) ⁻¹' A.N
  let old₀ := old.map ((Subtype.val : U₀ → Y) ⁻¹' ·)
  let born₀ := born.map ((Subtype.val : U₀ → Y) ⁻¹' ·)
  let L₀ := (Subtype.val : U₀ → Y) ⁻¹' Sj
  let lo₀ := (old.eraseIdx j.val).map ((Subtype.val : U₀ → Y) ⁻¹' ·)
  change IsClosedSubmanifold n L₀ at hLN
  change IsSNCDivisor n (lo₀ ++ born₀) at hLE
  change IsTransverse n L₀ born₀ at hLT
  change L₀ ⊆ closure (L₀ \ ⋃ H ∈ lo₀ ++ born₀,H) at hLD
  change ∀ y ∈ L₀,(∀ a,ordinaryTraceOrder L₀ (oldResidualPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a) y ≤ 1) ∧
    IsPreparedResidualSNCAt (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ y at hLP
  obtain ⟨V,hxV,hVU₀,H,hAux,hAuxTr,hSiV,hJiV,hOtherV⟩ :=
    protected_slice_window hn hW hE hdense i T hT hFull hOrd hNC hDenseS hxi U₀ hx₀
  let U₁ := innerOpen U₀ V
  let e := innerOpenEquiv U₀ V hVU₀
  let x₁ : U₁ := ⟨⟨x,hx₀⟩,hxV⟩
  let N₁ := (Subtype.val : U₁ → U₀) ⁻¹' N₀
  let old₁ := old₀.map ((Subtype.val : U₁ → U₀) ⁻¹' ·)
  let born₁ := born₀.map ((Subtype.val : U₁ → U₀) ⁻¹' ·)
  let L₁ := (Subtype.val : U₁ → U₀) ⁻¹' L₀
  let lo₁ := lo₀.map ((Subtype.val : U₁ → U₀) ⁻¹' ·)
  let Si₁ := (Subtype.val : U₁ → U₀) ⁻¹' ((Subtype.val : U₀ → Y) ⁻¹' Si)
  let H₁ := e ⁻¹' H
  let i₁ : Fin old₁.length := ⟨i.val,by simpa only [old₁,old₀,old,List.length_map] using i.isLt⟩
  let j₁ : Fin old₁.length := ⟨j.val,by simpa only [old₁,old₀,old,List.length_map] using j.isLt⟩
  have hne₁ : j₁ ≠ i₁ := by
    intro he
    have hv : j₁.val=i₁.val := congrArg (fun a : Fin old₁.length => a.val) he
    exact hne (Fin.ext hv)
  have hLo₁ : lo₁=old₁.eraseIdx j.val := by
    simp only [lo₁,lo₀,old₁,old₀,List.eraseIdx_map]
  have hN₀ : IsClosedSubmanifold n N₀ := isClosedSubmanifold_preimage_val hN U₀
  have hFull₀ : IsSNCDivisor n (old₀ ++ born₀) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₀) continuous_subtype_val hFullCurrent
  have hTr₀ : IsTransverse n N₀ born₀ := isTransverse_preimage (pullsBackCoordinates_val U₀) hTrCurrent
  have hDense₀ : N₀ ⊆ closure (N₀ \ ⋃ H ∈ old₀ ++ born₀,H) := by
    simpa only [List.map_append] using open_full_density hDenseCurrent U₀
  have hN₁ : IsClosedSubmanifold n N₁ := isClosedSubmanifold_preimage_val hN₀ U₁
  have hFull₁ : IsSNCDivisor n (old₁ ++ born₁) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₁) continuous_subtype_val hFull₀
  have hTr₁ : IsTransverse n N₁ born₁ := isTransverse_preimage (pullsBackCoordinates_val U₁) hTr₀
  have hDense₁ : N₁ ⊆ closure (N₁ \ ⋃ H ∈ old₁ ++ born₁,H) := by
    simpa only [List.map_append] using open_full_density (X := CMfd.of (n := n) U₀) hDense₀ U₁
  have hFpull : ((old.eraseIdx i.val ++ born).map ((Subtype.val : V → Y) ⁻¹' ·)).map
      (e ⁻¹' ·)=old₁.eraseIdx i.val ++ born₁ := by
    dsimp only [old₁,old₀,born₁,born₀]
    simp only [List.map_append,List.eraseIdx_map,List.map_map]
    rfl
  have hAux₁ : IsSNCDivisor n (H₁ :: (old₁.eraseIdx i.val ++ born₁)) := by
    have hh := isSNCDivisor_map_preimage (pullsBackCoordinates e) e.continuous hAux
    change IsSNCDivisor n ((H :: (old.eraseIdx i.val ++ born).map
      ((Subtype.val : V → Y) ⁻¹' ·)).map (e ⁻¹' ·)) at hh
    rw [List.map_cons,hFpull] at hh
    exact hh
  have hAuxTr₁ : IsTransverse n N₁ (H₁ :: (old₁.eraseIdx i.val ++ born₁)) := by
    have hh := isTransverse_preimage (pullsBackCoordinates e) hAuxTr
    change IsTransverse n N₁ ((H :: (old.eraseIdx i.val ++ born).map
      ((Subtype.val : V → Y) ⁻¹' ·)).map (e ⁻¹' ·)) at hh
    rw [List.map_cons,hFpull] at hh
    exact hh
  have hSi₁ : Si₁=N₁ ∩ H₁ := by
    have hh := congrArg (fun S : Set V => e ⁻¹' S) hSiV
    exact hh
  have hGetj₁ : old₁.get j₁=(Subtype.val : U₁ → U₀) ⁻¹'
      ((Subtype.val : U₀ → Y) ⁻¹' strictAlong T (E.get j)) := by
    simp [old₁,old₀,old,j₁,List.get_eq_getElem]
  have hSjTrace₁ : L₁=N₁ ∩ old₁.get j₁ := by
    rw [hGetj₁]
    exact congrArg (fun S : Set V => e ⁻¹' S) (hOtherV j hne).2
  let jOld : Fin old.length := ⟨j.val,by simpa only [old,List.length_map] using j.isLt⟩
  let j₀ : Fin old₀.length := ⟨j.val,by simpa only [old₀,old,List.length_map] using j.isLt⟩
  have hGetj : old.get jOld=strictAlong T (E.get j) := by simp [old,jOld,List.get_eq_getElem]
  have hJj : oldResidualPart A.N old born jOld=J j := by
    change nonmonomialPartAlong n A.N (restrictOn n A.N (vanishingIdeal (n := n) (old.get jOld))) born=_
    rw [hGetj]
    exact (hRecorded.2.2.2.2 j).2.2.1
  have hSupport₀ := open_residual_support hn hN hFullCurrent hTrCurrent hDenseCurrent U₀ jOld
  change (Subtype.val : U₀ → Y) ⁻¹' (A.N ∩ (oldResidualPart A.N old born jOld).zeroLocus)=
    N₀ ∩ (oldResidualPart (X := CMfd.of (n := n) U₀) N₀ old₀ born₀ j₀).zeroLocus at hSupport₀
  rw [hJj] at hSupport₀
  have hSupport₁ := open_residual_support (X := CMfd.of (n := n) U₀) hn hN₀ hFull₀ hTr₀ hDense₀ U₁ j₀
  change (Subtype.val : U₁ → U₀) ⁻¹' (N₀ ∩ (oldResidualPart (X := CMfd.of (n := n) U₀) N₀ old₀ born₀ j₀).zeroLocus)=
    N₁ ∩ (oldResidualPart (X := CMfd.of (n := n) U₁) N₁ old₁ born₁ j₁).zeroLocus at hSupport₁
  rw [←hSupport₀] at hSupport₁
  have hLN₁ : IsClosedSubmanifold n L₁ := isClosedSubmanifold_preimage_val hLN U₁
  have hLE₁ : IsSNCDivisor n (lo₁ ++ born₁) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val U₁) continuous_subtype_val hLE
  have hLT₁ : IsTransverse n L₁ born₁ := isTransverse_preimage (pullsBackCoordinates_val U₁) hLT
  have hLD₁ : L₁ ⊆ closure (L₁ \ ⋃ H ∈ lo₁ ++ born₁,H) := by
    simpa only [List.map_append] using open_full_density (X := CMfd.of (n := n) U₀) hLD U₁
  have hLowerOpen := current_prepared_open (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD
    (fun y hy => (hLP y hy).1) (fun y hy => (hLP y hy).2) U₁
  change (∀ y ∈ L₁,∀ a,ordinaryTraceOrder L₁ (oldResidualPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a) y ≤ 1) ∧
    (∀ y ∈ L₁,IsPreparedResidualSNCAt (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ y) at hLowerOpen
  obtain ⟨a₀,_ha₀,hRowI⟩ := hLRows i (Ne.symm hne)
  rw [if_pos rfl] at hRowI
  have hD₀ : oldMonomialPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a₀=
      restrictOn n L₀ (GermIdeal.pullback (m := n) (Subtype.val : U₀ → Y) Di) := hRowI.1
  have hBornCurrent : IsSNCDivisor n born := isSNCDivisor_of_sublist hFullCurrent (List.sublist_append_right old born)
  have hIRow := hRecorded.2.2.2.2 i
  have hcDi : Di.IsCoherent := isCoherent_monomialPartAlong hn hN hBornCurrent hTrCurrent hIRow.1 hIRow.2.1
  have hD₀not : ¬(oldMonomialPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a₀).mem (⟨x,hx₀⟩ : U₀) 1 := by
    rw [hD₀]
    exact nonunit_pullback_restrict (Z := CMfd.of (n := n) U₀) hcDi contMDiff_subtype_val hxjA hNonunit
  let a₁ : Fin lo₁.length := ⟨a₀.val,by simpa only [lo₁,lo₀,List.length_map] using a₀.isLt⟩
  have hGeta : lo₁.get a₁=(Subtype.val : U₁ → U₀) ⁻¹' lo₀.get a₀ := by simp [lo₁,a₁,List.get_eq_getElem]
  have hD₁ : oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a₁=
      GermIdeal.pullback (m := n) (Subtype.val : U₁ → U₀) (oldMonomialPart (X := CMfd.of (n := n) U₀) L₀ lo₀ born₀ a₀) := by
    change monomialPartAlong n L₁ (restrictOn n L₁ (vanishingIdeal (n := n) (lo₁.get a₁))) born₁=_
    rw [hGeta]
    exact (open_parts_pullback (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD U₁ a₀).1
  obtain ⟨_hcI₀,_hnzI₀,_hcJ₀,_hnzJ₀,hcD₀,_hnzD₀,_hmD₀,_hw₀⟩ :=
    actual_old_parts_geometry (X := CMfd.of (n := n) U₀) hn hLN hLE hLT hLD a₀
  have hD₁not : ¬(oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a₁).mem x₁ 1 := by
    rw [hD₁]
    exact nonunit_pullback (X := CMfd.of (n := n) U₀) (Z := CMfd.of (n := n) U₁) hcD₀ contMDiff_subtype_val hD₀not
  have hxL₁ : x₁ ∈ L₁ := hxjA
  have hActiveLo : (properRows (fun (a : Fin lo₁.length) (b : Fin born₁.length) =>
      divExpAlong n L₁ (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a) (born₁.get b) x₁)).Nonempty := by
    refine ⟨a₁,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    by_contra hnot
    have hsum : (∑ b,divExpAlong n L₁ (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a₁) (born₁.get b) x₁)=0 := by
      exact Nat.eq_zero_of_not_pos hnot
    have hzero (b : Fin born₁.length) : divExpAlong n L₁ (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a₁) (born₁.get b) x₁=0 := by
      have hh := Finset.single_le_sum (fun b (_hb : b ∈ (Finset.univ : Finset (Fin born₁.length))) =>
        Nat.zero_le (divExpAlong n L₁ (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ lo₁ born₁ a₁) (born₁.get b) x₁)) (Finset.mem_univ b)
      rw [hsum] at hh
      exact Nat.eq_zero_of_le_zero hh
    obtain ⟨_hcI₁,_hnzI₁,_hcJ₁,_hnzJ₁,hcD₁,hnzD₁,hmD₁,_hw₁⟩ :=
      actual_old_parts_geometry (X := CMfd.of (n := n) U₁) hn hLN₁ hLE₁ hLT₁ hLD₁ a₁
    exact hD₁not (HironakaG4CanonicalZeroRowUnit.one_mem_of_zero_canonical_row (X := CMfd.of (n := n) U₁) hn hLN₁
      (isSNCDivisor_of_sublist hLE₁ (List.sublist_append_right lo₁ born₁)) hLT₁ hcD₁ hnzD₁ hmD₁ hxL₁ hzero)
  have hActive : (properRows (fun (a : Fin (old₁.eraseIdx j₁.val).length) (b : Fin born₁.length) =>
      divExpAlong n L₁ (oldMonomialPart (X := CMfd.of (n := n) U₁) L₁ (old₁.eraseIdx j₁.val) born₁ a) (born₁.get b) x₁)).Nonempty := by
    rw [hLo₁] at hActiveLo
    exact hActiveLo
  rw [hLo₁] at hLD₁ hLowerOpen
  have hCore := choose_local_protected_monomial_step (X := CMfd.of (n := n) U₁) hn hN₁ hFull₁ hTr₁ hDense₁ i₁ j₁ hne₁
    hAux₁ hAuxTr₁ hLN₁ hSjTrace₁ hSupport₁ hLT₁
    hLD₁ hLowerOpen.1 hLowerOpen.2
    (show x₁ ∈ (N₁ ∩ H₁) ∩ L₁ from ⟨hSi₁ ▸ hxiA,hxL₁⟩) hActive
  dsimp only at hCore
  rw [←hSi₁] at hCore
  obtain ⟨U₂,Z,C,π,hπ,hx₂,S,hS,hCeq,hPoint,hThin,hCNC,hLowerBad,hUpperBad,
    hCarrierTest,hAmbientTest,hSmooth,hStrict,hNewNC,hNewDense⟩ := hCore
  let M₀ := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let M := MarkedIdeal.pullback (Subtype.val : U₂ → U₁)
    (MarkedIdeal.pullback (Subtype.val : U₁ → U₀) (MarkedIdeal.pullback (Subtype.val : U₀ → Y) M₀))
  have hMN : M.N=(Subtype.val : U₂ → U₁) ⁻¹' N₁ := by
    change (Subtype.val : U₂ → U₁) ⁻¹' ((Subtype.val : U₁ → U₀) ⁻¹' ((Subtype.val : U₀ → Y) ⁻¹' M₀.N))=_
    rw [hNi]
  have hME : M.E=born₁.map ((Subtype.val : U₂ → U₁) ⁻¹' ·) := by
    have hEi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).2
    change M₀.E=born at hEi
    change ((M₀.E.map ((Subtype.val : U₀ → Y) ⁻¹' ·)).map ((Subtype.val : U₁ → U₀) ⁻¹' ·)).map
      ((Subtype.val : U₂ → U₁) ⁻¹' ·)=_
    rw [hEi]
  have hMD : M.d=0 := chronologicalMarked_zero_mark (originalRelativeMemberMarked W (E.get i)) rfl T
  have hSi₀ : IsClosedSubmanifold n ((Subtype.val : U₀ → Y) ⁻¹' Si) := isClosedSubmanifold_preimage_val hSi U₀
  have hSi₁smooth : IsClosedSubmanifold n Si₁ := isClosedSubmanifold_preimage_val hSi₀ U₁
  have hMI : M.ideal=vanishingIdeal (n := n) ((Subtype.val : U₂ → U₁) ⁻¹' Si₁) := by
    change GermIdeal.pullback (m := n) (Subtype.val : U₂ → U₁)
      (GermIdeal.pullback (m := n) (Subtype.val : U₁ → U₀)
        (GermIdeal.pullback (m := n) (Subtype.val : U₀ → Y) (J i)))=_
    rw [hWholeSi,actual_vanishingIdeal_open Si hSi U₀,
      actual_vanishingIdeal_open (X := CMfd.of (n := n) U₀) _ hSi₀ U₁,
      actual_vanishingIdeal_open (X := CMfd.of (n := n) U₁) _ hSi₁smooth U₂]
  refine ⟨U₀,U₁,U₂,Z,C,π,hπ,?_⟩
  dsimp only
  refine ⟨S,hS,hCeq,?_,hThin,hCNC,hLowerBad,hUpperBad,hCarrierTest,hAmbientTest,
    hMN,hME,hMD,hSmooth,?_,hNewNC,hNewDense⟩
  · obtain ⟨c,hc,he⟩ := hPoint
    exact ⟨c,hc,congrArg (fun a : U₁ => a.val.val) he⟩
  · change nextRelativeStrict (X := CMfd.of (n := n) U₂) (Y := Z) M.N M.ideal C π=_
    rw [hMN,hMI]
    exact hStrict


end
end Hironaka.HironakaActualProtectedOtherRowLocalStep
