import Hironaka.Resolution.HironakaOriginalNCAllPrefixPhaseLex

set_option autoImplicit false

/-!
# The SAME remainder phase has a real zero append and permitted count reset

The natural producer internally chooses its actual canonical resolving A-phase.
The exact current highest locus identifies its deferred selected-zero union.
When nonempty, this is the whole parent-cosupport phase-lex maximum. When empty,
its actual blowup is an empty step; no false empty whole-maximum claim is made.
The same actual append resolves L and carries every original branch history.
The old-count reset is on the explicit complement of strict Z, which contains
the entire current original cosupport. It is not asserted outside that open.

Blueprint: hironaka-original-nc-zero-priority-reset-extension.tex.
Source-only proof-body draft; no kernel-check or original NC-driver claim.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.HironakaOriginalNCZeroPriority

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  CoefficientRestrictionTower HomogenizedGlueingTower MemberInterTowerAlong
  HironakaStepOneSpecialAnalyticLoci HironakaStepOneMemberLowerExtension
  HironakaDimensionTwoStepOneAnalyticSuperlevels HironakaStepOneZeroContactRemainderExtension
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaBoundaryCoefficientStratumResolution
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCPhaseLex
  HironakaOriginalNCAllPrefixPhaseLex
open ResolutionDriver (maxLocus IsCanonicalSegment)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem maxLocus_remainderPhaseLex_of_cleared_remainder
    {D : Type u} {Λ : Type v} [LinearOrder Λ]
    (S R : Set D) (b : D → ℕ) (f : D → Λ) {r : ℕ}
    (hBound : ∀ x, b x ≤ r) (hClear : S ∩ R = ∅)
    (hNe : {x ∈ S | r ≤ b x}.Nonempty) :
    maxLocus (remainderPhaseLex b R f) S = {x ∈ S | r ≤ b x} := by
  classical
  have hOff : ∀ x ∈ S, x ∉ R := by
    intro x hx hxR
    have hh : x ∈ S ∩ R := ⟨hx, hxR⟩
    rw [hClear] at hh
    exact hh
  obtain ⟨z, hzS, hzTop⟩ := hNe
  have hzCount : b z = r := le_antisymm (hBound z) hzTop
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hCmp := hx.2 z hzS
    rw [remainderPhaseLex, remainderPhaseLex, if_neg (hOff z hzS),
      if_neg (hOff x hx.1), hzCount, Prod.Lex.toLex_le_toLex] at hCmp
    rcases hCmp with hLt | ⟨hEq, _⟩
    · exact hLt.le
    · exact hEq.le
  · rintro ⟨hxS, hxTop⟩
    have hxCount : b x = r := le_antisymm (hBound x) hxTop
    refine ⟨hxS, ?_⟩
    intro y hyS
    rw [remainderPhaseLex, remainderPhaseLex, if_neg (hOff y hyS),
      if_neg (hOff x hxS), hxCount, Prod.Lex.toLex_le_toLex]
    rcases (hBound y).lt_or_eq with hyLt | hyEq
    · exact Or.inl hyLt
    · exact Or.inr ⟨hyEq, le_rfl⟩

/-- At the end of a SAME actual resolving A-phase, every current count,
parent test history and exact selected-zero level is derived internally.
The natural producer below supplies P and its actual A-resolution itself. -/
theorem remainder_end_zero_level
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (P : BlowupTower X Y)
    (hRes : IsGeoResolution
      (contactRemainderMarked (withN (coeffMarked (⟨univ, E, I, d⟩ : MarkedIdeal n X))
        {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) 0) P) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    let R := A.N
    let C := strictAlong P (selectedComponents (n := n) L.N L.cosupp)
    IsGeoTestTower L P ∧ IsGeoTestTower M P ∧ CentresIn Z P ∧ CentresIn R P ∧
      IsClosedSubmanifold n C ∧ IsTransverse n C (geoTransformAlong L P).E ∧
      C ⊆ (geoTransformAlong L P).cosupp ∧
      (geoTransformAlong L P).N = strictAlong P R ∪ C ∧
      Disjoint (strictAlong P R) C ∧
      (geoTransformAlong L P).cosupp ∩ strictAlong P R = ∅ ∧
      (geoTransformAlong M P).cosupp ∩ strictAlong P Z = C ∧
      (geoTransformAlong M P).cosupp ∩ strictAlong P R = ∅ ∧
      ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong P H) (geoTransformAlong M P).E,
        (∀ y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y ≤ r) ∧
        {y | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} =
          strictAlong P Z ∧
        {y ∈ (geoTransformAlong M P).cosupp |
          r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} = C ∧
        (C.Nonempty → C = maxLocus
          (remainderPhaseLex (branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc))
            (strictAlong P R) ((CanonicalCentres.canonicalInvariant n).inv A P))
          (geoTransformAlong M P).cosupp) := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  let R := A.N
  let C := strictAlong P (selectedComponents (n := n) L.N L.cosupp)
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hLI : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪 := M) rfl hI
  have hLW : L.IsWellFormed :=
    ⟨hZ, hLI, isSNCDivisor_of_boundaryAdapted h, highest_stratum_isTransverse h hBound⟩
  obtain ⟨hLP, hMP, hPZ, hLCos, hACos⟩ :=
    original_remainder_cosupport_dictionary I hI d hd h hBound P hRes.1
  have hPR : CentresIn R P := centresIn_of_isGeoTestTower_withN A A.N P hRes.1
  obtain ⟨hC, hCE, hCcos, hPart, hDis⟩ :=
    HironakaNormalCrossingsCoefficientStratumResolution.selected_strict_geometry L hLW P hLP hPR
  have hMClear : (geoTransformAlong M P).cosupp ∩ strictAlong P R = ∅ :=
    hACos.symm.trans hRes.2
  have hLClear : (geoTransformAlong L P).cosupp ∩ strictAlong P R = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyL, hyR⟩
    have hyM := (hLCos ▸ hyL).1
    have hh : y ∈ (geoTransformAlong M P).cosupp ∩ strictAlong P R := ⟨hyM, hyR⟩
    rw [hMClear] at hh
    exact hh
  have hHigh : (geoTransformAlong M P).cosupp ∩ strictAlong P Z = C := by
    rw [← hLCos]
    apply le_antisymm
    · intro y hyL
      have hyPart : y ∈ strictAlong P R ∪ C :=
        hPart ▸ (geoTransformAlong L P).cosupp_subset_N hyL
      rcases hyPart with hyR | hyC
      · have hh : y ∈ (geoTransformAlong L P).cosupp ∩ strictAlong P R := ⟨hyL, hyR⟩
        rw [hLClear] at hh
        exact False.elim hh
      · exact hyC
    · exact hCcos
  obtain ⟨hc, hCurrentBound, _hCurrentTop, hCurrentHigh⟩ :=
    exists_highest_history_current_pair_high_locus I hI d h hr hBound P hMP hPZ
  have hTop : {y ∈ (geoTransformAlong M P).cosupp |
      r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} = C := by
    change (geoTransformAlong M P).cosupp ∩
      {y | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y} = C
    rw [hCurrentHigh]
    exact hHigh
  refine ⟨hLP, hMP, hPZ, hPR, hC, hCE, hCcos, hPart, hDis, hLClear, hHigh,
    hMClear, hc, hCurrentBound, hCurrentHigh, hTop, ?_⟩
  intro hNe
  have hTopNe : {y ∈ (geoTransformAlong M P).cosupp |
      r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y}.Nonempty := by
    rw [hTop]
    exact hNe
  exact hTop.symm.trans (maxLocus_remainderPhaseLex_of_cleared_remainder
    (geoTransformAlong M P).cosupp (strictAlong P R)
    (branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc))
    ((CanonicalCentres.canonicalInvariant n).inv A P) hCurrentBound hMClear hTopNe).symm

-- The fixed public result names its SNC/union and existential current-pair
-- witnesses although later fields need only their types. Preserve that result.
set_option linter.unusedVariables false in
/-- Natural original data internally select the SAME complete canonical A-phase,
its real selected-zero blowup, every original literal branch-prefix history and
the exact whole-cosupport open on which the old count resets to at most r-1.
There is no caller phase, history, empty-A, maximum or current-count certificate. -/
theorem exists_original_remainder_zero_append_permitted_reset
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1 ≤ d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0 < r)
    (hBound : ∀ x : X,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
    let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    let V := CanonicalCentres.canonicalInvariant n
    ∃ (Y : CMfd.{u} n) (P : BlowupTower X Y),
      IsCanonicalSegment A (V.inv A) P ∧ IsGeoResolution A P ∧
      ∃ (Y' : CMfd.{u} n) (π : Y' → Y)
        (hπ : IsBlowupAlong n (strictAlong P (selectedComponents (n := n) L.N L.cosupp)) π),
        let C := strictAlong P (selectedComponents (n := n) L.N L.cosupp)
        let T : BlowupTower X Y' := .step P C π hπ
        IsGeoResolution L T ∧ IsGeoTestTower M T ∧ IsOriginalBranchTestTower M H T ∧
        (∀ (W : Opens X) (B : List (Set W))
          (hSNC : IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : W → X) M).E))
          (hUnion : (Subtype.val : W → X) ⁻¹' H = (⋃ D ∈ B, D)),
          let MW := MarkedIdeal.pullback (Subtype.val : W → X) M
          let MB : MarkedIdeal n W := { MW with E := B ++ MW.E }
          ∀ j : ℕ, IsGeoTestTower MB (head (restrict W T) j) ∧
            (geoTransformAlong MB (head (restrict W T) j)).IsWellFormed ∧
            (geoTransformAlong MB (head (restrict W T) j)).E =
              B.map (strictAlong (head (restrict W T) j)) ++
                (geoTransformAlong MW (head (restrict W T) j)).E) ∧
        ∃ hcP : IsBoundaryAdaptedCarrier (n := n) (strictAlong P H) (geoTransformAlong M P).E,
          {y ∈ (geoTransformAlong M P).cosupp |
            r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcP) y} = C ∧
          (C.Nonempty → C = maxLocus
            (remainderPhaseLex (branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcP))
              (strictAlong P A.N) (V.inv A P)) (geoTransformAlong M P).cosupp) ∧
          ∃ (hcT : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E)
            (U : Opens Y'),
            (U : Set Y') = (strictAlong T Z)ᶜ ∧ (geoTransformAlong M T).cosupp ⊆ U ∧
            ∃ hcU : IsBoundaryAdaptedCarrier (n := n)
              ((Subtype.val : U → Y') ⁻¹' strictAlong T H)
              ((geoTransformAlong M T).E.map (fun D => (Subtype.val : U → Y') ⁻¹' D)),
              ∀ y : U, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcU) y ≤ r - 1 := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ, E, I, d⟩
  let Z := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let L := withN (coeffMarked M) Z
  let A := contactRemainderMarked L 0
  obtain ⟨Y, P, hCan, hRes, _hMP, _hHistoryP, _hPrefixes⟩ :=
    exists_original_canonical_remainder_all_prefix_phase_lex I hI d hd hK h hr hBound
  let R := A.N
  let C := strictAlong P (selectedComponents (n := n) L.N L.cosupp)
  obtain ⟨hLP, _hMP', _hPZ, _hPR, hC, hCE, hCcos, hPart, hDis, hLClear,
      _hHigh, _hMClear, hcP, _hPBound, _hPHigh, hTop, hMax⟩ :=
    remainder_end_zero_level I hI d hd h hr hBound P hRes
  have hZ := isClosedSubmanifold_highest_superlevel
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound
  have hLI : L.ideal.IsCoherent := isCoherent_coeffMarked (𝔪 := M) rfl hI
  have hLW : L.IsWellFormed :=
    ⟨hZ, hLI, isSNCDivisor_of_boundaryAdapted h, highest_stratum_isTransverse h hBound⟩
  have hwP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hLW P hLP
  have hCP : C ⊆ (geoTransformAlong L P).N :=
    fun _ hx => (geoTransformAlong L P).cosupp_subset_N (hCcos hx)
  have hDim : ResolutionInvariantSpec.DimLE n L.N (n - r) := fun _ hx =>
    ⟨n - r, le_rfl, regularAtDim_highest_superlevel
      (isNormalCrossingsCarrier_of_boundaryAdapted h) hBound hx⟩
  have hDimP := InvDomainTowerAlong.dimLE_geoTransformAlong hZ hLI hDim P hLP
  have hInt : interior C = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyN := hCP (interior_subset hy)
    have hyZ : y ∈ strictAlong P Z := (N_geoTransformAlong L P) ▸ hyN
    have hyInitial := strictAlong_subset_preimage P hZ.1 hyZ
    have hrn : r ≤ n := hyInitial.trans
      (branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) (P.proj y))
    have hyn : RegularAtDim (n := n) C y n :=
      EmbeddedFromResolution.regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
    obtain ⟨j, hj, hreg⟩ := hDimP y hyN
    have hnle := BlowupStrictSubmanifold.le_of_regularAtDim_subset hyn hreg hCP
    omega
  obtain ⟨Y', tY', cY', mY', π, hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hInt
  let Yf : CMfd.{u} n :=
    { carrier := Y', topologicalSpace := tY', chartedSpace := cY', isComplexManifold := mY' }
  let T : BlowupTower X Yf := .step P C π hπ
  have hTL : IsGeoTestTower L T := ⟨hLP, hC, hCcos, hCE.hasNormalCrossings⟩
  have hResL : IsGeoResolution L T := by
    refine ⟨hTL, eq_empty_iff_forall_notMem.mpr ?_⟩
    intro z hz
    have hNZ : (geoTransformAlong L T).N =
        BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong P R) := by
      change BlowupStrictSubmanifold.geoStrictTransform π C (geoTransformAlong L P).N = _
      have hPart' : (geoTransformAlong L P).N = strictAlong P R ∪ C := hPart
      rw [hPart']
      simp only [BlowupStrictSubmanifold.geoStrictTransform, union_sdiff_distrib,
        sdiff_self, union_empty]
    have hzR : π z ∈ strictAlong P R :=
      BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous
        (isClosed_strictAlong P (isClosedSubmanifold_remainingComponents hZ L.cosupp).1)
        (hNZ ▸ (geoTransformAlong L T).cosupp_subset_N hz)
    have hzC : π z ∉ C := fun hc => Set.disjoint_left.mp hDis hzR hc
    have hzL : π z ∈ (geoTransformAlong L P).cosupp :=
      TransformOffCentre.mem_cosupp_of_mem_cosupp_geoTransform (geoTransformAlong L P)
        hwP.isClosedSubmanifold_N.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwP.isCoherent hg)
        hπ hzC hz
    have hh : π z ∈ (geoTransformAlong L P).cosupp ∩ strictAlong P R := ⟨hzL, hzR⟩
    rw [hLClear] at hh
    exact hh
  obtain ⟨hMT, hTZ⟩ := (coeff_restrict_tower_iff M rfl hI hd hZ T).1.mp hTL
  have hCosT := (coeff_restrict_tower_iff M rfl hI hd hZ T).2 hTL
  have hClearT : (geoTransformAlong M T).cosupp ∩ strictAlong T Z = ∅ :=
    hCosT.symm.trans hResL.2
  have hHistory := isOriginalBranchTestTower_of_centresIn_highest_stratum
    I hI d h hr hBound T hMT hTZ
  obtain ⟨hcT, _hTBound, _hTTop, hTHigh⟩ :=
    exists_highest_history_current_pair_high_locus I hI d h hr hBound T hMT hTZ
  let U : Opens Yf := ⟨(strictAlong T Z)ᶜ, (isClosed_strictAlong T hZ.1).isOpen_compl⟩
  have hCover : (geoTransformAlong M T).cosupp ⊆ U := by
    intro y hy hyZ
    have hh : y ∈ (geoTransformAlong M T).cosupp ∩ strictAlong T Z := ⟨hy, hyZ⟩
    rw [hClearT] at hh
    exact hh
  have hcU := boundaryAdapted_open U hcT
  have hReset : ∀ y : U,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcU) y ≤ r - 1 := by
    intro y
    have hLt : branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hcT) y.val < r := by
      apply lt_of_not_ge
      intro hyTop
      have hyZ : y.val ∈ strictAlong T Z := hTHigh ▸ hyTop
      exact y.property hyZ
    have he := branchMultiplicity_open U (isNormalCrossingsCarrier_of_boundaryAdapted hcT)
      (isNormalCrossingsCarrier_of_boundaryAdapted hcU) y
    omega
  refine ⟨Y, P, hCan, hRes, Yf, π, hπ, hResL, hMT, hHistory, ?_,
    hcP, hTop, hMax, hcT, U, rfl, hCover, hcU, hReset⟩
  intro W B hSNC hUnion
  exact original_branch_prefix_histories M rfl hI T hHistory W B hSNC hUnion

end
end Hironaka.HironakaOriginalNCZeroPriority
