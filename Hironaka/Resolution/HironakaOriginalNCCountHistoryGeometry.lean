import Hironaka.Resolution.HironakaOriginalOldBranchAppend
import Hironaka.Resolution.HironakaNormalCrossingsGlobalPhaseCarrier
import Hironaka.Resolution.HironakaNormalCrossingsJointBranchCharts
import Hironaka.Blowup.BlowupTowerSplitIso

set_option autoImplicit false

/-! Actual old-count geometry for ANY compatible original branch-test history.
No selected output resolution, count certificate or centre maximum is read.
The general chart is obtained from the existing highest chart on a genuine
open on which the original point has locally maximal intrinsic old count.
Blueprint: hironaka-original-nc-count-birth-history-extension.tex.
Source-only proof-body draft, with no kernel-check claim. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCCountHistory

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings NormalCrossingsInvariance HomogenizedGlueingTower MemberInterTowerAlong
  BoundaryCount HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsBiholomorphicMultiplicity HironakaNormalCrossingsJointBranchCharts
  HironakaNormalCrossingsSNCBlockCarrier HironakaNormalCrossingsGlobalPhaseCarrier
  HironakaOriginalOldBranchOpenHistory MaxLocusLocal BlowupRestrictOpen

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem preimage_union_list {D F : Type*} (f : D → F) (B : List (Set F)) :
    f ⁻¹' (⋃ C ∈ B, C) = ⋃ C ∈ B.map (f ⁻¹' ·), C := by
  ext x
  simp only [mem_preimage, mem_iUnion, List.mem_map]
  constructor
  · rintro ⟨C, hC, hx⟩
    exact ⟨f ⁻¹' C, ⟨C, hC, rfl⟩, hx⟩
  · rintro ⟨_, ⟨C, hC, rfl⟩, hx⟩
    exact ⟨C, hC, hx⟩

/-- Genuine original joint charts at arbitrary points, with every retained
slot preserved. No global maximum hypothesis is imposed at the point. -/
theorem exists_original_joint_branch_chart
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E) (x : X) :
    ∃ (U : Opens X) (B : List (Set U)), x ∈ U ∧
      IsSNCDivisor n (B ++ E.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (Subtype.val : U → X) ⁻¹' H = (⋃ C ∈ B, C) := by
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  let r := branchMultiplicity hH x
  let W : Opens X := ⟨{z | r + 1 ≤ branchMultiplicity hH z}ᶜ,
    (isClosed_branchMultiplicity_superlevel hH (r + 1)).isOpen_compl⟩
  have hxW : x ∈ W := by change ¬ r + 1 ≤ r; omega
  have hW := boundaryAdapted_open W h
  have hBound : ∀ z : W,
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) z ≤ r := by
    intro z
    rw [branchMultiplicity_open W hH (isNormalCrossingsCarrier_of_boundaryAdapted hW)]
    have hz := z.property
    change ¬ r + 1 ≤ branchMultiplicity hH z.val at hz
    omega
  have hxTop : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hW) ⟨x, hxW⟩ := by
    exact (branchMultiplicity_open W hH (isNormalCrossingsCarrier_of_boundaryAdapted hW) ⟨x, hxW⟩).ge
  obtain ⟨V, B, hxV, hSNC, hUnion, _hContain⟩ :=
    exists_highest_joint_branch_chart (X := CMfd.of (n := n) W) hW hBound hxTop
  let U : Opens X := ⟨(Subtype.val : W → X) '' (V : Set W),
    W.isOpen.isOpenMap_subtype_val _ V.isOpen⟩
  have hUW : U ≤ W := by rintro z ⟨p, _hp, rfl⟩; exact p.property
  have hNested : nestedOpens W U = V := by
    ext p
    constructor
    · rintro ⟨q, hq, heq⟩
      have hpq : q = p := Subtype.ext heq
      exact hpq ▸ hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  let e : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) U :=
    (BlowupTowerIsoTail.opensCongr (Y := CMfd.of (n := n) W) hNested.symm).trans
      (nestedOpensDiffeo (n := n) hUW)
  have he (p : V) : (e p : X) = (p.val : X) := rfl
  have heInv (p : U) : ((e.symm p).val : X) = p.val := by
    have hh := he (e.symm p)
    simpa only [e.apply_symm_apply] using hh.symm
  let D := B.map (e.symm ⁻¹' ·)
  have hPull := isSNCDivisor_map_preimage (MarkedIdealTowerTransport.pullsBackCoordinates e.symm)
    e.symm.contMDiff.continuous hSNC
  have hLists :
      ((E.map ((Subtype.val : W → X) ⁻¹' ·)).map ((Subtype.val : V → W) ⁻¹' ·)).map
          (e.symm ⁻¹' ·) = E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro C _hC
    ext p
    change ((e.symm p).val : X) ∈ C ↔ p.val ∈ C
    rw [heInv]
  refine ⟨U, D, ⟨⟨x, hxW⟩, hxV, rfl⟩, ?_, ?_⟩
  · rw [List.map_append, hLists] at hPull
    exact hPull
  · rw [← preimage_union_list, ← hUnion]
    ext p
    change p.val ∈ H ↔ ((e.symm p).val : X) ∈ H
    rw [heInv]

/-- An arbitrary actual original branch-test history produces its entire current
adapted pair. The original ideal/mark and all retained/born slots are unchanged. -/
theorem exists_current_pair_of_original_branch_history
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) :
    IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E := by
  have hWF : M.IsWellFormed := by
    refine ⟨?_, hI, isSNCDivisor_of_boundaryAdapted h, ?_⟩
    · rw [hN]; exact isClosedSubmanifold_univ
    · rw [hN]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor
        (isSNCDivisor_of_boundaryAdapted h)
  have hWFT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF T hT
  apply boundaryAdapted_of_open_traces (isClosed_strictAlong T h.1) hWFT.isSNCDivisor.1
  intro y
  obtain ⟨U, B, hxU, hSNC, hUnion⟩ := exists_original_joint_branch_chart h (T.proj y)
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let MB : MarkedIdeal n U := { MU with E := B ++ MU.E }
  let TU := restrict U T
  have hTU : IsGeoTestTower MB TU := hHistory U B hSNC hUnion
  have hWFB : MB.IsWellFormed := by
    refine ⟨?_, GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,
      hSNC, ?_⟩
    · change IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' M.N)
      rw [hN, preimage_univ]; exact isClosedSubmanifold_univ
    · change IsTransverse n ((Subtype.val : U → X) ⁻¹' M.N) (B ++ MU.E)
      rw [hN, preimage_univ]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  have hCurrentSNC : IsSNCDivisor n (B.map (strictAlong TU) ++ (geoTransformAlong MU TU).E) := by
    rw [← entire_original_old_retained_boundary MU B TU]
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWFB TU hTU).isSNCDivisor
  have hc := boundaryAdapted_union_of_snc_append _ _ hCurrentSNC
  have hUnionT : (⋃ C ∈ B.map (strictAlong TU), C) =
      (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T H :=
    (strictAlong_original_branch_union TU B).symm.trans
      ((congrArg (strictAlong TU) hUnion).symm.trans (strictAlong_restrict U T H))
  change IsBoundaryAdaptedCarrier (n := n) (⋃ C ∈ B.map (strictAlong TU), C)
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E at hc
  have hMN : IsClosedSubmanifold n M.N := by rw [hN]; exact isClosedSubmanifold_univ
  rw [hUnionT, geoTransformAlong_restrict U hMN hI T hT] at hc
  exact ⟨openPreimage T U, hxU, hc⟩

/-- The value is a function of original H and actual T alone. On the actual
history domain the internally proved NC property excludes the fallback. -/
def oldCount (H : Set X) (T : BlowupTower X Y) (y : Y) : ℕ :=
  if hNC : IsNormalCrossingsCarrier (n := n) (strictAlong T H) then
    branchMultiplicity hNC y else 0

theorem oldCount_eq {H : Set X} (T : BlowupTower X Y)
    (hNC : IsNormalCrossingsCarrier (n := n) (strictAlong T H)) (y : Y) :
    oldCount H T y = branchMultiplicity hNC y := by simp only [oldCount, dif_pos hNC]

private theorem count_congr {D : Type u} [TopologicalSpace D]
    [ChartedSpace (ComplexModel n) D] {A B : Set D}
    (hA : IsNormalCrossingsCarrier (n := n) A) (hB : IsNormalCrossingsCarrier (n := n) B)
    (he : A = B) (y : D) : branchMultiplicity hA y = branchMultiplicity hB y := by
  subst B
  rfl

/-- One literal original joint branch chart computes the intrinsic current
count, without deleting any vanished original branch slot. -/
theorem oldCount_eq_boundaryCount_chart
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T)
    (U : Opens X) (B : List (Set U))
    (hSNC : IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E))
    (hUnion : (Subtype.val : U → X) ⁻¹' H = (⋃ C ∈ B, C))
    (p : openPreimage T U) :
    oldCount H T p.val = boundaryCount (B.map (strictAlong (restrict U T))) p := by
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let MB : MarkedIdeal n U := { MU with E := B ++ MU.E }
  let TU := restrict U T
  have hWFB : MB.IsWellFormed := by
    refine ⟨?_, GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,
      hSNC, ?_⟩
    · change IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' M.N)
      rw [hN, preimage_univ]; exact isClosedSubmanifold_univ
    · change IsTransverse n ((Subtype.val : U → X) ⁻¹' M.N) (B ++ MU.E)
      rw [hN, preimage_univ]
      exact SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hSNC
  have hWF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWFB TU
    (hHistory U B hSNC hUnion)
  have hCurrentSNC : IsSNCDivisor n (B.map (strictAlong TU) ++ (geoTransformAlong MU TU).E) := by
    rw [← entire_original_old_retained_boundary MU B TU]
    exact hWF.isSNCDivisor
  let hRaw := boundaryAdapted_union_of_snc_append _ _ hCurrentSNC
  let hc := exists_current_pair_of_original_branch_history M hN hI h T hT hHistory
  let hp := boundaryAdapted_open (openPreimage T U) hc
  have hUnionT : (⋃ C ∈ B.map (strictAlong TU), C) =
      (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T H :=
    (strictAlong_original_branch_union TU B).symm.trans
      ((congrArg (strictAlong TU) hUnion).symm.trans (strictAlong_restrict U T H))
  calc
    oldCount H T p.val = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) p.val :=
      oldCount_eq T _ _
    _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) p :=
      (branchMultiplicity_open (openPreimage T U)
        (isNormalCrossingsCarrier_of_boundaryAdapted hc)
        (isNormalCrossingsCarrier_of_boundaryAdapted hp) p).symm
    _ = branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hRaw) p :=
      count_congr _ _ hUnionT.symm p
    _ = boundaryCount (B.map (strictAlong TU)) p :=
      (branchMultiplicity_union_eq_count _ _ hCurrentSNC p).1

/-- Actual strict-branch membership gives the one-step old-count inequality
for ANY compatible original history, including empty actual centres. -/
theorem oldCount_step_le
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower M (.step T C π hπ))
    (hHistory : IsOriginalBranchTestTower M H (.step T C π hπ)) (z : Z) :
    oldCount H (.step T C π hπ) z ≤ oldCount H T (π z) := by
  have hHistoryT : IsOriginalBranchTestTower M H T :=
    fun U B hSNC hUnion => (hHistory U B hSNC hUnion).1
  obtain ⟨U, B, hxU, hSNC, hUnion⟩ := exists_original_joint_branch_chart h (T.proj (π z))
  let S : BlowupTower X Z := .step T C π hπ
  let q : openPreimage S U := ⟨z, hxU⟩
  let p : openPreimage T U := ⟨π z, hxU⟩
  let ρ : openPreimage S U → openPreimage T U := fun v => ⟨π v.val, v.property⟩
  let CU : Set (openPreimage T U) := (Subtype.val : openPreimage T U → Y) ⁻¹' C
  have hρ : Continuous ρ := (contMDiff_opens_mk
    (hπ.contMDiff.comp contMDiff_subtype_val) (fun v : openPreimage S U => v.property)).continuous
  have hClosed : ∀ A ∈ B.map (strictAlong (restrict U T)), IsClosed A := by
    intro A hA
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hA
    exact isClosed_strictAlong _ (hSNC.1 D (List.mem_append_left _ hD))
  calc
    oldCount H S z = boundaryCount (B.map (strictAlong (restrict U S))) q :=
      oldCount_eq_boundaryCount_chart M hN hI h S hT hHistory U B hSNC hUnion q
    _ = boundaryCount ((B.map (strictAlong (restrict U T))).map
        (BlowupStrictSubmanifold.geoStrictTransform ρ CU)) q := by
      rw [List.map_map]
      rfl
    _ ≤ boundaryCount (B.map (strictAlong (restrict U T))) p :=
      boundaryCount_map_geoStrictTransform_le hρ hClosed q
    _ = oldCount H T (π z) :=
      (oldCount_eq_boundaryCount_chart M hN hI h T hT.1 hHistoryT U B hSNC hUnion p).symm

/-- Taking an actual prefix retains every universal original branch-test
history. This is a projection of the given domain, not a new certificate. -/
theorem originalBranchHistory_head (M : MarkedIdeal n X) {H : Set X} :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsOriginalBranchTestTower M H T →
      ∀ j : ℕ, IsOriginalBranchTestTower M H (head T j)
  | _, .refl, _h, 0 => fun _ _ _ _ => trivial
  | _, .refl, _h, _ + 1 => fun _ _ _ _ => trivial
  | _, .step _T _C _π _hπ, h, 0 => h
  | _, .step T _C _π _hπ, h, j + 1 =>
      originalBranchHistory_head M T (fun U B hSNC hUnion => (h U B hSNC hUnion).1) j

/-- Every literal prefix has an internally produced whole current adapted pair. -/
theorem currentPair_head
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (j : ℕ) :
    IsBoundaryAdaptedCarrier (n := n) (strictAlong (head T j) H)
      (geoTransformAlong M (head T j)).E :=
  exists_current_pair_of_original_branch_history M hN hI h (head T j)
    ((isGeoTestTower_iff_head_tail M T j).mp hT).1
    (originalBranchHistory_head M T hHistory j)

/-- Intrinsic whole-current old count on a literal open restriction.
The NC property on both sides is produced from the ambient history itself. -/
theorem oldCount_restrict
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (U : Opens X) (p : openPreimage T U) :
    oldCount ((Subtype.val : U → X) ⁻¹' H) (restrict U T) p = oldCount H T p.val := by
  let hc := exists_current_pair_of_original_branch_history M hN hI h T hT hHistory
  let hp := boundaryAdapted_open (openPreimage T U) hc
  have hNCU : IsNormalCrossingsCarrier (n := n)
      (strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' H)) := by
    rw [strictAlong_restrict U T H]
    exact isNormalCrossingsCarrier_of_boundaryAdapted hp
  rw [oldCount_eq _ hNCU, oldCount_eq _ (isNormalCrossingsCarrier_of_boundaryAdapted hc)]
  exact (count_congr hNCU (isNormalCrossingsCarrier_of_boundaryAdapted hp)
    (strictAlong_restrict U T H) p).trans
      (branchMultiplicity_open (openPreimage T U)
        (isNormalCrossingsCarrier_of_boundaryAdapted hc)
        (isNormalCrossingsCarrier_of_boundaryAdapted hp) p)

/-- Whole-current old count under an actual whole-history isomorphism.
Only the ambient original history domain is needed; the other NC carrier is
produced by genuine biholomorphic preimage geometry. -/
theorem oldCount_towerIso
    (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    {X' Y' : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower M T)
    (hHistory : IsOriginalBranchTestTower M H T) (y : Y') :
    oldCount (Φ ⁻¹' H) T' y = oldCount H T (χ y) := by
  let hc := exists_current_pair_of_original_branch_history M hN hI h T hT hHistory
  let hNC := isNormalCrossingsCarrier_of_boundaryAdapted hc
  have hNoExc (p : Y') : p ∉ exceptionalLocus n χ :=
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply p
  have hp := isNormalCrossingsCarrier_preimage χ.contMDiff hNoExc hNC
  have hNC' : IsNormalCrossingsCarrier (n := n) (strictAlong T' (Φ ⁻¹' H)) := by
    rw [hIso.strictAlong_eq]
    exact hp
  rw [oldCount_eq _ hNC', oldCount_eq _ hNC]
  exact (count_congr hNC' hp (hIso.strictAlong_eq H) y).trans
    (branchMultiplicity_diffeomorph χ hNC hp y)

end
end Hironaka.HironakaOriginalNCCountHistory
