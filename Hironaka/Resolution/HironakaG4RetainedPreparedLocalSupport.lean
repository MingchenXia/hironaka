import Hironaka.Resolution.HironakaG34PreparedRowEmptyTail
import Hironaka.Resolution.HironakaActualRetainedBornResidualOpen
import Hironaka.Resolution.HironakaG4SharpBadFootprint
import Hironaka.Resolution.HironakaG34NonPureLowDim

/-! A retained prepared row keeps its actual support and preparation across
an actual tower whose original footprint misses that support. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparedLocalSupport
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HironakaActualRetainedBornResidualSeed HironakaActualRetainedBornResidualOpen
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpActualChronologicalStrictStep
  HironakaG34PreparedRowEmptyTail HironakaG4SharpBadFootprint
  RelativePrincipalizationSpan RestrictEmptyTower MarkedIdealRestrictOpen
  HironakaG34NonPureLowDim HironakaSharpOriginalAllBoundaryCentre NonmonomialOrderLocal

variable {n : ℕ} {X Y Z : CMfd.{u} n}

def retainedRowSupport (N : Set X) (old born : List (Set X)) (i : Fin old.length)
    (T : BlowupTower X Y) : Set Y :=
  (chronologicalMarked (retainedResidualMarked N old born i) T).N ∩
    (chronologicalMarked (retainedResidualMarked N old born i) T).ideal.zeroLocus

def retainedRowBoundary (N : Set X) (old born : List (Set X)) (i : Fin old.length)
    (T : BlowupTower X Y) : List (Set Y) :=
  (old.map (strictAlong T)).eraseIdx i.val ++ (geoTransformAlong (geometricTemplate N born) T).E

def RetainedRowPrepared (N : Set X) (old born : List (Set X)) (i : Fin old.length)
    (T : BlowupTower X Y) : Prop :=
  let M := chronologicalMarked (retainedResidualMarked N old born i) T
  let S := retainedRowSupport N old born i T
  let F := retainedRowBoundary N old born i T
  (∀ y ∈ M.N,ordinaryTraceOrder M.N M.ideal y ≤ 1) ∧
    HasNormalCrossings n S F ∧ S ⊆ closure (S \ ⋃ G ∈ F,G)

private theorem retainedRowBoundary_step (N : Set X) (old born : List (Set X))
    (i : Fin old.length) (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    retainedRowBoundary N old born i (.step T C π hπ)=
      (retainedRowBoundary N old born i T).map (geoStrictTransform π C) ++ [π ⁻¹' C] := by
  have hOld : old.map (strictAlong (.step T C π hπ))=
      (old.map (strictAlong T)).map (geoStrictTransform π C) := by
    rw [List.map_map]
    rfl
  change (old.map (strictAlong (.step T C π hπ))).eraseIdx i.val ++
      ((geoTransformAlong (geometricTemplate N born) T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C])=
    ((old.map (strictAlong T)).eraseIdx i.val ++ (geoTransformAlong (geometricTemplate N born) T).E).map
      (geoStrictTransform π C) ++ [π ⁻¹' C]
  rw [hOld,List.eraseIdx_map,List.map_append,List.append_assoc]

/-- Actual chronological preparation and exact support transport across a
tower supported away from the initially prepared row. This is available in
the retained ambient itself, including any open restriction of that ambient. -/
theorem retained_prepared_row_of_disjoint_footprint (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G)) (i : Fin old.length)
    (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {D : Set X} (hDisj : Disjoint D (retainedRowSupport N old born i (.refl : BlowupTower X X)))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hOver : CentresOver D T) :
    RetainedRowPrepared N old born i T ∧
      retainedRowSupport N old born i T =
        T.proj ⁻¹' retainedRowSupport N old born i (.refl : BlowupTower X X) := by
  obtain ⟨hSeed,hNZ,hPr⟩ := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hAux : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N born) T → CentresOver D T →
      RetainedRowPrepared N old born i T ∧
        retainedRowSupport N old born i T =
          T.proj ⁻¹' retainedRowSupport N old born i (.refl : BlowupTower X X) ∧
        ∀ G ∈ retainedRowBoundary N old born i T,IsClosed G := by
    intro Y T
    induction T with
    | refl =>
      intro _ _
      refine ⟨hPrep,rfl,?_⟩
      intro G hG
      unfold retainedRowBoundary at hG
      rw [show List.map (strictAlong (.refl : BlowupTower X X)) old = old from List.map_id old] at hG
      change G ∈ old.eraseIdx i.val ++ born at hG
      apply hE.1 G
      rcases List.mem_append.mp hG with h | h
      · exact List.mem_append_left _ (List.mem_of_mem_eraseIdx h)
      · exact List.mem_append_right _ h
    | step T C π hπ ih =>
      intro hT hOver
      obtain ⟨⟨hOrd,hNC,hDense⟩,hSupp,hClosed⟩ := ih hT.1 hOver.1
      let M := chronologicalMarked (retainedResidualMarked N old born i) T
      let S := retainedRowSupport N old born i T
      let F := retainedRowBoundary N old born i T
      obtain ⟨hwM,hnzM,hprM⟩ := chronologicalMarked_actual_geometry hn
        (retainedResidualMarked N old born i) hSeed rfl hNZ hPr T hT.1
      have hNext := chronologicalMarked_actual_geometry hn
        (retainedResidualMarked N old born i) hSeed rfl hNZ hPr (.step T C π hπ) hT
      have hMN : M.N=(geoTransformAlong (geometricTemplate N born) T).N :=
        (chronologicalMarked_geometric_fields (retainedResidualMarked N old born i) T).1
      have hCN : C ⊆ M.N := by rw [hMN]; exact hT.2.subset_N
      have hSC : IsClosed S :=
        hwM.isClosedSubmanifold_N.1.inter (OrderTaylor.isClosed_zeroLocus_of_isCoherent hwM.isCoherent)
      have hCS : Disjoint C S := by
        change Disjoint C (retainedRowSupport N old born i T)
        rw [hSupp]
        exact (hDisj.preimage T.proj).mono_left hOver.2
      have hs := nextRelativeStrict_support_of_disjoint hn hwM.isClosedSubmanifold_N hwM.isCoherent
        hnzM hprM hπ hCN hCS hNext.1.isClosedSubmanifold_N
      have hNewS : retainedRowSupport N old born i (.step T C π hπ)=π ⁻¹' S := hs.2.2
      have hNewF := retainedRowBoundary_step N old born i T C π hπ
      refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
      · intro z hz
        exact (hs.1 z hz).trans (hOrd (π z)
          (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hwM.isClosedSubmanifold_N.1 hz))
      · rw [hNewS,hNewF]
        intro z hz
        have hzC : π z ∉ C := fun hc => Set.disjoint_left.mp hCS hc hz
        have hStrict : geoStrictTransform π C S = π ⁻¹' S :=
          geoStrictTransform_eq_preimage_of_disjoint hπ.contMDiff.continuous hSC hCS
        by_contra hBad
        have hBad' : z ∈ originalSharpBadLocus (n := n) (geoStrictTransform π C S)
            (F.map (geoStrictTransform π C) ++ [π ⁻¹' C]) := by
          rw [hStrict]
          exact ⟨hz,hBad⟩
        rcases originalSharpBadLocus_strict_subset_preimage_union hSC hClosed hπ hBad' with h | h
        · exact h.2 (hNC (π z) hz)
        · exact hzC h
      · change (retainedRowSupport N old born i (.step T C π hπ)) ⊆
          closure (retainedRowSupport N old born i (.step T C π hπ) \
            ⋃ G ∈ retainedRowBoundary N old born i (.step T C π hπ),G)
        rw [hNewS,hNewF]
        exact preimage_subset_closure_strict_of_disjoint hπ hClosed hCS hDense
      · rw [hNewS,show S = T.proj ⁻¹' retainedRowSupport N old born i .refl from hSupp]
        rfl
      · rw [hNewF]
        intro G hG
        rcases List.mem_append.mp hG with h | h
        · obtain ⟨H,_hH,rfl⟩ := List.mem_map.mp h
          exact isClosed_closure
        · rw [List.mem_singleton] at h
          rw [h]
          exact hπ.1.1.preimage hπ.contMDiff.continuous
  exact ⟨(hAux T hT hOver).1,(hAux T hT hOver).2.1⟩

/-- On a shrunken open ambient, preparation is retained with the exact
preimage of the original chronological row support. -/
theorem retained_prepared_row_restrict_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G)) (i : Fin old.length)
    (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X)) (U : Opens X) :
    let v := (Subtype.val : U → X)
    let OU := old.map (v ⁻¹' ·)
    let BU := born.map (v ⁻¹' ·)
    let iU : Fin OU.length := Fin.cast (List.length_map _).symm i
    RetainedRowPrepared (X := CMfd.of (n := n) U) (v ⁻¹' N) OU BU iU .refl ∧
      retainedRowSupport (X := CMfd.of (n := n) U) (v ⁻¹' N) OU BU iU .refl =
        v ⁻¹' retainedRowSupport N old born i .refl := by
  intro v OU BU iU
  let Z := CMfd.of (n := n) U
  let M := retainedResidualMarked N old born i
  let MU := retainedResidualMarked (X := Z) (v ⁻¹' N) OU BU iU
  let S := retainedRowSupport N old born i (.refl : BlowupTower X X)
  let SU := retainedRowSupport (X := Z) (v ⁻¹' N) OU BU iU .refl
  let F := retainedRowBoundary N old born i (.refl : BlowupTower X X)
  let FU := retainedRowBoundary (X := Z) (v ⁻¹' N) OU BU iU .refl
  have hM : MarkedIdealBiholomorphism.MarkedIdeal.pullback v M = MU :=
    retainedResidualMarked_pullback_open hn hN hE hTr hdense U i
  have hI := congrArg (fun L : MarkedIdeal n U => L.ideal) hM
  obtain ⟨hSeed,hNZ,_hPr⟩ := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hv : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ v := contMDiff_subtype_val
  have hS : SU = v ⁻¹' S := by
    change (v ⁻¹' N) ∩ MU.ideal.zeroLocus = v ⁻¹' (N ∩ M.ideal.zeroLocus)
    rw [←hI]
    exact congrArg (fun A => (v ⁻¹' N) ∩ A) (BlowupExceptionalDivisor.zeroLocus_pullback hv hSeed.isCoherent)
  have hF : FU = F.map (v ⁻¹' ·) := by
    change (OU.map (strictAlong (.refl : BlowupTower Z Z))).eraseIdx iU.val ++ BU =
      (((old.map (strictAlong (.refl : BlowupTower X X))).eraseIdx i.val) ++ born).map (v ⁻¹' ·)
    have hIndex : iU.val = i.val := rfl
    rw [hIndex, show List.map (strictAlong (.refl : BlowupTower Z Z)) OU = OU from List.map_id OU,
      show List.map (strictAlong (.refl : BlowupTower X X)) old = old from List.map_id old,
      List.map_append,List.eraseIdx_map]
  obtain ⟨hOrd,hNC,hDense⟩ := hPrep
  refine ⟨⟨?_,?_,?_⟩,hS⟩
  · intro x hx
    have hOrd' := nmOrd_pullback_val hn (ordinaryTraceMarked_isWellFormed hN hSeed.isCoherent) hNZ U x
    change ordinaryTraceOrder (v ⁻¹' N)
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback v M).ideal x =
      ordinaryTraceOrder N M.ideal x.val at hOrd'
    rw [hM] at hOrd'
    exact hOrd'.trans_le (hOrd x.val hx)
  · change HasNormalCrossings n SU FU
    rw [hS,hF]
    intro x hx
    exact normalCrossingsAt_preimage_val_iff.mpr (hNC x.val hx)
  · change SU ⊆ closure (SU \ ⋃ G ∈ FU,G)
    rw [hS,hF]
    exact open_full_density hDense U

set_option maxHeartbeats 450000 in
/-- A tower on a restricted open preserves an originally prepared row
whenever its footprint misses that row in the original ambient. -/
theorem retained_prepared_row_on_open_tower_of_disjoint_footprint (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G)) (i : Fin old.length)
    (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {D : Set X} (hDisj : Disjoint D (retainedRowSupport N old born i (.refl : BlowupTower X X)))
    (U : Opens X) (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : IsGeoTestTower (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
      (born.map ((Subtype.val : U → X) ⁻¹' ·))) T)
    (hOver : CentresOver ((Subtype.val : U → X) ⁻¹' D) T) (k : ℕ) :
    let v := (Subtype.val : U → X)
    let OU := old.map (v ⁻¹' ·)
    let BU := born.map (v ⁻¹' ·)
    let iU : Fin OU.length := Fin.cast (List.length_map _).symm i
    let Q := BlowupTowerSplit.head T k
    RetainedRowPrepared (v ⁻¹' N) OU BU iU Q ∧
      retainedRowSupport (v ⁻¹' N) OU BU iU Q =
        (v ∘ Q.proj) ⁻¹' retainedRowSupport N old born i .refl := by
  intro v OU BU iU Q
  let Z := CMfd.of (n := n) U
  obtain ⟨hPrepU,hSuppU⟩ := retained_prepared_row_restrict_open hn hN hE hTr hdense i hPrep U
  let S := retainedRowSupport (X := Z) (v ⁻¹' N) OU BU iU .refl
  have hSupport : S = v ⁻¹' retainedRowSupport N old born i .refl := hSuppU
  have hDisjU : Disjoint (v ⁻¹' D) S :=
    hSupport.symm ▸ hDisj.preimage v
  have hEU : IsSNCDivisor n (OU ++ BU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hDenseU : v ⁻¹' N ⊆ closure (v ⁻¹' N \ ⋃ G ∈ OU ++ BU,G) := by
    simpa only [List.map_append] using open_full_density hdense U
  have hNU : IsClosedSubmanifold n (v ⁻¹' N) :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hTU : IsTransverse n (v ⁻¹' N) BU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hTests : IsGeoTestTower (geometricTemplate (X := Z) (v ⁻¹' N) BU) Q :=
    ((BlowupTowerSplit.isGeoTestTower_iff_head_tail _ T k).mp hT).1
  have hOverQ : CentresOver (v ⁻¹' D) Q := centresOver_head _ T k hOver
  obtain ⟨hPrepQ,hSuppQ⟩ := retained_prepared_row_of_disjoint_footprint (X := Z) hn
    hNU hEU hTU hDenseU iU hPrepU hDisjU Q hTests hOverQ
  exact ⟨hPrepQ,hSuppQ.trans (congrArg (fun A : Set U => Q.proj ⁻¹' A) hSupport)⟩

end
end Hironaka.HironakaG4RetainedPreparedLocalSupport
