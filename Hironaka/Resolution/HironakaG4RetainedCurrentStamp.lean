import Hironaka.Resolution.HironakaG4OrderedDefectStamp
import Hironaka.Resolution.HironakaG4RetainedRankTowerIso
import Hironaka.Resolution.HironakaSharpActualFamilyDefectOpenNaturality
import Hironaka.Resolution.HironakaActualRetainedBornResidualOpen
import Hironaka.Resolution.HironakaSharpActualEmptyChronologicalDefect

/-! Original chronological rows and actual native current tuple have the
same defect and ordered stamp. The exact current marked seed is retained. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedCurrentStamp
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower NormalCrossings
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealBiholomorphism HironakaActualRetainedBornResidualOpen
  MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG4OrderedDefectStamp HironakaG4RetainedRankOpenComparison
  HironakaG4RetainedRankTowerIso HironakaG4PreparedCentreCoordinates
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBoundaryMaskBlock
  HironakaActualRetainedBornResidualSeed HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFamilyDefectOpenNaturality HironakaSharpActualEmptyChronologicalDefect
  HironakaG34JointMaskEquivariance NormalCrossingsComparison NormalCrossingsInvariance

variable {n : ℕ} {X Y : CMfd.{u} n}

def retainedDefectOrderedRankAlong (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (z : Y) : (ℕ ×ₗ ℕ) ×ₗ ℕ :=
  let r := retainedProfileAlong N old born T z
  orderedDefectStampRank r (retainedInactiveRows N old born r T z)

private theorem actualFamilyDistinctDefect_finCongr {a b : ℕ} (hab : a=b)
    (N : Set Y) (F : Fin b → GermIdeal n Y) :
    actualFamilyDistinctDefect N (fun i : Fin a => F (finCongr hab i)) =
      actualFamilyDistinctDefect N F := by
  subst b
  rfl

/-- The chronological measure and defect at the current actual tuple are
exactly the native retained data used for the next local block. -/
theorem actual_retained_defect_and_rank_current_tuple (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let O := old.map (strictAlong T)
    actualFamilyDistinctDefect A.N (oldResidualPart A.N O A.E) =
      retainedDistinctDefect N old born T ∧
    ∀ z : Y,retainedDefectOrderedRank A.N O A.E z =
      retainedDefectOrderedRankAlong N old born T z := by
  classical
  intro A O
  let ι : Fin old.length ≃ Fin O.length := finCongr (List.length_map _).symm
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) T).ideal
  let G := oldResidualPart A.N O A.E
  have hRow (i : Fin old.length) : G (ι i) = F i :=
    congrArg (fun M : MarkedIdeal n Y => M.ideal)
      (retained_seed_eq_chronological_current hn hN hE hTr hdense T hT hFull i)
  have hFactor (i : Fin old.length) :
      oldMonomialPart A.N O A.E (ι i) = (retainedFactorMarked N old born T i).ideal := by
    have hGet : O.get (ι i) = strictAlong T (old.get i) := by simp [O,ι]
    unfold oldMonomialPart oldTraceIdeal retainedFactorMarked
    rw [hGet]
  refine ⟨?_,?_⟩
  · change actualFamilyDistinctDefect A.N G = actualFamilyDistinctDefect A.N F
    rw [←show actualFamilyDistinctDefect A.N (fun i => G (ι i)) =
      actualFamilyDistinctDefect A.N G from
        actualFamilyDistinctDefect_finCongr (List.length_map (as := old) _).symm A.N G]
    rw [show (fun i => G (ι i)) = F from funext hRow]
  · intro z
    let r := retainedProfileAlong N old born T z
    let s := fun j => ordinaryTraceOrder A.N (G j) z
    let P := retainedInactiveRows N old born r T z
    let Q := inactiveCanonicalRows A.N O A.E s z
    have hOrd (i : Fin old.length) : s (ι i) = r i := by
      change ordinaryTraceOrder A.N (G (ι i)) z = ordinaryTraceOrder A.N (F i) z
      rw [hRow]
    have hMask : Q = P.map ι.toEmbedding := by
      ext j
      obtain ⟨i,rfl⟩ := ι.surjective j
      rw [Finset.mem_map_equiv,ι.symm_apply_apply]
      simp only [Q,P,inactiveCanonicalRows,retainedInactiveRows,Finset.mem_filter,
        Finset.mem_univ,true_and,hOrd,hFactor]
    exact orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm r s P Q hOrd hMask

/-- An ordinary open inclusion preserves the actual starting retained
defect and the entire refined stamp rank of the same physical point. -/
theorem actual_retained_defect_and_rank_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G)) (U : Opens X) :
    let XU := CMfd.of (n := n) U
    let ν := (Subtype.val : U → X)
    let NU := ν ⁻¹' N
    let OU := old.map (ν ⁻¹' ·)
    let BU := born.map (ν ⁻¹' ·)
    actualFamilyDistinctDefect NU (oldResidualPart (X := XU) NU OU BU) =
      ν ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
    ∀ z : U,retainedDefectOrderedRank (X := XU) NU OU BU z =
      retainedDefectOrderedRank N old born z.val := by
  classical
  intro XU ν NU OU BU
  let ι : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
  let F := oldResidualPart N old born
  let G := oldResidualPart (X := XU) NU OU BU
  have hSeed (i : Fin old.length) := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hJ (i : Fin old.length) : GermIdeal.pullback (m := n) ν (F i) = G (ι i) :=
    congrArg (fun M : MarkedIdeal n U => M.ideal)
      (retainedResidualMarked_pullback_open hn hN hE hTr hdense U i)
  have hDef := actual_family_distinct_defect_open hn hN F (fun i => (hSeed i).1.isCoherent)
    (fun i => (hSeed i).2.1) (fun i => (hSeed i).2.2) U
  rw [show (fun i => GermIdeal.pullback (m := n) ν (F i)) =
    (fun i => G (ι i)) from funext hJ] at hDef
  refine ⟨?_,?_⟩
  · exact (actualFamilyDistinctDefect_finCongr (List.length_map (as := old) _).symm NU G).symm.trans hDef
  · intro z
    let T : BlowupTower X X := .refl
    let R := restrict U T
    let e := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞
    have h := actual_retained_rank_open_tower_iso hn hN hE hTr hdense U T trivial trivial
      R trivial trivial e (IsTowerIso.refl_self R) z
    let r := fun i => ordinaryTraceOrder N (F i) z.val
    let s := fun j => ordinaryTraceOrder NU (G j) z
    let P := inactiveCanonicalRows N old born r z.val
    let Q := inactiveCanonicalRows (X := XU) NU OU BU s z
    exact orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm r s P Q
      h.1 h.2.1

set_option maxHeartbeats 480000 in
/-- Exact native retained defect under an actual open embedding. Thus a
restriction followed by an actual transport preserves terminal defect
emptiness of the transported retained tuple. -/
theorem actual_retained_defect_open_embedding (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {Z : CMfd.{u} n} (f : Z → X) (hf : HironakaBaseChange.IsOpenHoloEmbedding n f) :
    let NZ := f ⁻¹' N
    let OZ := old.map (f ⁻¹' ·)
    let BZ := born.map (f ⁻¹' ·)
    actualFamilyDistinctDefect NZ (oldResidualPart NZ OZ BZ) =
      f ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born) := by
  intro NZ OZ BZ
  have hfCopy := hf
  obtain ⟨U,φ,hφ⟩ := hfCopy
  let XU := CMfd.of (n := n) U
  let ν := (Subtype.val : U → X)
  let NU := ν ⁻¹' N
  let OU := old.map (ν ⁻¹' ·)
  let BU := born.map (ν ⁻¹' ·)
  let ιU : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
  let ιZ : Fin old.length ≃ Fin OZ.length := finCongr (List.length_map _).symm
  let F := oldResidualPart N old born
  let FU := oldResidualPart (X := XU) NU OU BU
  let FZ := oldResidualPart NZ OZ BZ
  have hfComp : f=ν ∘ φ := funext hφ
  have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hEU : IsSNCDivisor n (OU ++ BU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTU : IsTransverse n NU BU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ OU ++ BU,H) := by
    simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hdense U
  have hSeedU i := retainedResidualMarked_geometry (X := XU) hn hNU hEU hTU hDenseU i
  have hSeed i := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hFU (i : Fin old.length) :
      GermIdeal.pullback (m := n) ν (F i) = FU (ιU i) :=
    congrArg (fun M : MarkedIdeal n U => M.ideal)
      (retainedResidualMarked_pullback_open hn hN hE hTr hdense U i)
  have hFZ (i : Fin old.length) : GermIdeal.pullback (m := n) f (F i) = FZ (ιZ i) := by
    have hGet : OZ.get (ιZ i) = f ⁻¹' old.get i := by simp [OZ,ιZ]
    unfold F FZ oldResidualPart oldTraceIdeal
    rw [hGet]
    exact pullback_residual hf hn hN hE hTr hdense i
  have hJ (i : Fin old.length) : GermIdeal.pullback (m := n) φ (FU (ιU i)) = FZ (ιZ i) := by
    have hC : (F i).IsCoherent := (hSeed i).1.isCoherent
    rw [←hFU,←GermIdealTotalTransform.pullback_comp (f := ν) (g := φ) contMDiff_subtype_val φ.contMDiff hC,
      ←hfComp,hFZ]
  have hU := (actual_retained_defect_and_rank_open hn hN hE hTr hdense U).1
  have hB := actual_family_distinct_defect_biholo hn φ hNU FU
    (fun i => (hSeedU i).1.isCoherent) (fun i => (hSeedU i).2.1) (fun i => (hSeedU i).2.2)
  let GU := fun i : Fin OU.length => GermIdeal.pullback (m := n) φ (FU i)
  have hNativeN : φ ⁻¹' NU = NZ := by
    change φ ⁻¹' (ν ⁻¹' N) = f ⁻¹' N
    rw [hfComp,Set.preimage_comp]
  change actualFamilyDistinctDefect (φ ⁻¹' NU) GU = φ ⁻¹' actualFamilyDistinctDefect NU FU at hB
  rw [hNativeN,hU,←Set.preimage_comp,←hfComp] at hB
  have hCastU : actualFamilyDistinctDefect NZ (fun i => GU (ιU i)) =
      actualFamilyDistinctDefect NZ GU :=
    actualFamilyDistinctDefect_finCongr (List.length_map (as := old) _).symm NZ GU
  have hCastZ : actualFamilyDistinctDefect NZ (fun i => FZ (ιZ i)) =
      actualFamilyDistinctDefect NZ FZ :=
    actualFamilyDistinctDefect_finCongr (List.length_map (as := old) _).symm NZ FZ
  change actualFamilyDistinctDefect NZ FZ = _
  rw [←hCastZ,←show (fun i => GU (ιU i)) = (fun i => FZ (ιZ i)) from funext hJ,
    hCastU,hB]

/-- The complete encoded rank and true defect commute with a native base
biholomorphism under the ordered old-boundary index cast. -/
theorem actual_retained_defect_and_rank_biholomorph (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {Z : CMfd.{u} n} (φ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    let NZ := φ ⁻¹' N
    let OZ := old.map (φ ⁻¹' ·)
    let BZ := born.map (φ ⁻¹' ·)
    actualFamilyDistinctDefect NZ (oldResidualPart NZ OZ BZ) =
      φ ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
    ∀ z : Z,retainedDefectOrderedRank NZ OZ BZ z = retainedDefectOrderedRank N old born (φ z) := by
  intro NZ OZ BZ
  refine ⟨actual_retained_defect_open_embedding hn hN hE hTr hdense φ
    (isOpenHoloEmbedding_diffeomorph φ),?_⟩
  intro z
  let S : BlowupTower X X := .refl
  let R : BlowupTower Z Z := .refl
  let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (φ z)
  let s := fun i => ordinaryTraceOrder NZ (oldResidualPart NZ OZ BZ i) z
  let P := inactiveCanonicalRows N old born r (φ z)
  let Q := inactiveCanonicalRows NZ OZ BZ s z
  have h := actual_retained_rank_under_tower_iso hn φ hN hE hTr hdense S trivial trivial R φ
    IsTowerIso.refl z
  exact orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm r s P Q
    h.1 h.2.1

end
end Hironaka.HironakaG4RetainedCurrentStamp
