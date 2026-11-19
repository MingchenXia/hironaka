import Hironaka.Resolution.HironakaActualRetainedBornResidualSeed
import Hironaka.Resolution.HironakaG4PreparedMixedSelectedStep
import Hironaka.Resolution.HironakaActualRetainedBoundaryJointStep
import Hironaka.Resolution.HironakaSharpActualFamilyDefectOpenNaturality

/-! Whole retained-born canonical residuals and normalized products on actual
target opens. The source-first proof is
`hironaka-actual-retained-born-residual-open-20261101.tex`. No order,
preparedness or future residual-comparison premise is used. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualRetainedBornResidualOpen
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings MonomialPartAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaG4PreparedCentreCoordinates HironakaG4RecordedTowerResidualCompatibility
  HironakaActualRetainedBornResidualSeed HironakaActualRetainedBoundaryJointStep
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualEquimultipleResidualHistory
  RelativePrincipalizationSpan RestrictedIdealExtension

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- All four actual retained-seed fields pull back, including the entire born list. -/
theorem retainedResidualMarked_pullback_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X) (i : Fin old.length) :
    let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let iU : Fin oldU.length := ⟨i.val,by simpa only [oldU,List.length_map] using i.isLt⟩
    MarkedIdeal.pullback (Subtype.val : U → X) (retainedResidualMarked N old born i) =
      retainedResidualMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
        oldU (born.map ((Subtype.val : U → X) ⁻¹' ·)) iU := by
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let iU : Fin oldU.length := ⟨i.val,by simpa only [oldU,List.length_map] using i.isLt⟩
  have hGet : oldU.get iU = (Subtype.val : U → X) ⁻¹' old.get i := by simp [oldU,iU]
  have hJ := (HironakaG4PreparedMixedSelectedStep.open_parts_pullback_native
    hn hN hE hTr hdense U i).2
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_ <;> try rfl
  change GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) =
    oldResidualPart (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
      oldU (born.map ((Subtype.val : U → X) ⁻¹' ·)) iU
  simpa only [oldResidualPart,oldTraceIdeal,hGet] using hJ.symm

/-- Original chronological rows on an actual target open are the native retained seeds. -/
theorem original_chronological_row_pullback_open (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (U : Opens Y) (i : Fin E.length) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let oldU := (E.map (strictAlong T)).map ((Subtype.val : U → Y) ⁻¹' ·)
    let iU : Fin oldU.length := ⟨i.val,by simpa only [oldU,List.length_map] using i.isLt⟩
    MarkedIdeal.pullback (Subtype.val : U → Y)
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T) =
      retainedResidualMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → Y) ⁻¹' A.N)
        oldU (A.E.map ((Subtype.val : U → Y) ⁻¹' ·)) iU := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let j : Fin (E.map (strictAlong T)).length :=
    ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
  have hDict := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hOpen := retainedResidualMarked_pullback_open hn hDict.1 hDict.2.1
    hDict.2.2.1 hDict.2.2.2.1 U j
  have hRow := retained_seed_eq_original_chronological hn hW hE hdense T hT hFull i
  rw [hRow] at hOpen
  exact hOpen

private theorem canonicalResidualFamily_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X) :
    canonicalResidualFamily (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
      (old.map ((Subtype.val : U → X) ⁻¹' ·)) (born.map ((Subtype.val : U → X) ⁻¹' ·)) =
      (canonicalResidualFamily N old born).map (GermIdeal.pullback (m := n) (Subtype.val : U → X)) := by
  simp only [canonicalResidualFamily,List.map_map]
  apply List.map_congr_left
  intro H hH
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
  exact (HironakaG4PreparedMixedSelectedStep.open_parts_pullback_native
    hn hN hE hTr hdense U i).2

/-- The native normalized finite product pulls back with the SAME retained born list and mark. -/
theorem canonicalProductMarked_pullback_open (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (q : ℕ) (U : Opens X) :
    MarkedIdeal.pullback (Subtype.val : U → X) (canonicalProductMarked N old born q) =
      canonicalProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
        (old.map ((Subtype.val : U → X) ⁻¹' ·)) (born.map ((Subtype.val : U → X) ⁻¹' ·)) q := by
  have hCoh : ∀ I ∈ canonicalResidualFamily N old born,I.IsCoherent := by
    intro I hI
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hI
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.1
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_ <;> try rfl
  change GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (relativeIdealListProduct N (canonicalResidualFamily N old born)) =
    relativeIdealListProduct (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
      (canonicalResidualFamily (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
        (old.map ((Subtype.val : U → X) ⁻¹' ·)) (born.map ((Subtype.val : U → X) ⁻¹' ·)))
  rw [HironakaSharpActualFamilyDefectOpenNaturality.relativeIdealListProduct_open
    hN (canonicalResidualFamily N old born) hCoh U]
  rw [canonicalResidualFamily_open hn hN hE hTr hdense U]

/-- The actual canonical current product is the SAME original chronological residual record. -/
theorem canonicalProductMarked_eq_original_residualMarked (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (q : ℕ) :
    let A := geoTransformAlong (geometricTemplate W []) T
    canonicalProductMarked A.N (E.map (strictAlong T)) A.E q = residualMarked W E q T := by
  let A := geoTransformAlong (geometricTemplate W []) T
  have hRows : canonicalResidualFamily A.N (E.map (strictAlong T)) A.E =
      chronologicalMemberFamily W E T := by
    simp only [canonicalResidualFamily,chronologicalMemberFamily,List.map_map]
    apply List.map_congr_left
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    have h := congrArg MarkedIdeal.ideal
      (retained_seed_eq_original_chronological hn hW hE hdense T hT hFull i)
    simpa [retainedResidualMarked,oldResidualPart,oldTraceIdeal] using h
  change (⟨A.N,A.E,relativeIdealListProduct A.N
      (canonicalResidualFamily A.N (E.map (strictAlong T)) A.E),q⟩ : MarkedIdeal n Y) = _
  rw [hRows]
  rfl

/-- The original marked residual product restricts to the actual native retained canonical product. -/
theorem original_residualMarked_pullback_open (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (q : ℕ) (U : Opens Y) :
    let A := geoTransformAlong (geometricTemplate W []) T
    MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T) =
      canonicalProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → Y) ⁻¹' A.N)
        ((E.map (strictAlong T)).map ((Subtype.val : U → Y) ⁻¹' ·))
        (A.E.map ((Subtype.val : U → Y) ⁻¹' ·)) q := by
  have hDict := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hOpen := canonicalProductMarked_pullback_open hn hDict.1 hDict.2.1
    hDict.2.2.1 hDict.2.2.2.1 q U
  rw [canonicalProductMarked_eq_original_residualMarked hn hW hE hdense T hT hFull q] at hOpen
  exact hOpen

end
end Hironaka.HironakaActualRetainedBornResidualOpen
