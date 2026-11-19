import Hironaka.Resolution.HironakaG4ProcessedMaskRestriction
import Hironaka.Resolution.HironakaG4RetainedPreparedLocalSupport
import Hironaka.Resolution.HironakaActualOriginalProcessedJointPreparedness
import Hironaka.Resolution.HironakaActualProtectedGammaOpenCompatibility

/-! Restrict the actual processed prefix, preserving its two tests, every
original residual support and its sharp count bound. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ProcessedStateRestriction

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings NormalCrossingsInvariance HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedTowerResidualCompatibility HironakaG4ProcessedMaskRestriction
  HironakaG4RetainedPreparedLocalSupport HironakaActualRetainedBornResidualSeed
  HironakaActualProcessedAllMasksDrop HironakaActualProcessedMaskFiniteBlock
  HironakaActualOriginalProcessedJointPreparedness
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaActualProtectedGammaOpenCompatibility
  HomogenizedGlueingTower RestrictEmptyTower IdealWeightPowers
  HironakaG34NonPureLowDim HironakaG4MonomialFamilyInvariant

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 550000 in
/-- Every field of the original processed state restricts to a literal base
open, with both source lists retained, and each residual support is its
exact preimage on the terminal open. -/
theorem processed_at_restrict (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (q : ℕ) (hAt : At W E q T) (U : Opens X) :
    let v := (Subtype.val : U → X)
    let u := (Subtype.val : openPreimage T U → Y)
    let WU := v ⁻¹' W
    let EU := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EU.length := finCongr (List.length_map _).symm
    let R := restrict U T
    At WU EU q R ∧ ∀ i : Fin E.length,residualSupport WU EU R (e i) = u ⁻¹' residualSupport W E T i := by
  intro v u WU EU e R
  let A := geoTransformAlong (geometricTemplate W []) T
  let B := geoTransformAlong (geometricTemplate WU []) R
  let old := E.map (strictAlong T)
  let oldU := EU.map (strictAlong R)
  rcases hAt with ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,_hPrepared,hBound⟩
  have hWU : IsClosedSubmanifold n WU :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU : IsSNCDivisor n EU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hDenseU : WU ⊆ closure (WU \ ⋃ H ∈ EU,H) := open_full_density hdense U
  have hRU := isGeoTestTower_restrict U hW isCoherent_unitIdeal T hT
  rw [template_pullback (X := X) (Y := CMfd.of (n := n) U),List.map_nil] at hRU
  have hFullU := isGeoTestTower_restrict U isClosedSubmanifold_univ isCoherent_unitIdeal T hFull
  rw [template_pullback (X := X) (Y := CMfd.of (n := n) U),preimage_univ] at hFullU
  have hSharpU := currentSharp_restrict U T hFull hSharp
  have hGeom := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hBU : B = MarkedIdeal.pullback u A := original_carrier_template_restrict hW T hT U
  have hBU_N : B.N = u ⁻¹' A.N := congrArg MarkedIdeal.N hBU
  have hBU_E : B.E = A.E.map (u ⁻¹' ·) := congrArg MarkedIdeal.E hBU
  have hOld : oldU = old.map (u ⁻¹' ·) := by
    simp only [oldU,EU,old,List.map_map]
    refine List.map_congr_left ?_
    intro H _
    exact strictAlong_restrict U T H
  have hRows (i : Fin E.length) :
      let J := chronologicalMarked (originalRelativeMemberMarked WU (EU.get (e i))) R
      let S := residualSupport WU EU R (e i)
      let F := oldU.eraseIdx (e i).val ++ B.E
      (∀ x ∈ B.N,ordinaryTraceOrder B.N J.ideal x ≤ 1) ∧
        HasNormalCrossings n S F ∧ S ⊆ closure (S \ ⋃ H ∈ F,H) ∧
        S = u ⁻¹' residualSupport W E T i := by
    let j : Fin old.length := Fin.cast (List.length_map _).symm i
    let jU : Fin (old.map (u ⁻¹' ·)).length := Fin.cast (List.length_map _).symm j
    let jm : Fin oldU.length := Fin.cast (List.length_map _).symm (e i)
    let M := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    let MU := chronologicalMarked (originalRelativeMemberMarked WU (EU.get (e i))) R
    have hSeed : retainedResidualMarked A.N old A.E j = M :=
      retained_seed_eq_original_chronological hn hW hE hdense T hT hFull i
    have hSeedU : retainedResidualMarked B.N oldU B.E jm = MU :=
      retained_seed_eq_original_chronological hn hWU hEU hDenseU R hRU hFullU (e i)
    have hRe : RetainedRowPrepared A.N old A.E j (.refl : BlowupTower Y Y) := by
      have hMN : M.N = A.N := (chronologicalMarked_geometric_fields
        (originalRelativeMemberMarked W (E.get i)) T).1
      have hF : retainedRowBoundary A.N old A.E j (.refl : BlowupTower Y Y) =
          old.eraseIdx i.val ++ A.E := by
        change (old.map id).eraseIdx i.val ++ A.E = _
        rw [List.map_id]
      have hS : retainedRowSupport A.N old A.E j (.refl : BlowupTower Y Y) =
          residualSupport W E T i := by
        change (retainedResidualMarked A.N old A.E j).N ∩
          (retainedResidualMarked A.N old A.E j).ideal.zeroLocus = _
        rw [hSeed,hMN]
        rfl
      refine ⟨?_,?_,?_⟩
      · change ∀ x ∈ (retainedResidualMarked A.N old A.E j).N,
          ordinaryTraceOrder (retainedResidualMarked A.N old A.E j).N
            (retainedResidualMarked A.N old A.E j).ideal x ≤ 1
        rw [hSeed,hMN]
        exact fun x hx => hOrd x hx i
      · rw [hS,hF]
        exact hNC i
      · rw [hS,hF]
        exact hDenseS i
    have hNew := retained_prepared_row_restrict_open hn hGeom.1 hGeom.2.1 hGeom.2.2.1
      hGeom.2.2.2.1 j hRe (openPreimage T U)
    have hNew' : RetainedRowPrepared B.N oldU B.E jm
          (.refl : BlowupTower (CMfd.of (n := n) (openPreimage T U)) _) ∧
        retainedRowSupport B.N oldU B.E jm
          (.refl : BlowupTower (CMfd.of (n := n) (openPreimage T U)) _) =
        u ⁻¹' retainedRowSupport A.N old A.E j (.refl : BlowupTower Y Y) := by
      rw [hBU_N,hBU_E]
      let F := old.map (u ⁻¹' ·)
      have hReindex (L : List (Set (openPreimage T U))) (hL : L = F)
          (k : Fin L.length) (hk : k.val = j.val) :
          RetainedRowPrepared (u ⁻¹' A.N) L (A.E.map (u ⁻¹' ·)) k
            (.refl : BlowupTower (CMfd.of (n := n) (openPreimage T U)) _) ∧
          retainedRowSupport (u ⁻¹' A.N) L (A.E.map (u ⁻¹' ·)) k
            (.refl : BlowupTower (CMfd.of (n := n) (openPreimage T U)) _) =
              u ⁻¹' retainedRowSupport A.N old A.E j (.refl : BlowupTower Y Y) := by
        subst L
        rw [show k = jU from Fin.ext hk]
        exact hNew
      exact hReindex oldU hOld jm rfl
    have hMN : M.N = A.N := (chronologicalMarked_geometric_fields
      (originalRelativeMemberMarked W (E.get i)) T).1
    have hMUN : MU.N = B.N := (chronologicalMarked_geometric_fields
      (originalRelativeMemberMarked WU (EU.get (e i))) R).1
    have hF : retainedRowBoundary B.N oldU B.E jm
        (.refl : BlowupTower (CMfd.of (n := n) (openPreimage T U)) _) = oldU.eraseIdx (e i).val ++ B.E := by
      change (oldU.map id).eraseIdx (e i).val ++ B.E = _
      rw [List.map_id]
    have hS : retainedRowSupport B.N oldU B.E jm
        (.refl : BlowupTower (CMfd.of (n := n) (openPreimage T U)) _) = residualSupport WU EU R (e i) := by
      change (retainedResidualMarked B.N oldU B.E jm).N ∩
        (retainedResidualMarked B.N oldU B.E jm).ideal.zeroLocus = _
      rw [hSeedU,hMUN]
      rfl
    have hSrcSupp : retainedRowSupport A.N old A.E j (.refl : BlowupTower Y Y) =
        residualSupport W E T i := by
      change (retainedResidualMarked A.N old A.E j).N ∩
        (retainedResidualMarked A.N old A.E j).ideal.zeroLocus = _
      rw [hSeed,hMN]
      rfl
    obtain ⟨⟨hO,hN,hD⟩,hSupp⟩ := hNew'
    change (∀ x ∈ (retainedResidualMarked B.N oldU B.E jm).N,
      ordinaryTraceOrder (retainedResidualMarked B.N oldU B.E jm).N
        (retainedResidualMarked B.N oldU B.E jm).ideal x ≤ 1) at hO
    rw [hSeedU,hMUN] at hO
    rw [hS,hF] at hN hD
    rw [hS,hSrcSupp] at hSupp
    exact ⟨hO,hN,hD,hSupp⟩
  have hUO (x : openPreimage T U) (hx : x ∈ B.N) (i : Fin EU.length) :
      ordinaryTraceOrder B.N (chronologicalMarked (originalRelativeMemberMarked WU (EU.get i)) R).ideal x ≤ 1 := by
    obtain ⟨j,rfl⟩ := e.surjective i
    exact (hRows j).1 x hx
  have hUN (i : Fin EU.length) : HasNormalCrossings n (residualSupport WU EU R i)
      (oldU.eraseIdx i.val ++ B.E) := by
    obtain ⟨j,rfl⟩ := e.surjective i
    exact (hRows j).2.1
  have hUD (i : Fin EU.length) : residualSupport WU EU R i ⊆ closure
      (residualSupport WU EU R i \ ⋃ H ∈ oldU.eraseIdx i.val ++ B.E,H) := by
    obtain ⟨j,rfl⟩ := e.surjective i
    exact (hRows j).2.2.1
  have hUAt := actual_original_processed_joint_preparedness hn hWU hEU hDenseU
    R hRU hFullU hUO hUN hUD
  have hMatrix := (processed_mask_matrix_restrict hn hW hE hdense T hT hFull U).2
  refine ⟨⟨hRU,hFullU,hSharpU,hUO,hUN,hUD,hUAt,?_⟩,fun i => (hRows i).2.2.2⟩
  intro z hz
  rw [(hMatrix z).2.1]
  change z ∈ B.N at hz
  rw [hBU_N] at hz
  exact hBound z.val hz

end
end Hironaka.HironakaG4ProcessedStateRestriction
