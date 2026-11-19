import Hironaka.Resolution.HironakaG8NativeUniformClockRank
import Hironaka.Resolution.HironakaOriginalRecursiveEmptyDeletion
import Hironaka.Blowup.BlowupTowerIsoTail

/-! A single identity empty step removed from the shared ambient clock on
every original native window, keeping the same actual suffix. -/

set_option autoImplicit false
set_option maxHeartbeats 3600000

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeEmptyStepWindow

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealBiholomorphism MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaOriginalInteriorEmptyHistory HironakaOriginalRecursiveEmptyDeletion
  HironakaOriginalRecursiveBoundaryHistoryMap

variable {n : ℕ} {X A Y : CMfd.{0} n}

local notation "ref" B => Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞

/-- Restricting the shared identity empty step is the same identity
empty step on the literal restricted prefix. -/
private theorem restrict_interiorEmptyHistory_iso (U : Opens X)
    (H : BlowupTower X A) (S : BlowupTower A Y) :
    ∃ φ : CMfd.of (n := n) (openPreimage (interiorEmptyHistory H S) U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage S (openPreimage H U)),
      (∀ x, (φ x).val = x.val) ∧
      IsTowerIso (ref (CMfd.of (n := n) U)) (restrict U (interiorEmptyHistory H S))
        (interiorEmptyHistory (restrict U H) (restrict (openPreimage H U) S)) φ := by
  have hAppend := isTowerIso_restrict_append U
    (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S
  exact ⟨_,fun _ => rfl,hAppend⟩

/-- The two literal native restrictions share their endpoint points.
The original active value before deletion is the common chronological
shift of the value after deletion. -/
theorem original_window_identity_empty_deletion (hn : 0 < n) (k : ℕ) (U : Opens X)
    (M : MarkedIdeal n (CMfd.of (n := n) U)) (hM : IsInvDomain k M)
    (H : BlowupTower X A) (S : BlowupTower A Y)
    (hCan : IsCanonical M ((invFamily hn k).inv M) (restrict U (interiorEmptyHistory H S))) :
    IsCanonical M ((invFamily hn k).inv M) (restrict U (H.append S)) ∧
      ∀ (x : openPreimage (interiorEmptyHistory H S) U) (y : openPreimage (H.append S) U),
        x.val = y.val →
        (x ∈ (geoTransformAlong M (restrict U (interiorEmptyHistory H S))).cosupp ↔
          y ∈ (geoTransformAlong M (restrict U (H.append S))).cosupp) ∧
        (x ∈ (geoTransformAlong M (restrict U (interiorEmptyHistory H S))).cosupp →
          (invFamily hn k).inv M (restrict U (interiorEmptyHistory H S)) x =
            recursiveHistoryShift k (M.E.length + H.length)
              ((invFamily hn k).inv M (restrict U (H.append S)) y)) := by
  let I := interiorEmptyHistory H S
  let T := H.append S
  let HO := restrict U H
  let SO := restrict (openPreimage H U) S
  let RI := interiorEmptyHistory HO SO
  let RT := HO.append SO
  let φT := opensCongr (n := n) (openPreimage_append H S U).symm
  have hIsoT : IsTowerIso (ref (CMfd.of (n := n) U)) (restrict U T) RT φT :=
    isTowerIso_restrict_append U H S
  obtain ⟨φI,hφI,hIsoI⟩ := restrict_interiorEmptyHistory_iso U H S
  have hPull : MarkedIdeal.pullback (ref (CMfd.of (n := n) U)) M = M :=
    ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  have hCanI := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (invFamily hn k)
    hM _ hIsoI.symm hCan
  have hId : (ref (CMfd.of (n := n) U)).symm = ref (CMfd.of (n := n) U) :=
    Diffeomorph.ext fun _ => rfl
  rw [hId,hPull] at hCanI
  have hDelete := original_recursive_family_empty_deletion_entire_values hn k M hM HO SO hCanI
  have hCanT := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (invFamily hn k)
    hM _ hIsoT hDelete.1
  rw [hPull] at hCanT
  refine ⟨hCanT,?_⟩
  have hTestI := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hM RI hCanI
  have hTestT := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hM RT hDelete.1
  have hTestH := ((isGeoTestTower_append_iff M HO SO).mp hTestT).1
  have hGeo := (geometric_dictionary M hM.isWellFormed HO hTestH SO).2.2.2.1
  have hCosI := IsTowerIso.cosupp_geoTransformAlong (ref (CMfd.of (n := n) U))
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hIsoI hTestI
  have hCosT := IsTowerIso.cosupp_geoTransformAlong (ref (CMfd.of (n := n) U))
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hIsoT hTestT
  rw [hPull] at hCosI hCosT
  intro x y hxy
  have hφ : φI x = φT y := Subtype.ext ((hφI x).trans hxy)
  have hCos : x ∈ (geoTransformAlong M (restrict U I)).cosupp ↔
      y ∈ (geoTransformAlong M (restrict U T)).cosupp := by
    rw [hCosI,hCosT,mem_preimage,mem_preimage,hφ,hGeo]
  refine ⟨hCos,?_⟩
  intro hx
  have hx' : φI x ∈ (geoTransformAlong M RI).cosupp := by
    change x ∈ (geoTransformAlong M (restrict U I)).cosupp at hx
    rwa [hCosI] at hx
  have hy' : φT y ∈ (geoTransformAlong M RT).cosupp := by rw [← hφ,← hGeo]; exact hx'
  have hValueI := (invFamily hn k).isInvValue.towerIso (ref (CMfd.of (n := n) U)) M hM
    (restrict U I) RI φI hIsoI hCanI x hx'
  have hValueT := (invFamily hn k).isInvValue.towerIso (ref (CMfd.of (n := n) U)) M hM
    (restrict U T) RT φT hIsoT hDelete.1 y hy'
  rw [hPull] at hValueI hValueT
  have hValue := hDelete.2 (φI x) hx'
  rw [length_restrict] at hValue
  exact hValueI.trans (hValue.trans (by rw [hφ, hValueT]))

end
end Hironaka.HironakaG8NativeEmptyStepWindow
