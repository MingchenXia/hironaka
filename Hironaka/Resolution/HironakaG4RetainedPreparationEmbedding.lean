import Hironaka.Resolution.HironakaG4RetainedPreparedDefectRerun
import Hironaka.Resolution.HironakaG34ProfileWindowNaturality

/-! The current prepared row is local under an actual open holomorphic embedding. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparationEmbedding
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings HironakaBaseChange HironakaG34JointMaskEquivariance HironakaG34ProfileWindowNaturality
  HironakaActualRetainedBornResidualSeed HironakaG4PreparedCentreCoordinates
  HironakaG4OrderedRetainedDefectTrace HironakaG4RetainedPreparedLocalSupport
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteChronologicalHistory
  HironakaActualRetainedBornResidualHistory HironakaG4RetainedPreparedDefectRerun

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 650000 in
/-- A prepared native row remains prepared under an actual open holomorphic
embedding, and its support pulls back under that same map. -/
theorem retained_preparation_pullback_open_embedding (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i : Fin old.length) (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    (f : Y → X) (hf : IsOpenHoloEmbedding n f) :
    let N' := f ⁻¹' N
    let O' := old.map (f ⁻¹' ·)
    let B' := born.map (f ⁻¹' ·)
    let j : Fin O'.length := Fin.cast (List.length_map _).symm i
    RetainedRowPrepared N' O' B' j (.refl : BlowupTower Y Y) ∧
      retainedRowSupport N' O' B' j (.refl : BlowupTower Y Y) =
        f ⁻¹' retainedRowSupport N old born i (.refl : BlowupTower X X) := by
  intro N' O' B' j
  let J := oldResidualPart N old born i
  let J' := oldResidualPart N' O' B' j
  let S := retainedRowSupport N old born i (.refl : BlowupTower X X)
  let S' := retainedRowSupport N' O' B' j (.refl : BlowupTower Y Y)
  let F := retainedRowBoundary N old born i (.refl : BlowupTower X X)
  let F' := retainedRowBoundary N' O' B' j (.refl : BlowupTower Y Y)
  have hSeed := retainedResidualMarked_geometry hn g.carrier g.full g.born_transverse g.dense i
  have hJ : GermIdeal.pullback (m := n) f J = J' := by
    have hGet : O'.get j = f ⁻¹' old.get i := by simp [O',j]
    unfold J J' oldResidualPart oldTraceIdeal
    rw [hGet]
    exact pullback_residual hf hn g.carrier g.full g.born_transverse g.dense i
  have hS : S' = f ⁻¹' S := by
    change N' ∩ J'.zeroLocus = f ⁻¹' (N ∩ J.zeroLocus)
    rw [←hJ]
    exact congrArg (fun A => N' ∩ A) (BlowupExceptionalDivisor.zeroLocus_pullback hf.contMDiff hSeed.1.isCoherent)
  have hF : F' = F.map (f ⁻¹' ·) := by
    change (O'.map id).eraseIdx i.val ++ B' = ((old.map id).eraseIdx i.val ++ born).map (f ⁻¹' ·)
    rw [List.map_id,List.map_id,List.map_append,List.eraseIdx_map]
  refine ⟨⟨?_,?_,?_⟩,hS⟩
  · intro y hy
    obtain ⟨U,φ,hφ⟩ := hf
    have hPhi : f = (Subtype.val : U → X) ∘ φ := funext hφ
    have hOrd := ordinary_order_pullback_open_iso hn g.carrier hSeed.1.isCoherent hSeed.2.1 U φ y
    rw [←hPhi] at hOrd
    change ordinaryTraceOrder (X := Y) N' (GermIdeal.pullback (m := n) f J) y =
      ordinaryTraceOrder N J (φ y).val at hOrd
    rw [hJ] at hOrd
    change ordinaryTraceOrder N' J' y ≤ 1
    rw [hOrd,←hφ]
    exact hPrep.1 (f y) hy
  · change HasNormalCrossings n S' F'
    rw [hS,hF]
    exact hf.hasNormalCrossings_preimage hPrep.2.1
  · change S' ⊆ closure (S' \ ⋃ H ∈ F',H)
    rw [hS,hF,←HironakaEmbeddedBoundary.preimage_biUnion_list,←preimage_sdiff,←hf.preimage_closure]
    exact preimage_mono hPrep.2.2

private theorem retained_state_eq_of_tuple_eq {N N' : Set X}
    {old old' born born' : List (Set X)} {i : Fin old.length} {j : Fin old'.length}
    (hN : N = N') (hO : old = old') (hB : born = born') (hIndex : i.val = j.val) :
    (RetainedRowPrepared N old born i (.refl : BlowupTower X X) ↔
      RetainedRowPrepared N' old' born' j (.refl : BlowupTower X X)) ∧
    retainedRowSupport N old born i (.refl : BlowupTower X X) =
      retainedRowSupport N' old' born' j (.refl : BlowupTower X X) := by
  subst N'
  subst old'
  subst born'
  have hij : i = j := Fin.ext hIndex
  subst j
  exact ⟨Iff.rfl,rfl⟩

set_option maxHeartbeats 650000 in
/-- The actual endpoint pulls back a prepared row and its support when
the current carrier, ordered old traces and ordered born boundary pull
back through the given open embedding. -/
theorem retained_preparation_of_endpoint_open_embedding (hn : 0 < n)
    {n₁ : Set X} {old₁ born₁ : List (Set X)} (g₁ : NativeRetainedGeometry n₁ old₁ born₁)
    {X' Y' : CMfd.{u} n} {n₂ : Set X'} {old₂ born₂ : List (Set X')}
    (g₂ : NativeRetainedGeometry n₂ old₂ born₂)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate n₁ born₁) T)
    (hFT : IsGeoTestTower (geometricTemplate (univ : Set X) (old₁ ++ born₁)) T)
    (S : BlowupTower X' Y') (hS : IsGeoTestTower (geometricTemplate n₂ born₂) S)
    (hFS : IsGeoTestTower (geometricTemplate (univ : Set X') (old₂ ++ born₂)) S)
    (f : Y' → Y) (hf : IsOpenHoloEmbedding n f) (i : Fin old₁.length) (j : Fin old₂.length)
    (hIndex : i.val = j.val) :
    let AT := geoTransformAlong (geometricTemplate n₁ born₁) T
    let AS := geoTransformAlong (geometricTemplate n₂ born₂) S
    let OT := old₁.map (strictAlong T)
    let OS := old₂.map (strictAlong S)
    AS.N = f ⁻¹' AT.N → OS = OT.map (f ⁻¹' ·) → AS.E = AT.E.map (f ⁻¹' ·) →
    RetainedRowPrepared n₁ old₁ born₁ i T →
    RetainedRowPrepared n₂ old₂ born₂ j S ∧
    retainedRowSupport n₂ old₂ born₂ j S = f ⁻¹' retainedRowSupport n₁ old₁ born₁ i T := by
  intro AT AS OT OS hN hO hB hPrep
  let iT : Fin OT.length := Fin.cast (List.length_map _).symm i
  let jS : Fin OS.length := Fin.cast (List.length_map _).symm j
  have hRec := actual_retained_born_recorded_residual_dictionary hn g₁.carrier g₁.full
    g₁.born_transverse g₁.dense T hT hFT
  have hGT : NativeRetainedGeometry AT.N OT AT.E := ⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩
  have hAtT := retained_preparation_current_readback hn g₁ i T hT hFT
  have hAtS := retained_preparation_current_readback hn g₂ j S hS hFS
  have hPull := retained_preparation_pullback_open_embedding hn hGT iT (hAtT.1.mp hPrep) f hf
  let iPull : Fin (OT.map (f ⁻¹' ·)).length := Fin.cast (List.length_map _).symm iT
  have hEq := retained_state_eq_of_tuple_eq (i := jS) (j := iPull) hN hO hB hIndex.symm
  exact ⟨hAtS.1.mpr (hEq.1.mpr hPull.1),hAtS.2.trans (hEq.2.trans
    (hPull.2.trans (congrArg (fun W => f ⁻¹' W) hAtT.2.symm)))⟩

end
end Hironaka.HironakaG4RetainedPreparationEmbedding
