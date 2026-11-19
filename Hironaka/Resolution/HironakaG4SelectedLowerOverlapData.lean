import Hironaka.Resolution.HironakaG4OrderedCrestEmptyBorn
import Hironaka.Resolution.HironakaG4RetainedRankTowerIso
import Hironaka.Resolution.HironakaG4RetainedTraceComparison
import Hironaka.Resolution.HironakaG4FullBoundaryCompactCleanup
import Hironaka.Resolution.HironakaG3BoundaryStoppingOpenRestriction
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal

/-! The selected lower problem on physically identified retained prefixes. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SelectedLowerOverlapData

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaG4OrderedRetainedDefectTrace
  HironakaActualRetainedBornResidualHistory HironakaG4PreparedCentreCoordinates
  HironakaG4OrderedCrestEmptyBorn HironakaG4RetainedRankTowerIso HironakaG34JointMaskEquivariance
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareBornSlots HironakaG4RetainedTraceComparison
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4FullBoundaryCompactCleanup
  HironakaG3BoundaryStoppingOpenRestriction HironakaG34NonPureLowDim
  HironakaActualOpenEmbeddingVanishingIdeal HironakaSharpNormalCrossingsOpenLocus NormalCrossings

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private theorem filter_selected_position {α : Type*} (keep : α → Bool)
    (xs : List α) (i : Fin xs.length) (hKeep : keep (xs.get i)) :
    let k := ((xs.take i.val).filter keep).length
    (xs.filter keep)[k]? = some (xs.get i) ∧
      (xs.filter keep).eraseIdx k = (xs.eraseIdx i.val).filter keep := by
  intro k
  have hSplit : xs.filter keep = (xs.take i.val).filter keep ++
      (xs.get i :: (xs.drop (i.val + 1)).filter keep) := by
    have hList : xs = xs.take i.val ++ (xs.get i :: xs.drop (i.val + 1)) := by
      rw [List.get_eq_getElem, ← List.drop_eq_getElem_cons i.isLt, List.take_append_drop]
    calc
      _ = (xs.take i.val ++ (xs.get i :: xs.drop (i.val + 1))).filter keep :=
        congrArg (List.filter keep) hList
      _ = _ := by simp only [List.filter_append, List.filter_cons, hKeep, ↓reduceIte]
  constructor
  · rw [hSplit, List.getElem?_append_right (show ((xs.take i.val).filter keep).length ≤ k from le_rfl)]
    simp [k]
  · rw [hSplit, List.eraseIdx_append_of_length_le (show ((xs.take i.val).filter keep).length ≤ k from le_rfl)]
    simp [k, List.eraseIdx_eq_take_drop_succ]

/-- Selected live rows at the same position in the filtered old list
agree, and their deletion leaves the same filtered chronological list. -/
theorem matched_old_rows_of_live_positions
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {old : List (Set X)} {old' : List (Set X')}
    (hOld : liveBorn old' = (liveBorn old).map (e ⁻¹' ·))
    (j : Fin old.length) (j' : Fin old'.length)
    (hLive : (old.get j).Nonempty) (hLive' : (old'.get j').Nonempty)
    (hPos : (liveBorn (old'.take j'.val)).length = (liveBorn (old.take j.val)).length) :
    old'.get j' = e ⁻¹' old.get j ∧
      liveBorn (old'.eraseIdx j'.val) = (liveBorn (old.eraseIdx j.val)).map (e ⁻¹' ·) := by
  let k := (liveBorn (old.take j.val)).length
  obtain ⟨hGet,hErase⟩ := filter_selected_position (fun H : Set X => decide H.Nonempty) old j (decide_eq_true hLive)
  obtain ⟨hGet',hErase'⟩ := filter_selected_position (fun H : Set X' => decide H.Nonempty) old' j' (decide_eq_true hLive')
  change (liveBorn old)[k]? = _ at hGet
  change (liveBorn old).eraseIdx k = _ at hErase
  change (liveBorn old')[(liveBorn (old'.take j'.val)).length]? = _ at hGet'
  change (liveBorn old').eraseIdx (liveBorn (old'.take j'.val)).length = _ at hErase'
  rw [hPos, hOld, List.getElem?_map, hGet, Option.map_some] at hGet'
  rw [hPos, hOld, List.eraseIdx_map, hErase] at hErase'
  exact ⟨(Option.some.inj hGet').symm,hErase'.symm⟩

/-- Literal row correspondence is a special case of the matching row
and complement-list data, even when that selected slot is empty. -/
theorem matched_old_rows_of_literal
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {old : List (Set X)} {old' : List (Set X')}
    (hOld : old' = old.map (e ⁻¹' ·))
    (j : Fin old.length) (j' : Fin old'.length) (hIndex : j'.val = j.val) :
    old'.get j' = e ⁻¹' old.get j ∧
      liveBorn (old'.eraseIdx j'.val) = (liveBorn (old.eraseIdx j.val)).map (e ⁻¹' ·) := by
  subst old'
  let j₀ : Fin (old.map (e ⁻¹' ·)).length := Fin.cast (List.length_map _).symm j
  have hj : j' = j₀ := Fin.ext hIndex
  subst j'
  constructor
  · simp [j₀]
  · change liveBorn ((old.map (e ⁻¹' ·)).eraseIdx j.val) = _
    simpa only [List.eraseIdx_map] using
      filter_map_bijection e e.surjective (old.eraseIdx j.val)

/-- The same selected retained row determines the lower residual input,
even when the old lists have different empty slots. Erasing corresponding
selected rows preserves the ordered nonempty lower boundary. -/
theorem selected_lower_data_of_matched_old_rows (hn : 0 < n)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')}
    (hN : N' = e ⁻¹' N)
    (hBorn : liveBorn born' = (liveBorn born).map (e ⁻¹' ·))
    (j : Fin old.length) (j' : Fin old'.length)
    (hRow : old'.get j' = e ⁻¹' old.get j)
    (hRest : liveBorn (old'.eraseIdx j'.val) = (liveBorn (old.eraseIdx j.val)).map (e ⁻¹' ·)) :
    GermIdeal.pullback (m := n) e (oldResidualPart N old born j) = oldResidualPart N' old' born' j' ∧
    N' ∩ (oldResidualPart N' old' born' j').zeroLocus =
      e ⁻¹' (N ∩ (oldResidualPart N old born j).zeroLocus) ∧
    liveBorn (old'.eraseIdx j'.val ++ born') =
      (liveBorn (old.eraseIdx j.val ++ born)).map (e ⁻¹' ·) := by
  subst N'
  let f : Set X → Set X' := (e ⁻¹' ·)
  have hfilt : (born.map f).filter (fun H => decide H.Nonempty) =
      born'.filter (fun H => decide H.Nonempty) :=
    (filter_map_bijection e e.surjective born).trans hBorn.symm
  have hGeom := pullback_residual (isOpenHoloEmbedding_diffeomorph e) hn
    g.carrier g.full g.born_transverse g.dense j
  have hNative : GermIdeal.pullback (m := n) e (oldResidualPart N old born j) =
      oldResidualPart (e ⁻¹' N) old' (born.map f) j' := by
    unfold oldResidualPart oldTraceIdeal
    rw [hRow]
    exact hGeom
  have hResidual : GermIdeal.pullback (m := n) e (oldResidualPart N old born j) =
      oldResidualPart (e ⁻¹' N) old' born' j' := by
    rw [hNative, ← oldResidualPart_filter_empty_born (e ⁻¹' N) old' (born.map f),
      hfilt, oldResidualPart_filter_empty_born]
  have hCoh := (actual_old_parts_geometry hn g.carrier g.full g.born_transverse g.dense j).2.2.1
  refine ⟨hResidual, ?_, ?_⟩
  · rw [← hResidual, BlowupExceptionalDivisor.zeroLocus_pullback e.contMDiff hCoh, preimage_inter]
  · change liveBorn (old'.eraseIdx j'.val ++ born') = (liveBorn (old.eraseIdx j.val ++ born)).map f
    simp only [liveBorn, List.filter_append, List.map_append] at hRest hBorn ⊢
    rw [hRest,hBorn]

/-- On matched endpoint data the selected old row has the same actual
residual ideal and carrier support under pullback. Removing its literal
old slot leaves the same ordered nonempty lower boundary. -/
theorem selected_lower_data_under_endpoint (hn : 0 < n)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')}
    (hN : N' = e ⁻¹' N) (hOld : old' = old.map (e ⁻¹' ·))
    (hBorn : born'.filter (fun H => decide H.Nonempty) =
      (born.filter (fun H => decide H.Nonempty)).map (e ⁻¹' ·))
    (j : Fin old.length) (j' : Fin old'.length) (hIndex : j'.val = j.val) :
    GermIdeal.pullback (m := n) e (oldResidualPart N old born j) = oldResidualPart N' old' born' j' ∧
    N' ∩ (oldResidualPart N' old' born' j').zeroLocus =
      e ⁻¹' (N ∩ (oldResidualPart N old born j).zeroLocus) ∧
    (old'.eraseIdx j'.val ++ born').filter (fun H => decide H.Nonempty) =
      ((old.eraseIdx j.val ++ born).filter (fun H => decide H.Nonempty)).map (e ⁻¹' ·) := by
  obtain ⟨hRow,hRest⟩ := matched_old_rows_of_literal e hOld j j' hIndex
  exact selected_lower_data_of_matched_old_rows hn e g hN hBorn j j' hRow hRest

/-- A physical comparison of actual upper prefixes identifies the
lower problem of the same original old boundary index. Empty born
stages may occur independently in the two prefixes. -/
theorem selected_lower_data_of_emptyAware_prefix (hn : 0 < n)
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : EmptyAwareTowerIso φ T' T ψ)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    {born' : List (Set X')}
    (hBorn : born'.filter (fun H => decide H.Nonempty) =
      (born.filter (fun H => decide H.Nonempty)).map (φ ⁻¹' ·))
    (j : Fin old.length) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let A' := geoTransformAlong (geometricTemplate (φ ⁻¹' N) born') T'
    let O := old.map (strictAlong T)
    let O' := (old.map (φ ⁻¹' ·)).map (strictAlong T')
    let i : Fin O.length := ⟨j.val, by simpa only [O,List.length_map] using j.isLt⟩
    let i' : Fin O'.length := ⟨j.val, by simpa only [O',List.length_map] using j.isLt⟩
    GermIdeal.pullback (m := n) ψ (oldResidualPart A.N O A.E i) = oldResidualPart A'.N O' A'.E i' ∧
    A'.N ∩ (oldResidualPart A'.N O' A'.E i').zeroLocus =
      ψ ⁻¹' (A.N ∩ (oldResidualPart A.N O A.E i).zeroLocus) ∧
    (O'.eraseIdx i'.val ++ A'.E).filter (fun H => decide H.Nonempty) =
      ((O.eraseIdx i.val ++ A.E).filter (fun H => decide H.Nonempty)).map (ψ ⁻¹' ·) := by
  intro A A' O O' i i'
  obtain ⟨hN,hOld,hBorn'⟩ := retained_inputs_of_emptyAware g rfl rfl hBorn hIso
  have hRec := actual_retained_born_recorded_residual_dictionary hn g.carrier g.full
    g.born_transverse g.dense T hT hFull
  have gCurrent : NativeRetainedGeometry A.N O A.E := ⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩
  exact selected_lower_data_under_endpoint hn ψ gCurrent hN hOld hBorn' i i' rfl

/-- The same selected carrier and nonempty lower boundary identify the
whole original mark-one lower problem and the marked-stratum boundary
union used by its canonical history. -/
theorem lower_marked_input_under_filtered_boundary
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {L : Set X} {F : List (Set X)} {L' : Set X'} {F' : List (Set X')}
    (hL : L' = e ⁻¹' L)
    (hF : F'.filter (fun B => decide B.Nonempty) =
      (F.filter (fun B => decide B.Nonempty)).map (e ⁻¹' ·)) :
    let B := originalSharpBadLocus (n := n) L F
    let B' := originalSharpBadLocus (n := n) L' F'
    let M : MarkedIdeal n X := ⟨L,[],vanishingIdeal (n := n) B,1⟩
    let M' : MarkedIdeal n X' := ⟨L',[],vanishingIdeal (n := n) B',1⟩
    B' = e ⁻¹' B ∧ MarkedIdeal.pullback e M = M' ∧
      (⋃ G ∈ F', G) = e ⁻¹' (⋃ G ∈ F, G) := by
  intro B B' M M'
  have hBad : B' = e ⁻¹' B := by
    ext x
    change (x ∈ L' ∧ ¬normalCrossingsAt (n := n) L' F' x) ↔
      (e x ∈ L ∧ ¬normalCrossingsAt (n := n) L F (e x))
    rw [hL]
    refine and_congr Iff.rfl (not_congr ?_)
    rw [← normalCrossingsAt_filter_nonempty_iff _ F' x,
      ← normalCrossingsAt_filter_nonempty_iff _ F (e x),hF]
    exact ⟨normalCrossingsAt_of_preimage_diffeo e,normalCrossingsAt_preimage_diffeo e⟩
  refine ⟨hBad,?_,?_⟩
  · change (MarkedIdeal.mk (e ⁻¹' L) []
      (GermIdeal.pullback (m := n) e (vanishingIdeal (n := n) B)) 1 : MarkedIdeal n X') = M'
    rw [pullback_vanishingIdeal_of_biholomorphism,← hL,← hBad]
  · calc
      (⋃ G ∈ F', G) = ⋃ G ∈ F'.filter (fun H => decide H.Nonempty), G :=
        (biUnion_nonempty_filter F').symm
      _ = ⋃ G ∈ (F.filter (fun H => decide H.Nonempty)).map (e ⁻¹' ·), G := by rw [hF]
      _ = e ⁻¹' (⋃ G ∈ F.filter (fun H => decide H.Nonempty), G) :=
        (HironakaEmbeddedBoundary.preimage_biUnion_list _ _).symm
      _ = e ⁻¹' (⋃ G ∈ F, G) := by rw [biUnion_nonempty_filter]

end
end Hironaka.HironakaG4SelectedLowerOverlapData
