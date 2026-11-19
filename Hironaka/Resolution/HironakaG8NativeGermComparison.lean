import Hironaka.Resolution.HironakaG8CofinalLocalPointRank
import Hironaka.Resolution.HironakaG8LabelledNativeOverlap

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeGermComparison

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry
  HironakaG8OccupiedSlotComparison HironakaG8LabelledNativeHistory
  HironakaG8LabelledNativeOverlap HironakaG8CofinalLocalPointRank

theorem occupiedComparison_eq_of_first_footprint
    {n : ℕ} {X A Y B : CMfd.{0} n}
    {T : BlowupTower X Y} {S : BlowupTower A B}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    (h : EmptyAwareTowerIso φ T S ψ)
    (p : {k // Occupied T k}) (q : {k // Occupied S k})
    (hFoot : slotFootprint T p.val = φ ⁻¹' slotFootprint S q.val)
    (hFirstLeft : ∀ r : {k // Occupied T k},
      slotFootprint T r.val = slotFootprint T p.val → p ≤ r)
    (hFirstRight : ∀ r : {k // Occupied S k},
      slotFootprint S r.val = slotFootprint S q.val → q ≤ r) :
    occupiedComparison h p = q := by
  let e := occupiedComparison h
  have hMark (r : {k // Occupied T k}) :
      slotFootprint T r.val = slotFootprint T p.val ↔
        slotFootprint S (e r).val = slotFootprint S q.val := by
    rw [slotFootprint_occupiedComparison h r,hFoot]
    exact φ.surjective.preimage_injective.eq_iff
  apply le_antisymm
  · have hLeft := hFirstLeft (e.symm q) ((hMark _).mpr (by rw [e.apply_symm_apply]))
    have hLe := e.monotone hLeft
    simpa only [e.apply_symm_apply] using hLe
  · exact hFirstRight (e p) ((hMark p).mp rfl)

theorem no_self_comparison_between_distinct_occurrences
    {n : ℕ} {X Y : CMfd.{0} n} {T : BlowupTower X Y}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : EmptyAwareTowerIso φ T T ψ) (p q : {k // Occupied T k}) (hne : p ≠ q) :
    occupiedComparison h p ≠ q := by
  have he : occupiedComparison h = OrderIso.refl _ := occupied_orderIso_unique _ _
  simpa only [he,OrderIso.refl_apply] using hne

theorem first_footprint_of_no_earlier_local_equality
    {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y) (U : Opens X)
    (x : U) (p : {k // Occupied (restrict U T) k})
    (hFresh : ∀ k < p.val, ¬ ∀ᶠ z in nhds x.val,
      (z ∈ slotFootprint T k ↔ z ∈ slotFootprint T p.val)) :
    ∀ r : {k // Occupied (restrict U T) k},
      slotFootprint (restrict U T) r.val = slotFootprint (restrict U T) p.val → p ≤ r := by
  intro r hEq
  by_contra hn
  have hr : r.val < p.val := lt_of_not_ge hn
  apply hFresh r.val hr
  rw [slotFootprint_restrict,slotFootprint_restrict] at hEq
  filter_upwards [U.isOpen.mem_nhds x.property] with z hz
  exact Set.ext_iff.mp hEq (⟨z,hz⟩ : U)

theorem exists_selected_native_germ_comparison
    {n : ℕ} (hn : 0 < n) {X X' Y Y' : CMfd.{0} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')}
    (hCarrier : W' = φ ⁻¹' W)
    (hBoundary : E'.filter (fun B => decide B.Nonempty) =
      (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hDense' : W' ⊆ closure (W' \ ⋃ B ∈ E', B))
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {L L' : List (ℕ → ℕ)}
    (hLeft : LabelledNativeTower n W' E' univ T' L')
    (hRight : LabelledNativeTower n W E univ T L)
    (p : {k // Occupied T' k}) (q : {k // Occupied T k})
    (hFoot : slotFootprint T' p.val = φ ⁻¹' slotFootprint T q.val)
    (hFirstLeft : ∀ r : {k // Occupied T' k},
      slotFootprint T' r.val = slotFootprint T' p.val → p ≤ r)
    (hFirstRight : ∀ r : {k // Occupied T k},
      slotFootprint T r.val = slotFootprint T q.val → q ≤ r) :
    ∃ (ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
      (h : EmptyAwareTowerIso φ T' T ψ), occupiedComparison h p = q := by
  obtain ⟨ψ,h⟩ := labelled_native_history_overlap hn φ hCarrier hBoundary hDense' hDense hLeft hRight
  exact ⟨ψ,h,occupiedComparison_eq_of_first_footprint h p q hFoot hFirstLeft hFirstRight⟩

open HironakaG3RTowerClass

theorem localPointComparison_of_native_germ_first_footprint
    {n : ℕ} (hn : 0 < n) {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {I : Type*} (Evs : CofinalEvents c I)
    (i j : ℕ) (U : Opens (c i).U) (V : Opens (c j).U)
    (W : Set (c i).U) (W' : Set (c j).U)
    (B : List (Set (c i).U)) (B' : List (Set (c j).U))
    (L L' : List (ℕ → ℕ))
    (hLeft : LabelledNativeTower n W B univ (c i).T L)
    (hRight : LabelledNativeTower n W' B' univ (c j).T L')
    (φ : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (hCarrier : (Subtype.val : U → (c i).U) ⁻¹' W =
      φ ⁻¹' ((Subtype.val : V → (c j).U) ⁻¹' W'))
    (hBoundary : (B.map ((Subtype.val : U → (c i).U) ⁻¹' ·)).filter (fun D => decide D.Nonempty) =
      ((B'.map ((Subtype.val : V → (c j).U) ⁻¹' ·)).map (φ ⁻¹' ·)).filter
        (fun D => decide D.Nonempty))
    (hDenseLeft : (Subtype.val : U → (c i).U) ⁻¹' W ⊆
      closure (((Subtype.val : U → (c i).U) ⁻¹' W) \
        ⋃ D ∈ B.map ((Subtype.val : U → (c i).U) ⁻¹' ·), D))
    (hDenseRight : (Subtype.val : V → (c j).U) ⁻¹' W' ⊆
      closure (((Subtype.val : V → (c j).U) ⁻¹' W') \
        ⋃ D ∈ B'.map ((Subtype.val : V → (c j).U) ⁻¹' ·), D))
    (p : {k // Occupied (restrict U (c i).T) k})
    (q : {k // Occupied (restrict V (c j).T) k})
    (hFoot : slotFootprint (restrict U (c i).T) p.val =
      φ ⁻¹' slotFootprint (restrict V (c j).T) q.val)
    (hFirstLeft : ∀ r : {k // Occupied (restrict U (c i).T) k},
      slotFootprint (restrict U (c i).T) r.val = slotFootprint (restrict U (c i).T) p.val → p ≤ r)
    (hFirstRight : ∀ r : {k // Occupied (restrict V (c j).T) k},
      slotFootprint (restrict V (c j).T) r.val = slotFootprint (restrict V (c j).T) q.val → q ≤ r)
    (a : I)
    (hEventLeft : Evs.event i (occupiedRestrictionEmbedding U (c i).T p) = a)
    (hEventRight : Evs.event j (occupiedRestrictionEmbedding V (c j).T q) = a)
    (x : U) :
    Nonempty (LocalPointComparison Evs a x.val.val (φ x).val.val) := by
  have hL : LabelledNativeTower n ((Subtype.val : U → (c i).U) ⁻¹' W)
      (B.map ((Subtype.val : U → (c i).U) ⁻¹' ·)) univ (restrict U (c i).T) L := by
    simpa only [preimage_univ] using hLeft.restrictOpen U
  have hR : LabelledNativeTower n ((Subtype.val : V → (c j).U) ⁻¹' W')
      (B'.map ((Subtype.val : V → (c j).U) ⁻¹' ·)) univ (restrict V (c j).T) L' := by
    simpa only [preimage_univ] using hRight.restrictOpen V
  obtain ⟨ψ,h,hpq⟩ := exists_selected_native_germ_comparison hn φ hCarrier hBoundary
    hDenseLeft hDenseRight hL hR p q hFoot hFirstLeft hFirstRight
  exact ⟨{
    leftIndex := i
    rightIndex := j
    leftOpen := U
    rightOpen := V
    base := φ
    endpoint := ψ
    compare := h
    slot := p
    point := x
    point_eq := rfl
    base_point_eq := rfl
    left_event := hEventLeft
    right_event := by rw [hpq]; exact hEventRight }⟩

end
end Hironaka.HironakaG8NativeGermComparison
