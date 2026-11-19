import Hironaka.Resolution.HironakaG8OccupiedSlotComparison

/-! The actual direct occupied lifts compose along nested physical charts. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NestedOccupiedSlotComparison

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry
  HironakaG8OccupiedSlotComparison

variable {n : ℕ} {A B C X Y Z : CMfd.{0} n}

/-- Under a physical overlap into the larger chart, a raw slot occupies
the smaller window exactly when its larger counterpart occupies the
literal nested restriction of that chart. -/
theorem occupied_visibility_in_nested_chart
    {S : BlowupTower B Y} (R : BlowupTower C Z)
    (U : Opens B) (V D : Opens C) (hDV : D ≤ V)
    {φ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R V)}
    (h : EmptyAwareTowerIso φ S (restrict V R) ψ)
    (hU : (U : Set B) = (Subtype.val ∘ φ) ⁻¹' (D : Set C))
    (i : {k // Occupied S k}) :
    Occupied (restrict U S) i.val ↔
      Occupied (restrict D R) (occupiedLiftOnOpen V R h i).val := by
  let j := occupiedComparison h i
  have hF := slotFootprint_occupiedComparison h i
  rw [slotFootprint_restrict] at hF
  change slotFootprint S i.val = (Subtype.val ∘ φ) ⁻¹' slotFootprint R j.val at hF
  rw [occupied_restrict_iff_slotFootprint_meets,occupied_restrict_iff_slotFootprint_meets,hF,hU]
  change ((Subtype.val ∘ φ) ⁻¹' slotFootprint R j.val ∩
      (Subtype.val ∘ φ) ⁻¹' (D : Set C)).Nonempty ↔
    (slotFootprint R j.val ∩ (D : Set C)).Nonempty
  constructor
  · rintro ⟨b,hb,hbD⟩
    exact ⟨(φ b).val,hb,hbD⟩
  · rintro ⟨c,hc,hcD⟩
    obtain ⟨b,hb⟩ := φ.surjective ⟨c,hDV hcD⟩
    change φ b = ⟨c,hDV hcD⟩ at hb
    refine ⟨b,?_,?_⟩
    · change (φ b).val ∈ slotFootprint R j.val
      rwa [hb]
    · change (φ b).val ∈ D
      rwa [hb]

/-- The direct occupied lift agrees with the composite along genuine nested
physical windows. All three supplied comparisons are actual empty-aware
overlap theorems, and their endpoint maps need no extra coherence premise. -/
theorem occupiedLiftOnOpen_comp_nested
    {T : BlowupTower A X} (S : BlowupTower B Y) (R : BlowupTower C Z)
    (U : Opens B) (V D : Opens C) (hDV : D ≤ V)
    {φ₁ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U}
    {ψ₁ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S U)}
    {φ₂ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {ψ₂ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R V)}
    {φ₃ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) D}
    {ψ₃ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R D)}
    (h₁ : EmptyAwareTowerIso φ₁ T (restrict U S) ψ₁)
    (h₂ : EmptyAwareTowerIso φ₂ S (restrict V R) ψ₂)
    (h₃ : EmptyAwareTowerIso φ₃ T (restrict D R) ψ₃)
    (hU : (U : Set B) = (Subtype.val ∘ φ₂) ⁻¹' (D : Set C)) :
    (occupiedLiftOnOpen U S h₁).trans (occupiedLiftOnOpen V R h₂) =
      occupiedLiftOnOpen D R h₃ := by
  apply occupied_orderEmbedding_unique_of_range
  ext j
  rw [mem_range_occupiedLiftOnOpen D R h₃]
  constructor
  · rintro ⟨i,rfl⟩
    let b := occupiedLiftOnOpen U S h₁ i
    have hb : Occupied (restrict U S) b.val :=
      (mem_range_occupiedLiftOnOpen U S h₁ b).mp ⟨i,rfl⟩
    exact (occupied_visibility_in_nested_chart R U V D hDV h₂ hU b).mp hb
  · intro hj
    have hjV : Occupied (restrict V R) j.val := by
      rw [occupied_restrict_iff_slotFootprint_meets] at hj ⊢
      exact hj.mono (inter_subset_inter_right _ hDV)
    obtain ⟨b,rfl⟩ := (mem_range_occupiedLiftOnOpen V R h₂ j).mpr hjV
    have hb := (occupied_visibility_in_nested_chart R U V D hDV h₂ hU b).mpr hj
    obtain ⟨a,rfl⟩ := (mem_range_occupiedLiftOnOpen U S h₁ b).mpr hb
    exact ⟨a,rfl⟩

end Hironaka.HironakaG8NestedOccupiedSlotComparison
