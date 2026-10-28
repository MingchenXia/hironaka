/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointEmbeddedBoundaryLift
import Hironaka.Resolution.HironakaActualClosedContactBlowupRestriction
import Hironaka.Blowup.ExceptionalPushforwardAlong

/-! Literal whole boundary trace under an actual native strict-contact
comparison: every original index and the born exceptional member, then the
entire ordered list. No target trace or controlled-ideal certificate. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointStrictBoundaryTrace
noncomputable section
open Hironaka.BlowupSequences NormalCrossings BlowupStrictSubmanifold
  SubmanifoldChartedSpace HironakaActualClosedContactBlowupRestriction

private theorem preimage_strict_of_commuting {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (σ : Y → X) (ρ : Z → X) (F : Z ≃ₜ Y) (h : σ∘F=ρ) (D W : Set X) :
    F ⁻¹' geoStrictTransform σ D W=geoStrictTransform ρ D W := by
  change F ⁻¹' closure (σ ⁻¹' (W\D))=closure (ρ ⁻¹' (W\D))
  rw [F.preimage_closure]
  congr 1
  change (σ∘F) ⁻¹' (W\D)=ρ ⁻¹' (W\D)
  rw [h]

variable {d t : ℕ} {X Y Z : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
  {N : Set X} (hNc : IsClosed N)
  (hS : ∀ x∈N,RegularAtDim (n := d+t) N x d)
  {D : Set N} {π : Y → X} (hπ : IsBlowupAlong (d+t) ((Subtype.val : N → X) '' D) π)

omit [IsComplexManifold d Z] in
/-- Every original position, including an empty member, retains its exact
whole geometric strict trace through the SAME actual native comparison. -/
theorem every_original_strict_trace (hn : 0<d+t) {B : List (Set X)}
    (hB : IsSNCDivisor (d+t) B) (hT : IsTransverse (d+t) N B) :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    ∀ (ρ : Z → N),
    letI := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
    letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
    ∀ (F : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      geoStrictTransform π ((Subtype.val : N → X) '' D) N),
    restrictedProjection hNc D hπ∘F=ρ →
    HasNormalCrossings d D (B.map fun H => (Subtype.val : N → X) ⁻¹' H) →
    ∀ i : Fin B.length,
      F ⁻¹' ((Subtype.val : geoStrictTransform π ((Subtype.val : N → X) '' D) N → Y) ⁻¹'
        geoStrictTransform π ((Subtype.val : N → X) '' D) (B.get i))=
        geoStrictTransform ρ D ((Subtype.val : N → X) ⁻¹' B.get i) := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro ρ
  let := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
  let := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
  intro F hcomm hDNC i
  have hCN : (Subtype.val : N → X) '' D⊆N := by
    rintro _ ⟨p,_hp,rfl⟩; exact p.property
  have hNC := HironakaDisjointEmbeddedBoundaryLift.hasNormalCrossings_native_image hS hn hB hT D hDNC
  have himage := strictTransform_image hNc hπ ((Subtype.val : N → X) ⁻¹' B.get i)
  have hsource : (Subtype.val : N → X) '' ((Subtype.val : N → X) ⁻¹' B.get i)=B.get i∩N := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩; exact ⟨hp,p.property⟩
    · rintro ⟨hx,hxN⟩; exact ⟨⟨x,hxN⟩,hx,rfl⟩
  rw [hsource,ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hπ hNc hCN hB hT hNC i] at himage
  have htrace : (Subtype.val : geoStrictTransform π ((Subtype.val : N → X) '' D) N → Y) ⁻¹'
      geoStrictTransform π ((Subtype.val : N → X) '' D) (B.get i)=
      geoStrictTransform (restrictedProjection hNc D hπ) D ((Subtype.val : N → X) ⁻¹' B.get i) := by
    ext y
    constructor
    · intro hy
      have hymem : y.val∈(Subtype.val : geoStrictTransform π ((Subtype.val : N → X) '' D) N → Y) ''
          geoStrictTransform (restrictedProjection hNc D hπ) D ((Subtype.val : N → X) ⁻¹' B.get i) :=
        himage.symm ▸ ⟨hy,y.property⟩
      obtain ⟨z,hz,he⟩ := hymem
      have hzy : z=y := Subtype.ext he
      exact hzy ▸ hz
    · intro hy
      have hymem := himage ▸ Set.mem_image_of_mem (Subtype.val : geoStrictTransform π ((Subtype.val : N → X) '' D) N → Y) hy
      exact hymem.1
  rw [htrace]
  exact preimage_strict_of_commuting (restrictedProjection hNc D hπ) ρ F.toHomeomorph hcomm D _

omit [IsComplexManifold d Z] in
/-- The whole born exceptional member pulls back to the literal original
lower exceptional preimage, with no coordinate or ideal reduction. -/
theorem born_exceptional_trace :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    ∀ (ρ : Z → N),
    letI := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
    letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
    ∀ (F : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      geoStrictTransform π ((Subtype.val : N → X) '' D) N),
    restrictedProjection hNc D hπ∘F=ρ →
      F ⁻¹' ((Subtype.val : geoStrictTransform π ((Subtype.val : N → X) '' D) N → Y) ⁻¹'
        (π ⁻¹' ((Subtype.val : N → X) '' D)))=ρ ⁻¹' D := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro ρ
  let := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
  let := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
  intro F hcomm
  ext z
  have hbase : π (F z).val=(ρ z).val := congrArg Subtype.val (congrFun hcomm z)
  change π (F z).val∈(Subtype.val : N → X) '' D ↔ ρ z∈D
  rw [hbase]
  constructor
  · rintro ⟨p,hp,he⟩
    have he' : p=ρ z := Subtype.ext he
    exact he' ▸ hp
  · intro hz
    exact ⟨ρ z,hz,rfl⟩

omit [IsComplexManifold d Z] in
/-- Literal ordered list equality: ALL original strict slots followed by
exactly the born slot, without permutation or removal of empty members. -/
theorem whole_old_born_boundary_trace (hn : 0<d+t) {B : List (Set X)}
    (hB : IsSNCDivisor (d+t) B) (hT : IsTransverse (d+t) N B) :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    ∀ (ρ : Z → N),
    letI := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
    letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
    ∀ (F : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      geoStrictTransform π ((Subtype.val : N → X) '' D) N),
    restrictedProjection hNc D hπ∘F=ρ →
    HasNormalCrossings d D (B.map fun H => (Subtype.val : N → X) ⁻¹' H) →
      (B.map (geoStrictTransform π ((Subtype.val : N → X) '' D)) ++
        [π ⁻¹' ((Subtype.val : N → X) '' D)]).map (fun H => (fun z : Z => (F z).val) ⁻¹' H)=
      (B.map fun H => (Subtype.val : N → X) ⁻¹' H).map (geoStrictTransform ρ D) ++[ρ ⁻¹' D] := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro ρ
  let := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
  let := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
  intro F hcomm hDNC
  have hold := every_original_strict_trace hNc hS hπ hn hB hT ρ F hcomm hDNC
  have hborn := born_exceptional_trace hNc hS hπ ρ F hcomm
  rw [List.map_append,List.map_singleton,List.map_map,List.map_map]
  have heq : B.map (fun H => (fun z : Z => (F z).val) ⁻¹' geoStrictTransform π ((Subtype.val : N → X) '' D) H)=
      B.map (fun H => geoStrictTransform ρ D ((Subtype.val : N → X) ⁻¹' H)) := by
    apply List.map_congr_left
    intro H hH
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH
    subst H
    exact hold i
  simp only [Function.comp_def]
  rw [heq]
  exact congrArg (fun H => (B.map fun H => geoStrictTransform ρ D ((Subtype.val : N → X) ⁻¹' H)) ++ [H]) hborn

end
end Hironaka.HironakaDisjointStrictBoundaryTrace
