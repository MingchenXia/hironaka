/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalPureBoundaryIndependentSource
import Hironaka.Resolution.HironakaEmbeddedAnalytic

/-!
# Actual ordered dimension parts in smooth canonical recursion

The original intrinsic whole dimension parts, all-dimensional singular set
and increasing nonempty labelled list are transported by a genuine smooth
submersion.  Empty sources are handled without a false ambient-dimension bound.

Blueprint: `hironaka-original-canonical-dimension-list-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalCanonicalDimensionList

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers
  HironakaEmbeddedDimensionParts HironakaEmbeddedAnalytic
  HironakaOriginalSmoothIntrinsicRegularLoci HironakaSmoothSubmersionRelativeGeometry

variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {b : Y → X}

/-- Actual whole intrinsic dimension parts, with the genuine relative dimension. -/
theorem dimensionPart_preimage_eq_shift
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) (k : ℕ) :
    dimensionPart (n := m) (b ⁻¹' W) (k+(m-n)) = b ⁻¹' dimensionPart (n := n) W k := by
  unfold dimensionPart
  rw [regularLocus_preimage_eq hb W k]
  exact (HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
    |>.preimage_closure_eq_closure_preimage hb.contMDiff.continuous _).symm

/-- Source dimensions below the actual fibre dimension have no regular points. -/
theorem dimensionPart_preimage_eq_empty_of_lt_fibre
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) {j : ℕ} (hj : j < m-n) :
    dimensionPart (n := m) (b ⁻¹' W) j = ∅ := by
  have hreg : regularLocus (n := m) (b ⁻¹' W) j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact (Nat.not_le_of_gt hj)
      (HironakaSmoothSubmersionRegularityReflection.regularAtDim_of_preimage_submersion
        (hb.isSubmersionAt y) hy).1
  rw [dimensionPart,hreg,closure_empty]

/-- The entire intrinsic singular set, without selecting a single pure dimension. -/
theorem singularSet_preimage_eq
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) :
    singularSet (n := m) (b ⁻¹' W) = b ⁻¹' singularSet (n := n) W := by
  ext y
  change y ∈ singularSet (n := m) (b ⁻¹' W) ↔ b y ∈ singularSet (n := n) W
  rw [mem_singularSet_iff,mem_singularSet_iff]
  constructor
  · rintro ⟨hy,hs⟩
    refine ⟨hy,?_⟩
    intro k hk
    exact hs (k+(m-n)) (regularAtDim_preimage_submersion (hb.isSubmersionAt y) hk)
  · rintro ⟨hy,ht⟩
    refine ⟨hy,?_⟩
    intro j hj
    exact ht (j-(m-n))
      (HironakaSmoothSubmersionRegularityReflection.regularAtDim_of_preimage_submersion
        (hb.isSubmersionAt y) hj).2

/-- Literal equality of the whole increasing dimension-labelled input lists
after deleting exactly empty parts.  The source itself may be empty. -/
theorem nonempty_dimension_list_preimage
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (W : Set X) :
    ((List.range m).map (fun j => (dimensionPart (n := m) (b ⁻¹' W) j,j))).filter
        (fun p => decide p.1.Nonempty) =
      ((List.range n).map (fun k => (b ⁻¹' dimensionPart (n := n) W k,k+(m-n)))).filter
        (fun p => decide p.1.Nonempty) := by
  by_cases hY : Nonempty Y
  · obtain ⟨y⟩ := hY
    have hnm := HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt
      (hb.isSubmersionAt y)
    have hrange : List.range m = List.range (m-n) ++ (List.range n).map (fun k => (m-n)+k) := by
      conv_lhs => rw [show m = (m-n)+n by omega,List.range_add]
    rw [hrange,List.map_append,List.filter_append,List.map_map]
    have hlow : ((List.range (m-n)).map (fun j => (dimensionPart (n := m) (b ⁻¹' W) j,j))).filter
        (fun p => decide p.1.Nonempty) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro p hp
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
      simp only [dimensionPart_preimage_eq_empty_of_lt_fibre hb W (List.mem_range.mp hj),
        Set.not_nonempty_empty,decide_false,Bool.false_eq_true,not_false_eq_true]
    rw [hlow,List.nil_append]
    apply congrArg (List.filter (fun p : Set Y × ℕ => decide p.1.Nonempty))
    apply List.map_congr_left
    intro k _hk
    change (dimensionPart (n := m) (b ⁻¹' W) ((m-n)+k),(m-n)+k) =
      (b ⁻¹' dimensionPart (n := n) W k,k+(m-n))
    rw [Nat.add_comm (m-n) k,dimensionPart_preimage_eq_shift hb W k]
  · have he : ∀ A : Set Y, A = ∅ := by
      intro A
      apply eq_empty_iff_forall_notMem.mpr
      intro y _hy
      exact hY ⟨y⟩
    have hf : ∀ L : List (Set Y × ℕ), L.filter (fun p => decide p.1.Nonempty) = [] := by
      intro L
      apply List.filter_eq_nil_iff.mpr
      intro p _hp
      simp only [he p.1,Set.not_nonempty_empty,decide_false,Bool.false_eq_true,not_false_eq_true]
    exact (hf _).trans (hf _).symm

end

end Hironaka.HironakaOriginalCanonicalDimensionList
