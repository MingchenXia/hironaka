import Hironaka.Resolution.HironakaG3BoundaryContainedOriginalGlobalLift
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryContainedAnalyticTrace
noncomputable section
open Hironaka.BlowupSequences BlowupTowers SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity

/-- Analyticity of the actual ambient target gives analyticity of its full
native trace on the smooth containing contact. -/
theorem native_analytic_of_ambient_image {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ V : Set (nativeManifold (Nat.le_add_right d t) N hN),
      IsComplexAnalyticSubset (n := d+t) ((Subtype.val : N → X) '' V) →
      IsComplexAnalyticSubset (n := d) V := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hV
  have h := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_val (Nat.le_add_right d t) hN) hV
  have he : (Subtype.val : N → X) ⁻¹' ((Subtype.val : N → X) '' V) = V := by
    ext p
    constructor
    · rintro ⟨q,hq,hqp⟩
      exact Subtype.val_injective hqp ▸ hq
    · intro hp
      exact ⟨p,hp,rfl⟩
  rw [he] at h
  exact h

/-- Pure dimensionality of an ambient target contained in a closed smooth
contact descends to its actual native trace. -/
theorem native_pure_of_ambient_image {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN)) (r : ℕ),
      ((Subtype.val : N → X) '' V) ⊆ closure (regularLocus (n := d+t) ((Subtype.val : N → X) '' V) r) →
      V ⊆ closure (regularLocus (n := d) V r) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V r hpure
  have hreg : (Subtype.val : N → X) '' regularLocus (n := d) V r =
      regularLocus (n := d+t) ((Subtype.val : N → X) '' V) r := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact (regularAtDim_native_image_iff (Nat.le_add_right d t) hN V p r).mpr hp
    · intro hy
      obtain ⟨p,hp,rfl⟩ := regularLocus_subset ((Subtype.val : N → X) '' V) r hy
      exact ⟨p,(regularAtDim_native_image_iff (Nat.le_add_right d t) hN V p r).mp hy,rfl⟩
  intro p hp
  have h := hpure ⟨p,hp,rfl⟩
  rw [← hreg, hNc.isClosedEmbedding_subtypeVal.closure_image_eq] at h
  obtain ⟨q,hq,hqp⟩ := h
  exact Subtype.val_injective hqp ▸ hq

/-- Dense avoidance of the remaining ambient boundary descends to the
literal native traces of that boundary. -/
theorem native_dense_avoid_of_ambient_image {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN)) (B : List (Set X)),
      ((Subtype.val : N → X) '' V) ⊆ closure (((Subtype.val : N → X) '' V) \ ⋃ H ∈ B, H) →
      V ⊆ closure (V \ ⋃ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·), H) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V B hdense
  have himage : (Subtype.val : N → X) '' (V \ ⋃ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·), H) =
      ((Subtype.val : N → X) '' V) \ ⋃ H ∈ B, H := by
    ext x
    constructor
    · rintro ⟨p,⟨hp,hpB⟩,rfl⟩
      refine ⟨⟨p,hp,rfl⟩,?_⟩
      intro hxB
      apply hpB
      simp only [mem_iUnion, exists_prop] at hxB ⊢
      obtain ⟨H,hH,hpH⟩ := hxB
      exact ⟨(Subtype.val : N → X) ⁻¹' H,List.mem_map.mpr ⟨H,hH,rfl⟩,hpH⟩
    · rintro ⟨⟨p,hp,rfl⟩,hpB⟩
      refine ⟨p,⟨hp,?_⟩,rfl⟩
      intro hpB'
      apply hpB
      simp only [mem_iUnion, exists_prop] at hpB' ⊢
      obtain ⟨H,hH,hpH⟩ := hpB'
      obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
      exact ⟨H₀,hH₀,hpH⟩
  intro p hp
  have h := hdense ⟨p,hp,rfl⟩
  rw [← himage, hNc.isClosedEmbedding_subtypeVal.closure_image_eq] at h
  obtain ⟨q,hq,hqp⟩ := h
  exact Subtype.val_injective hqp ▸ hq

end
end Hironaka.HironakaG3BoundaryContainedAnalyticTrace
