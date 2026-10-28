/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointEmbeddedBoundaryLift
import Hironaka.Blowup.BlowupExistence
import Hironaka.Resolution.HironakaActualClosedContactBlowupRestriction

/-! Actual ambient blowup construction from an intrinsic centre and whole
transverse boundary, with prescribed lower blowup and entire born boundary.
No ambient centre geometry or ambient blowup is supplied as a certificate. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaDisjointConstructedAmbientLift
noncomputable section
open Hironaka.BlowupSequences NormalCrossings BlowupSNCTransform
  SimultaneousNormalCrossings RegularPointDimension RegularPatchPullback
  GiraudAlong BlowupFlatCoordinates TangentDirectionAlong SubmanifoldChartedSpace
  HironakaActualClosedContactBlowupRestriction BlowupStrictSubmanifold

private theorem plane_min {n : ℕ} (a : ℕ) :
    complexCoordinatePlane n (min n a)=complexCoordinatePlane n a := by
  ext z
  constructor
  · intro h j hj
    exact h j (by omega)
  · intro h j hj
    exact h j (by have := j.isLt; omega)

private theorem regular_of_joint_nc {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (hn : 0<n) {C N : Set X} {E : List (Set X)} (hCN : C⊆N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hNC : HasNormalCrossings n C E) {x : X} (hx : x∈C) :
    ∃ k, RegularAtDim (n := n) C x k := by
  obtain ⟨a,b,Φ,s,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn hCN hE hT hNC hx
  let c := flatMap Φ x
  have hc : c∈complexCoordinatePlane n a :=
    (hflat (mem_flatDomain_self Φ).1 (mem_flatDomain_self Φ).2).1.mp hx
  let Θ := subConst Φ c
  refine ⟨min n a,Nat.min_le_left _ _,hx,Θ,hsrc,sub_self _,?_⟩
  intro z hz hzΘ
  rw [plane_min]
  have hf := (hflat hz hzΘ).1
  change z∈C ↔ (Φ.toFun (chartAt (ComplexModel n) x z)-c)∈complexCoordinatePlane n a
  rw [hf]
  constructor
  · intro h j hj
    change Φ.toFun (chartAt (ComplexModel n) x z) j-c j=0
    rw [h j hj,hc j hj,sub_self]
  · intro h j hj
    have he := h j hj
    simpa only [PiLp.sub_apply,hc j hj,sub_zero] using he

private theorem interior_regular_eq_empty {n d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (hd : d<n) (hS : ∀ x∈N, RegularAtDim (n := n) N x d) :
    interior N=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he : (univ : Set X)∩interior N=N∩interior N := by
    ext z
    simp only [mem_inter_iff,mem_univ,true_and]
    exact ⟨fun hz => ⟨interior_subset hz,hz⟩,fun hz => hz.2⟩
  have hNn : RegularAtDim (n := n) N x n :=
    regularAtDim_of_inter_eq isOpen_interior hx he
      (AnalyticIrreducibleComponents.regularAtDim_univ (n := n) x)
  have hdim := eq_of_regularAtDim hNn (hS x (interior_subset hx))
  omega

/-- Construct the actual ambient blowup, its entire born boundary, and the
comparison to the prescribed original intrinsic blowup, without an ambient π input. -/
theorem exists_constructed_ambient_lift {d t : ℕ} {X Z : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
    {N : Set X} (hNc : IsClosed N)
    (hS : ∀ x∈N, RegularAtDim (n := d+t) N x d) (ht : 0<t)
    {E : List (Set X)} (hE : IsSNCDivisor (d+t) E) (hT : IsTransverse (d+t) N E) :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    ∀ (D : Set N) (ρ : Z → N), IsBlowupAlong d D ρ →
      HasNormalCrossings d D (E.map fun H => (Subtype.val : N → X) ⁻¹' H) →
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (d+t)) Y)
        (_ : IsComplexManifold (d+t) Y) (π : Y → X)
        (hπ : IsBlowupAlong (d+t) ((Subtype.val : N → X) '' D) π),
        HasNormalCrossings (d+t) ((Subtype.val : N → X) '' D) E ∧
        IsSNCDivisor (d+t) (E.map (geoStrictTransform π ((Subtype.val : N → X) '' D)) ++
          [π ⁻¹' ((Subtype.val : N → X) '' D)]) ∧
        IsTransverse (d+t) (geoStrictTransform π ((Subtype.val : N → X) '' D) N)
          (E.map (geoStrictTransform π ((Subtype.val : N → X) '' D)) ++
            [π ⁻¹' ((Subtype.val : N → X) '' D)]) ∧
        (letI := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
         letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
         ∃ F : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
             geoStrictTransform π ((Subtype.val : N → X) '' D) N,
           restrictedProjection hNc D hπ ∘ F=ρ) := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro D ρ hρ hDNC
  have hn : 0<d+t := by omega
  have hCN : (Subtype.val : N → X) '' D⊆N := by
    rintro _ ⟨p,_hp,rfl⟩
    exact p.property
  have hNC := HironakaDisjointEmbeddedBoundaryLift.hasNormalCrossings_native_image hS hn hE hT D hDNC
  have hCclosed : IsClosed ((Subtype.val : N → X) '' D) :=
    hNc.isClosedEmbedding_subtypeVal.isClosedMap D hρ.1.1
  have hC : IsClosedSubmanifold (d+t) ((Subtype.val : N → X) '' D) :=
    ⟨hCclosed,fun x hx => regular_of_joint_nc hn hCN hE hT hNC hx⟩
  have hNint : interior N=∅ := interior_regular_eq_empty (by omega) hS
  have hCint : interior ((Subtype.val : N → X) '' D)=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := interior_mono hCN hx
    rw [hNint] at hh
    exact hh
  obtain ⟨Y,τ,cs,hY,π,hπ⟩ := BlowupExistence.exists_isBlowupAlong
    ((Subtype.val : N → X) '' D) hC hCint
  refine ⟨Y,τ,cs,hY,π,hπ,hNC,
    isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hE hNC,
    isTransverse_geoTransformE_of_hasNormalCrossings hπ hNc hCN hE hT hNC,?_⟩
  exact exists_strictContact_diffeomorph (Nat.le_add_right d t) hNc hS hπ hρ

end
end Hironaka.HironakaDisjointConstructedAmbientLift
