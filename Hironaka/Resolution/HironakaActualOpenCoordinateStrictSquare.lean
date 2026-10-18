/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaBaseChange

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualOpenCoordinateStrictSquare
noncomputable section
open Hironaka.BlowupSequences HironakaBaseChange
variable {n : ℕ}

/-- The true inverse identity proves bijectivity of the actual differential, across distinct universes. -/
theorem mfderiv_actual_diffeomorph_bijective
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (e : M ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ N) (y : M) :
    Function.Bijective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) e y) := by
  have hc := mfderiv_comp y (e.symm.contMDiff.mdifferentiable (by simp) (e y))
    (e.contMDiff.mdifferentiable (by simp) y)
  have he : (e.symm ∘ e : M → M)=id := funext e.symm_apply_apply
  rw [he,mfderiv_id] at hc
  have hb : Function.Bijective
      ((mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) e.symm (e y)).comp
        (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) e y)) := by
    rw [← hc]
    exact Function.bijective_id
  exact (bijective_comp_clm_iff (E := ComplexModel n) _ _).mp hb |>.2

/-- An actual biholomorphism onto an actual open followed by its genuine inclusion has bijective differential. -/
theorem mfderiv_actual_open_coordinate_bijective
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (U : Opens N) (e : M ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U) (y : M) :
    Function.Bijective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (fun z : M => (e z : N)) y) := by
  rw [show (fun z : M => (e z : N))=(Subtype.val : U → N) ∘ e from rfl,
    mfderiv_comp y ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) (e y))
      (e.contMDiff.mdifferentiable (by simp) y)]
  exact (mfderiv_val_bijective (e y)).comp (mfderiv_actual_diffeomorph_bijective e y)

/-- The SAME original geometric strict sets commute with actual open coordinate squares across universes. -/
theorem strictTransform_actual_open_coordinate_square
    {X Y : Type u} {X' Y' : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']
    [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']
    (f : Y → X) (g : Y' → X')
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    (V : Opens X) (U : Opens Y)
    (a : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (b : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U)
    (hcomm : ∀ y, f (b y : Y)=(a (g y) : X)) (A : Set X) :
    strictTransform n g ((fun x => (a x : X)) ⁻¹' A)=
      (fun y => (b y : Y)) ⁻¹' strictTransform n f A := by
  let j : Y' → Y := fun y => b y
  let i : X' → X := fun x => a x
  have hj : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ j :=
    contMDiff_subtype_val.comp b.contMDiff
  have hi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ i :=
    contMDiff_subtype_val.comp a.contMDiff
  have hmaps : f ∘ j=i ∘ g := funext hcomm
  have hexc : exceptionalLocus n g=j ⁻¹' exceptionalLocus n f := by
    ext y
    have hleft := mfderiv_comp y (hf.mdifferentiable (by simp) (j y))
      (hj.mdifferentiable (by simp) y)
    have hright := mfderiv_comp y (hi.mdifferentiable (by simp) (g y))
      (hg.mdifferentiable (by simp) y)
    have hderiv : mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (f ∘ j) y=
        mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (i ∘ g) y := by rw [hmaps]
    rw [hleft,hright] at hderiv
    have hjb := mfderiv_actual_open_coordinate_bijective U b y
    have hib := mfderiv_actual_open_coordinate_bijective V a (g y)
    change Function.Bijective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) j y) at hjb
    change Function.Bijective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) i (g y)) at hib
    change (¬ Function.Bijective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) g y)) ↔
      ¬ Function.Bijective (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f (j y))
    constructor
    · intro hng hbf
      apply hng
      have hbcomp := hbf.comp hjb
      change Function.Bijective ((mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f (j y)).comp
        (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) j y)) at hbcomp
      rw [hderiv] at hbcomp
      exact ((bijective_comp_clm_iff (E := ComplexModel n) _ _).mp hbcomp).2
    · intro hnf hbg
      apply hnf
      have hbcomp := hib.comp hbg
      change Function.Bijective ((mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) i (g y)).comp
        (mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) g y)) at hbcomp
      rw [← hderiv] at hbcomp
      exact ((bijective_comp_clm_iff (E := ComplexModel n) _ _).mp hbcomp).1
  have hjopen : IsOpenMap j :=
    (U.isOpen.isOpenEmbedding_subtypeVal.comp b.toHomeomorph.isOpenEmbedding).isOpenMap
  have hclosure (S : Set Y) : j ⁻¹' closure S=closure (j ⁻¹' S) :=
    hjopen.preimage_closure_eq_closure_preimage hj.continuous S
  change strictTransform n g (i ⁻¹' A)=j ⁻¹' strictTransform n f A
  rw [strictTransform,strictTransform,hexc,hclosure,preimage_sdiff]
  congr 2
  ext y
  change (g y ∈ i ⁻¹' A) ↔ f (j y) ∈ A
  rw [hcomm]
  rfl

end
end Hironaka.HironakaActualOpenCoordinateStrictSquare
