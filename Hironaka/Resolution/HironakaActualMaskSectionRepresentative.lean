/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOpenSectionRepresentative
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualMaskSectionRepresentative
noncomputable section
open Hironaka.HolomorphicIdealSheaves MarkedIdeals
 MarkedIdealOperationsAlong.MarkedIdeal
 HironakaActualOpenZeroSectionDifferentials HironakaActualOpenSectionRepresentative
 HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
 HironakaSmoothSubmersionOrderedChoiceImageTrace
variable {n : ℕ}

def baseMask (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) : Opens U :=
  ⟨zeroSection U ⁻¹' O,O.isOpen.preimage (zeroSection_contMDiff U).continuous⟩

def overlap (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) : Opens (productOpen U) :=
  O ⊓ ⟨projection U ⁻¹' baseMask U O,(baseMask U O).isOpen.preimage (projection_contMDiff U).continuous⟩

def toMask (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) (z : overlap U O) : O :=
  ⟨z.val,z.property.1⟩

def sectionToMask (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) (x : baseMask U O) : O :=
  ⟨zeroSection U x.val,x.property⟩

def overlapProjection (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) (z : overlap U O) : baseMask U O :=
  ⟨projection U z.val,z.property.2⟩

private theorem projection_section (U : Opens (ComplexModel n)) (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

def overlapRetraction (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) (z : overlap U O) : overlap U O :=
  ⟨zeroSection U (projection U z.val),z.property.2,by
    change projection U (zeroSection U (projection U z.val))∈baseMask U O
    rw [projection_section]
    exact z.property.2⟩

private theorem toMask_contMDiff (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (toMask U O) := by
  apply (ContMDiff.subtypeVal_comp_iff O _).mp
  exact contMDiff_subtype_val

private theorem sectionToMask_contMDiff (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (sectionToMask U O) := by
  apply (ContMDiff.subtypeVal_comp_iff O _).mp
  exact (zeroSection_contMDiff U).comp contMDiff_subtype_val

private theorem overlapProjection_contMDiff (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ (overlapProjection U O) := by
  apply (ContMDiff.subtypeVal_comp_iff (baseMask U O) _).mp
  exact (projection_contMDiff U).comp contMDiff_subtype_val

private theorem overlapRetraction_contMDiff (U : Opens (ComplexModel n)) (O : Opens (productOpen U)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (overlapRetraction U O) := by
  apply (ContMDiff.subtypeVal_comp_iff (overlap U O) _).mp
  exact ((zeroSection_contMDiff U).comp (projection_contMDiff U)).comp contMDiff_subtype_val

theorem restrictEquiv_actual_mask_section (U : Opens (ComplexModel n)) (O : Opens (productOpen U))
    (A : Set U) (E : List (Set (overlap U O))) (d : ℕ)
    (J : GermIdeal (n+1) O) (hJ : ∀x g,J.mem x g → HolomorphicAt (n+1) g x) :
    RestrictEquiv
      (⟨(Subtype.val : overlap U O → productOpen U) ⁻¹' liftedCarrier A,E,
        GermIdeal.pullback (m := n+1) (toMask U O) J,d⟩ : MarkedIdeal (n+1) (overlap U O))
      (⟨(Subtype.val : overlap U O → productOpen U) ⁻¹' liftedCarrier A,E,
        GermIdeal.pullback (m := n+1) (overlapProjection U O)
          (GermIdeal.pullback (m := n) (sectionToMask U O) J),d⟩ : MarkedIdeal (n+1) (overlap U O)) := by
  let K := GermIdeal.pullback (m := n+1) (toMask U O) J
  have hK : ∀x g,K.mem x g → HolomorphicAt (n+1) g x := by
    intro x g hg
    exact hg.1
  have hfix : ∀z∈(Subtype.val : overlap U O → productOpen U) ⁻¹' liftedCarrier A,
      overlapRetraction U O z=z := by
    intro z hz
    apply Subtype.ext
    apply Subtype.ext
    change tangentInclusion n 1 (tangentProjection n 1 z.val.val)=z.val.val
    have hq : actualJointNormalProjection n 1 z.val.val=0 := hz.2
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero]
      using (join_projections (n := n) (m := 1) z.val.val)
  have hEq := restrictEquiv_retraction _ E d (overlapRetraction U O)
    (overlapRetraction_contMDiff U O) hfix K hK
  have hWhole : GermIdeal.pullback (m := n+1) (overlapRetraction U O) K=
      GermIdeal.pullback (m := n+1) (overlapProjection U O)
        (GermIdeal.pullback (m := n) (sectionToMask U O) J) := by
    rw [←whole_pullback_comp (toMask_contMDiff U O) (overlapRetraction_contMDiff U O) J hJ,
      ←whole_pullback_comp (sectionToMask_contMDiff U O) (overlapProjection_contMDiff U O) J hJ]
    rfl
  rw [hWhole] at hEq
  exact hEq
end
end Hironaka.HironakaActualMaskSectionRepresentative
