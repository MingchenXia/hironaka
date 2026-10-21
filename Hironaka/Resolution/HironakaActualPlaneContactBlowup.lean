/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualGraphContactCoefficient
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Blowup.BlowupExistence

/-!
# Actual one-step blowup lift onto the entire strict contact plane

The matched original centre ideal is internally identified along the literal
plane section. Genuine blowup universal properties give the actual lift;
properness, actual exceptional density and off-centre injectivity give its
ENTIRE strict-transform image. No invariant equality or restriction iso input.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPlaneContactBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualHolomorphicGraphIdeal
  HironakaActualGraphContactCoefficient HironakaSmoothSubmersionOrderedChoiceImageTrace
  BlowupStrictSubmanifold
variable {d : ℕ}

/-- The literal original scalar contact-plane section. -/
def planeSection (d : ℕ) : ComplexModel d → ComplexModel (d+1) := graphSection (fun _ => 0)

/-- The SAME original centre in the actual scalar contact plane. -/
def planeCentre (D : Set (ComplexModel d)) : Set (ComplexModel (d+1)) := graphCarrier (fun _ => 0) D

/-- The actual whole contact plane, before any blowup. -/
def contactPlane (d : ℕ) : Set (ComplexModel (d+1)) := planeCentre (univ : Set (ComplexModel d))

private theorem planeSection_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ (planeSection d) := by
  change ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞
    (fun x => tangentInclusion d 1 x + actualJointNormalInclusion d 1 0)
  exact (tangentInclusion d 1).contMDiff.add contMDiff_const

private theorem planeCentre_pullback (D : Set (ComplexModel d)) :
    GermIdeal.pullback (m := d) (planeSection d) (vanishingIdeal (n := d+1) (planeCentre D)) =
      vanishingIdeal (n := d) D := by
  apply GermIdeal.ext
  funext x F
  exact propext (graphSection_pullback_mem_iff (fun _ => 0) x (Eventually.of_forall fun _ => differentiableAt_const _) D F)

variable {Y Z : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+1)) Y]
  [IsComplexManifold (d+1) Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z]
  [IsComplexManifold d Z] {D : Set (ComplexModel d)} {π : Y → ComplexModel (d+1)} {ρ : Z → ComplexModel d}

omit [IsComplexManifold (d+1) Y] in
/-- Actual matched centre ideals internally supply the UNIQUE genuine cross-dimensional holomorphic blowup lift. -/
theorem exists_unique_plane_blowup_lift (hπ : IsBlowupAlong (d+1) (planeCentre D) π)
    (hρ : IsBlowupAlong d D ρ) :
    ∃! κ : Z → Y,ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ κ ∧
      π∘κ=planeSection d∘ρ := by
  have hcomp := planeSection_contMDiff.comp hρ.contMDiff
  have hi : (GermIdeal.pullback (m := d) (planeSection d∘ρ)
      (vanishingIdeal (n := d+1) (planeCentre D))).IsInvertible := by
    rw [whole_pullback_comp planeSection_contMDiff hρ.contMDiff
      (vanishingIdeal (n := d+1) (planeCentre D)) (fun _ _ h => h.1),planeCentre_pullback]
    exact hρ.2.2.2.1
  exact hπ.2.2.2.2 d Z (planeSection d∘ρ) hcomp hi

private theorem projection_planeSection (x : ComplexModel d) :
    tangentProjection d 1 (planeSection d x)=x := projection_graphSection _ _

private theorem planeSection_projection {z : ComplexModel (d+1)} (hz : z∈contactPlane d) :
    planeSection d (tangentProjection d 1 z)=z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [planeSection,graphSection]
  · have he := congrArg (fun v : ComplexModel 1 => v j) hz.2
    simpa [planeSection,graphSection] using he.symm

/-- Actual properness and exceptional density identify the ENTIRE strict contact-transform image of the genuine lift. -/
theorem plane_blowup_lift_proper_and_range (hπ : IsBlowupAlong (d+1) (planeCentre D) π)
    (hρ : IsBlowupAlong d D ρ) (κ : Z → Y)
    (hκ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ κ)
    (hcomm : π∘κ=planeSection d∘ρ) :
    IsProperMap κ ∧ range κ=geoStrictTransform π (planeCentre D) (contactPlane d) := by
  have hcomm' (z : Z) : π (κ z)=planeSection d (ρ z) := congrFun hcomm z
  have hproper : IsProperMap κ := by
    apply isProperMap_of_comp_of_t2 hκ.continuous
      ((tangentProjection d 1).continuous.comp hπ.contMDiff.continuous)
    have he : ((tangentProjection d 1)∘π)∘κ=ρ := by
      funext z
      change tangentProjection d 1 (π (κ z))=ρ z
      rw [hcomm',projection_planeSection]
    rw [he]
    exact HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hρ
  refine ⟨hproper,?_⟩
  let S := geoStrictTransform π (planeCentre D) (contactPlane d)
  have hclosed : IsClosed (range κ) := by
    rw [← image_univ]
    exact hproper.isClosedMap _ isClosed_univ
  apply le_antisymm
  · have hdense : closure (ρ ⁻¹' D)ᶜ=univ := by
      rw [closure_compl,ExceptionalFibres.interior_preimage_eq_empty hρ,compl_empty]
    have hpre : (ρ ⁻¹' D)ᶜ ⊆ κ ⁻¹' S := by
      intro z hz
      apply subset_closure
      change π (κ z)∈contactPlane d ∧ π (κ z)∉planeCentre D
      rw [hcomm']
      constructor
      · exact ⟨mem_univ _,by simp [planeSection,graphSection]⟩
      · intro hC
        have hz' : ρ z ∉ D := hz
        exact hz' (by simpa only [projection_planeSection] using hC.1)
    have hall : univ ⊆ κ ⁻¹' S := by
      rw [← hdense]
      exact closure_minimal hpre (isClosed_closure.preimage hκ.continuous)
    rintro _ ⟨z,rfl⟩
    exact hall (mem_univ z)
  · apply closure_minimal ?_ hclosed
    intro y hy
    obtain ⟨z,hz⟩ := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hρ
      (tangentProjection d 1 (π y))
    have hπy : planeSection d (tangentProjection d 1 (π y))=π y := planeSection_projection hy.1
    have he : π (κ z)=π y := by rw [hcomm',hz,hπy]
    have hkc : π (κ z)∉planeCentre D := by rw [he];exact hy.2
    have hi := (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.2.1
    exact ⟨z,hi hkc hy.2 he⟩

/-- Ordinary original contact-plane centre data INTERNALLY produce an actual lower blowup and its whole strict-image lift. -/
theorem exists_original_plane_contact_blowup (D : Set (ComplexModel d))
    (hD : IsClosedSubmanifold d D) (hDint : interior D=∅)
    (hπ : IsBlowupAlong (d+1) (planeCentre D) π) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel d) Z)
      (_ : IsComplexManifold d Z) (ρ : Z → ComplexModel d) (κ : Z → Y),
      IsBlowupAlong d D ρ ∧ ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ κ ∧
      π∘κ=planeSection d∘ρ ∧ IsProperMap κ ∧
      range κ=geoStrictTransform π (planeCentre D) (contactPlane d) := by
  obtain ⟨Z,tZ,cZ,mZ,ρ,hρ⟩ := BlowupExistence.exists_isBlowupAlong D hD hDint
  obtain ⟨κ,⟨hκ,hcomm⟩,_hunique⟩ := exists_unique_plane_blowup_lift hπ hρ
  obtain ⟨hproper,hrange⟩ := plane_blowup_lift_proper_and_range hπ hρ κ hκ hcomm
  exact ⟨Z,tZ,cZ,mZ,ρ,κ,hρ,hκ,hcomm,hproper,hrange⟩

end
end Hironaka.HironakaActualPlaneContactBlowup
