/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalAtlas
/-! Properness of the actual original-input terminal glued projection.
Complete three-node mathematics preceded proof code. Whole saturated local
ranges supply entire compact fibres and closed images from true local towers. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalTerminalProperProjection
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers HironakaOriginalTerminalAtlas
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

theorem originalTerminalGluedProjection_fibre (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (x : X) :
    (originalTerminalGluedProjection M hM) ⁻¹' ({x} : Set X)=
      (originalTerminalLocalInclusion M hM x) ''
        (((actualLocalTerminalAtlas M hM).tower x).proj ⁻¹'
          {⟨x,(actualLocalTerminalAtlas M hM).point_mem x⟩}) := by
  ext z
  constructor
  · intro hz
    have hp : originalTerminalGluedProjection M hM z=x := hz
    have hr : z ∈ range (originalTerminalLocalInclusion M hM x) := by
      rw [originalTerminalLocalInclusion_range]
      change originalTerminalGluedProjection M hM z ∈ (actualLocalTerminalAtlas M hM).openSet x
      rw [hp]
      exact (actualLocalTerminalAtlas M hM).point_mem x
    obtain ⟨y,rfl⟩ := hr
    refine ⟨y,?_,rfl⟩
    change ((actualLocalTerminalAtlas M hM).tower x).proj y=⟨x,_⟩
    apply Subtype.ext
    exact (originalTerminalGluedProjection_local M hM x y).symm.trans hp
  · rintro ⟨y,hy,rfl⟩
    have hy' : ((actualLocalTerminalAtlas M hM).tower x).proj y=⟨x,_⟩ := hy
    change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM x y)=x
    rw [originalTerminalGluedProjection_local]
    exact congrArg Subtype.val hy'

theorem originalTerminalGluedProjection_fibre_isCompact (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (x : X) :
    IsCompact ((originalTerminalGluedProjection M hM) ⁻¹' ({x} : Set X)) := by
  rw [originalTerminalGluedProjection_fibre]
  exact ((HironakaLocalPrincipalization.isProperMap_proj
    ((actualLocalTerminalAtlas M hM).tower x)).isCompact_preimage isCompact_singleton).image
      (originalTerminalLocalInclusion_openEmbedding M hM x).continuous

theorem originalTerminalGluedProjection_isClosedMap (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) : IsClosedMap (originalTerminalGluedProjection M hM) := by
  intro C hC
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let A := actualLocalTerminalAtlas M hM
  let Γ := originalTerminalLocalInclusion M hM x
  let u : A.openSet x := ⟨x,A.point_mem x⟩
  let B : Set (A.finalSpace x) := Γ ⁻¹' C
  have hB : IsClosed B := hC.preimage (originalTerminalLocalInclusion_openEmbedding M hM x).continuous
  have hcl : IsClosed ((A.tower x).proj '' B) :=
    (HironakaLocalPrincipalization.isProperMap_proj (A.tower x)).isClosedMap B hB
  let V : Set (A.openSet x) := ((A.tower x).proj '' B)ᶜ
  have hV : IsOpen V := hcl.isOpen_compl
  have hu : u ∈ V := by
    rintro ⟨y,hy,hyp⟩
    apply hx
    refine ⟨Γ y,hy,?_⟩
    exact (originalTerminalGluedProjection_local M hM x y).trans (congrArg Subtype.val hyp)
  refine ⟨Subtype.val '' V,?_,?_,⟨u,hu,rfl⟩⟩
  · rintro z ⟨v,hv,rfl⟩ hz
    obtain ⟨w,hw,hpw⟩ := hz
    have hr : w ∈ range Γ := by
      change w ∈ range (originalTerminalLocalInclusion M hM x)
      rw [originalTerminalLocalInclusion_range]
      change originalTerminalGluedProjection M hM w ∈ A.openSet x
      rw [hpw]
      exact v.property
    obtain ⟨y,hΓy⟩ := hr
    apply hv
    refine ⟨y,?_,?_⟩
    · change Γ y ∈ C
      rw [hΓy]
      exact hw
    · apply Subtype.ext
      have hlocal := originalTerminalGluedProjection_local M hM x y
      change originalTerminalGluedProjection M hM (Γ y)=((A.tower x).proj y).val at hlocal
      exact hlocal.symm.trans ((congrArg (originalTerminalGluedProjection M hM) hΓy).trans hpw)
  · exact (A.openSet x).isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hV

theorem originalTerminalGluedProjection_isProperMap (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) : IsProperMap (originalTerminalGluedProjection M hM) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(originalTerminalGluedProjection M hM).continuous,
      originalTerminalGluedProjection_isClosedMap M hM,
      originalTerminalGluedProjection_fibre_isCompact M hM⟩

end
end Hironaka.HironakaOriginalTerminalProperProjection
