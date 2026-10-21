/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceMaps

/-!
# Actual subspace presentation maps are independent of ambient extensions

Actual ambient holomorphic maps agreeing on C induce equal morphisms on the
whole reduced quotient-sheaf model. Mutual inverse identities only on C and D
therefore suffice for genuine presentation isomorphisms, in different ambient
dimensions. No structure-sheaf isomorphism or resolution data is supplied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspacePresentationIndependence
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

omit [IsComplexManifold m N] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotient_pullback_germ_eqOn {f g : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ g)
    {C : Set M} (hfg : Set.EqOn f g C) (U : Opens N)
    (s : actualComplexSection (n := m) U) (x : C)
    (hxF : f x.val ∈ U) (hxG : g x.val ∈ U) :
    (actualSubspaceInclusion (n := n) C).stalkMap x
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val
        ((actualComplexStructureSheaf (n := m) N).presheaf.germ U (f x.val) hxF s)) =
    (actualSubspaceInclusion (n := n) C).stalkMap x
      ((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap x.val
        ((actualComplexStructureSheaf (n := m) N).presheaf.germ U (g x.val) hxG s)) := by
  apply (actualSubspaceStalkWholeEquiv (n := n) C x).injective
  rw [actualSubspaceInclusion_stalk,actualSubspaceInclusion_stalk]
  have hF := PresheafedSpace.stalkMap_germ_apply
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom U x.val hxF s
  have hG := PresheafedSpace.stalkMap_germ_apply
    (ChartedSpace.locallyRingedSpaceMap g hg).toHom U x.val hxG s
  let V := (Opens.map (actualAmbientMap hf)).obj U
  let Z := (Opens.map (actualAmbientMap hg)).obj U
  let W : Opens M := V ⊓ Z
  let a := (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U) s
  let b := (ChartedSpace.locallyRingedSpaceMap g hg).toHom.c.app (op U) s
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let aW := F.map (homOfLE (show W ≤ V from inf_le_left)).op a
  let bW := F.map (homOfLE (show W ≤ Z from inf_le_right)).op b
  have hz : aW-bW ∈ actualSectionIdeal (vanishingIdeal (n := n) C) W := by
    apply (actualSectionIdeal_vanishing_iff C W (aW-bW)).mpr
    intro y hy hyC
    change s ⟨f y,hy.1⟩ - s ⟨g y,hy.2⟩ = 0
    exact sub_eq_zero.mpr (congrArg s (Subtype.ext (hfg hyC)))
  have hmem := hz x.val ⟨hxF,hxG⟩
  change F.germ W x.val ⟨hxF,hxG⟩ (aW-bW) ∈ _ at hmem
  rw [map_sub] at hmem
  have hq := Ideal.Quotient.eq.mpr hmem
  rw [F.germ_res_apply,F.germ_res_apply] at hq
  calc
    _ = Ideal.Quotient.mk _ (F.germ V x.val hxF a) :=
      congrArg (Ideal.Quotient.mk _) hF
    _ = Ideal.Quotient.mk _ (F.germ Z x.val hxG b) := hq
    _ = _ := (congrArg (Ideal.Quotient.mk _) hG).symm

omit [IsComplexManifold m N] in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality only on the actual source subset suffices for equal whole ambient quotient pullbacks. -/
theorem actualAmbientRestriction_eqOn {f g : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ g)
    {C : Set M} (hfg : Set.EqOn f g C) :
    actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap f hf =
      actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap g hg := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  have hbase :
      ((actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap f hf).toHom).base =
      ((actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap g hg).toHom).base := by
    ext x
    exact hfg x.property
  apply SheafedSpace.hom_stalk_ext _ _ hbase
  intro x
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  simp only [TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes_assoc]
  apply CommRingCat.hom_ext
  ext s
  simp only [PresheafedSpace.stalkMap.comp,ConcreteCategory.comp_apply]
  exact quotient_pullback_germ_eqOn hf hg hfg U s x hxU _

/-- Genuine descended morphisms depend only on the actual subset map, not on an ambient extension. -/
theorem actualSubspaceMap_eqOn {f g : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ g)
    {C : Set M} {D : Set N} (hCDf : ∀ x ∈ C, f x ∈ D) (hCDg : ∀ x ∈ C, g x ∈ D)
    (hfg : Set.EqOn f g C) : actualSubspaceMap hf hCDf = actualSubspaceMap hg hCDg := by
  apply (cancel_mono (actualSubspaceInclusion (n := m) D)).mp
  rw [← actualSubspaceMap_inclusion,← actualSubspaceMap_inclusion]
  exact actualAmbientRestriction_eqOn hf hg hfg

/-- Mutually inverse restrictions, in possibly different ambient dimensions, produce actual LRS isomorphisms. -/
def actualSubspaceMutualRestrictionIso {f : M → N} {g : N → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (hDC : ∀ y ∈ D, g y ∈ C)
    (hgf : ∀ x ∈ C, g (f x) = x) (hfg : ∀ y ∈ D, f (g y) = y) :
    actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D where
  hom := actualSubspaceMap hf hCD
  inv := actualSubspaceMap hg hDC
  hom_inv_id := by
    rw [← actualSubspaceMap_comp]
    exact (actualSubspaceMap_eqOn (hg.comp hf) contMDiff_id
      (fun x hx => hDC (f x) (hCD x hx)) (fun _ hx => hx) hgf).trans (actualSubspaceMap_id C)
  inv_hom_id := by
    rw [← actualSubspaceMap_comp]
    exact (actualSubspaceMap_eqOn (hf.comp hg) contMDiff_id
      (fun y hy => hCD (g y) (hDC y hy)) (fun _ hy => hy) hfg).trans (actualSubspaceMap_id D)

end
end Hironaka.HironakaActualAnalyticSubspacePresentationIndependence
