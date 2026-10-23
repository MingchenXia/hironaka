/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.StableMarkedCartierStalk
import DeJongAlterations.StableModificationBridge.StableMarkedCartierSpreadAlgebra
import DeJongAlterations.Geometry.BlowupCartier
import DeJongAlterations.StableModification.Blowups.StrictlySemistable

/-! The original semistable marking is genuinely effective Cartier.
Blueprint: `stable-marked-cartier.tex`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.StableModificationBridge.StableMarkedCartier

open StableModification Geometry.SpecIdealSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The ACTUAL original étale marking in the smooth locus of a generically smooth
nodal family is Cartier, internally deriving and spreading its whole ideal equation. -/
theorem isEffectiveCartierDivisor_of_isSemistablePair {X S : Scheme.{u}} (f : X ⟶ S)
    [DeJong.IsNodalCurve f] [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → DeJong.IsSmoothAt f x)
    (D : X.IdealSheafData) (hD : DeJong.IsSemistablePair f D) :
    IsEffectiveCartierDivisor D := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro x
  by_cases hxD : x ∈ (D.support : Set X)
  · obtain ⟨z, rfl⟩ := D.range_subschemeι.symm ▸ hxD
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := D.subschemeι z) (U := (⊤ : X.Opens)) trivial
    let U : X.affineOpens := ⟨W, hW⟩
    have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian U
    let p := (hW.primeIdealOf ⟨D.subschemeι z, hxW⟩).asIdeal
    let := X.presheaf.algebra_section_stalk ⟨D.subschemeι z, hxW⟩
    have : IsLocalization p.primeCompl (X.presheaf.stalk (D.subschemeι z)) :=
      hW.isLocalization_stalk ⟨D.subschemeι z, hxW⟩
    have hloc : ∃ g : X.presheaf.stalk (D.subschemeι z), IsRegular g ∧
        (D.ideal U).map (algebraMap Γ(X, W) (X.presheaf.stalk (D.subschemeι z))) =
          Ideal.span {g} := by
      obtain ⟨g, hg, hker⟩ := StableMarkedCartierStalk.exists_regular_stalk_kernel_generator
        f hS hgen D hD z
      refine ⟨g, hg, ?_⟩
      change (D.ideal U).map (X.presheaf.germ U.1 (D.subschemeι z) hxW).hom = Ideal.span {g}
      rw [← Algebra.NodeFittingIdealSheaf.stalkIdeal_eq_map_germ D U hxW,
        ← Algebra.NodeFittingIdealSheaf.ker_stalkMap_subschemeι]
      exact hker
    obtain ⟨s, hs, t, -, hreg, heq⟩ :=
      StableMarkedCartierSpreadAlgebra.exists_regular_generator_away p (D.ideal U) hloc
    let j : Spec (.of (Localization.Away s)) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) (Localization.Away s))) ≫ hW.fromSpec
    have hc : IsEffectiveCartierDivisor (D.comap j) := by
      dsimp only [j]
      rw [Scheme.IdealSheafData.comap_comp, Geometry.BlowupCartier.comap_fromSpec D U,
        specIdealSheaf_comap, heq]
      exact isEffectiveCartierDivisor_specIdealSheaf_span _ hreg
    have hrange : D.subschemeι z ∈ Set.range j := by
      have h := Curves.SemistableOpen.mem_range_localization_chart (jB := hW.fromSpec) s
        (hW.primeIdealOf ⟨D.subschemeι z, hxW⟩) hs
      rw [hW.fromSpec_primeIdealOf ⟨D.subschemeι z, hxW⟩] at h
      exact h
    obtain ⟨w, hw⟩ := hrange
    simpa only [hw] using
      Geometry.CartierLocality.exists_affine_neighborhood_of_isOpenImmersion j D hc w
  · let O : X.Opens := ⟨(D.support : Set X)ᶜ, D.support.isClosed.isOpen_compl⟩
    obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := O) hxD
    have htop : D.comap hW.fromSpec = ⊤ :=
      Curves.comap_eq_top_of_forall_notMem_support D hW.fromSpec fun y => by
        apply hWO
        have hy := Set.mem_range_self (f := hW.fromSpec) y
        rwa [hW.range_fromSpec] at hy
    have hc : IsEffectiveCartierDivisor (D.comap hW.fromSpec) := by
      rw [htop]
      exact isEffectiveCartierDivisor_top _
    simpa only [IsAffineOpen.fromSpec_primeIdealOf] using
      Geometry.CartierLocality.exists_affine_neighborhood_of_isOpenImmersion
        hW.fromSpec D hc (hW.primeIdealOf ⟨x, hxW⟩)

end DeJongAlterations.StableModificationBridge.StableMarkedCartier
