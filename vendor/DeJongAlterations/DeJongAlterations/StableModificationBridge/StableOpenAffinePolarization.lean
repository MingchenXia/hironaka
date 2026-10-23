/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.FibrePolarizationFinite
import DeJongAlterations.StableModificationBridge.GeneratedSectionBundleIso
import DeJongAlterations.StableModificationBridge.RelativeAffineNeighbourhood

/-!
# An actual affine polarization on one original base neighborhood

Blueprint: `stable-open-affine-polarization.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModificationBridge.StableOpenAffinePolarization

open StableModification.Projectivity Geometry.ProjectiveIdeal
open GeneratedSectionHyperplane GeneratedSectionBundleIso

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The natural original closed-fibre section internally produces an affine
map on ONE original base open and the whole SAME original power comparison. -/
theorem exists_affine_polarization {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (β : X ⟶ Y) [IsProper β] (p : Y ⟶ Spec (.of R))
    [IsLocallyNoetherian Y] (hloc : LocallyRelativelyProjective p β)
    (L : LineBundleData X) {y : Y} (hy : IsClosed ({y} : Set Y))
    [Infinite (Y.residueField y)] (hdim : topologicalKrullDim (β.fiber y) ≤ 1)
    (hsec : HasFiberSection β L y) :
    ∃ W : Y.Opens, y ∈ W ∧ ∃ m : ℕ, 0 < m ∧ ∃ (N : ℕ)
      (h : (β ⁻¹ᵁ W).toScheme ⟶ projectiveSpace R N), IsAffineHom h ∧
      Nonempty ((L.pullback (β ⁻¹ᵁ W).ι).twist (unitModule (β ⁻¹ᵁ W).toScheme) (m : ℤ) ≅
        ((nativeHyperplane R N).pullback h).twist (unitModule (β ⁻¹ᵁ W).toScheme) 1) := by
  obtain ⟨O, hyO, m, hm, N, T, hT, E, hyE, hfin⟩ :=
    FibrePolarizationFinite.exists_finite_sectionMap_of_hasFiberSection
      β p hloc L hy hdim hsec
  let U := β ⁻¹ᵁ O
  let pO := O.ι ≫ p
  let h₀ := LineBundleData.toProjectiveSpace ((β ∣_ O) ≫ pO) hT
  have hh₀ : h₀ ≫ projectiveSpaceStructure R N = (β ∣_ O) ≫ O.ι ≫ p :=
    LineBundleData.toProjectiveSpace_structure ((β ∣_ O) ≫ pO) hT
  obtain ⟨W, hyW, Z, k, hj, hrange, hka⟩ :=
    RelativeAffineNeighbourhood.exists_affine_neighbourhood β p O hyO h₀ hh₀ E hyE hfin
  let j := k ≫ U.ι
  let : IsOpenImmersion j := hj
  let : IsAffineHom (k ≫ h₀) := hka
  have hr : Set.range (β ⁻¹ᵁ W).ι = Set.range j := by
    rw [Scheme.Opens.range_ι]
    exact hrange.symm
  let e := IsOpenImmersion.isoOfRangeEq (β ⁻¹ᵁ W).ι j hr
  let b := e.hom ≫ k
  have hb : b ≫ U.ι = (β ⁻¹ᵁ W).ι := by
    dsimp only [b]
    rw [Category.assoc]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  have hba : IsAffineHom (b ≫ h₀) := by
    simpa only [b, Category.assoc] using
      (inferInstance : IsAffineHom (e.hom ≫ (k ≫ h₀)))
  let e₀ : (L.pullback U.ι).twist (unitModule U.toScheme) (m : ℤ) ≅
      ((nativeHyperplane R N).pullback h₀).twist (unitModule U.toScheme) 1 :=
    generatedPowerHyperplaneIso ((β ∣_ O) ≫ pO) hT
  let e₁ := ((L.pullback U.ι).nativePullbackTwistIso (m : ℤ) b).symm ≪≫
    (Scheme.Modules.pullback b).mapIso e₀ ≪≫
    (((nativeHyperplane R N).pullback h₀).nativePullbackTwistIso 1 b)
  refine ⟨W, hyW, m, hm, N, b ≫ h₀, hba, ⟨?_⟩⟩
  simpa only [LineBundleData.pullback_comp_eq, hb] using e₁

end DeJongAlterations.StableModificationBridge.StableOpenAffinePolarization
