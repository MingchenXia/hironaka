import DeJongAlterations.Geometry.BlowupDivisor
import DeJongAlterations.Geometry.SpecIdealSheaf
import DeJongAlterations.Geometry.CartierLocality
import DeJongAlterations.Geometry.BlowupGluing

/-!
# The full global blowup ideal is effective Cartier

The actual ideal-sheaf pullback is compared with the exact native affine
exceptional ideals, then glued by the actual global blowup open cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.BlowupCartier

open SpecIdealSheaf BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The canonical affine restriction preserves the complete native ideal. -/
theorem comap_fromSpec (U : X.affineOpens) :
    D.comap U.2.fromSpec = specIdealSheaf Γ(X, U.1) (D.ideal U) := by
  let f := U.2.fromSpec
  let V : X.affineOpens := ⟨f ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion f⟩
  have hV : V.1 = U.1 := by
    dsimp only [V, f]
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  let ρ : Γ(X, U.1) ⟶ Γ(X, V.1) := X.presheaf.map (homOfLE hV.le).op
  have hpre : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ f ⁻¹ᵁ U.1 := by
    rw [U.2.fromSpec_preimage_self]
  have happ : f.appLE U.1 ⊤ hpre = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    dsimp only [f]
    rw [Scheme.Hom.appLE, U.2.fromSpec_app_self]
    simp only [Category.assoc, ← Functor.map_comp]
    simp
  have hρ : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (f.appIso ⊤).inv = ρ := by
    rw [← happ]
    exact Scheme.Hom.appLE_appIso_inv f hpre
  have hρiso : IsIso ρ := by
    have heq : homOfLE hV.le = eqToHom hV := Subsingleton.elim _ _
    dsimp only [ρ]
    rw [heq]
    infer_instance
  let : IsIso ρ := hρiso
  apply (specIdealSheafEquiv Γ(X, U.1)).injective
  rw [specIdealSheafEquiv_specIdealSheaf, specIdealSheafEquiv_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.comap_comap]
  change (D.ideal V).comap
    ((Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (f.appIso ⊤).inv).hom = D.ideal U
  rw [hρ, ← D.map_ideal hV.le]
  exact Ideal.comap_map_of_bijective ρ.hom (ConcreteCategory.bijective_of_isIso ρ)

/-- An empty affine open has empty actual affine blowup, without ring nontriviality assumptions. -/
theorem affineBlowup_isEmpty_of_empty_affine (U : X.affineOpens) (hU : ¬ Nonempty U.1) :
    IsEmpty (affineBlowup (D.ideal U)) := by
  refine ⟨fun y => hU ?_⟩
  exact ⟨U.2.isoSpec.inv (affineBlowupStructure (D.ideal U) y)⟩

/-- The full original ideal is Cartier after its actual native affine blowup on every affine site piece. -/
theorem affine_pullback_isEffectiveCartier [IsIntegral X] (U : X.affineOpens) :
    IsEffectiveCartierDivisor
      (D.comap (affineBlowupStructure (D.ideal U) ≫ U.2.fromSpec)) := by
  rw [Scheme.IdealSheafData.comap_comp, comap_fromSpec]
  by_cases hU : Nonempty U.1
  · let : Nonempty U.1 := hU
    exact affineBlowupExceptionalIdeal_isEffectiveCartier (D.ideal U)
  · let : IsEmpty (affineBlowup (D.ideal U)) := affineBlowup_isEmpty_of_empty_affine D U hU
    intro y
    exact isEmptyElim y

/-- The exact global pulled-back ideal restricts to the full native affine exceptional ideal. -/
theorem blowup_pullback_comap_chart (U : X.AffineZariskiSite) :
    (D.comap (blowupStructure D)).comap (chartInclusion D U) =
      affineBlowupExceptionalIdeal (D.ideal ⟨U.1, U.2⟩) := by
  rw [← Scheme.IdealSheafData.comap_comp, chartInclusion_structure,
    Scheme.IdealSheafData.comap_comp, comap_fromSpec D ⟨U.1, U.2⟩]
  rfl

/-- On an integral scheme, the full native ideal becomes effective Cartier on its actual global blowup. -/
theorem blowup_pullback_isEffectiveCartier [IsIntegral X] :
    IsEffectiveCartierDivisor (D.comap (blowupStructure D)) := by
  apply CartierLocality.of_openCover _ (blowupCover D)
  intro U
  change IsEffectiveCartierDivisor ((D.comap (blowupStructure D)).comap (chartInclusion D U))
  rw [← Scheme.IdealSheafData.comap_comp, chartInclusion_structure]
  exact affine_pullback_isEffectiveCartier D ⟨U.1, U.2⟩

/-- The exact pulled-back Cartier ideal has the actual inverse-image support. -/
theorem blowup_pullback_support :
    (D.comap (blowupStructure D)).support = D.support.preimage (blowupStructure D).continuous :=
  Scheme.IdealSheafData.support_comap D (blowupStructure D)

/-- For a closed subset, the concrete native blowup makes its full inverse-image ideal Cartier
and has precisely its inverse-image closed support. No properness or alteration claim is needed here. -/
theorem vanishingIdeal_blowup_cartier [IsIntegral X] (Z : Closeds X) :
    IsEffectiveCartierDivisor
      ((Scheme.IdealSheafData.vanishingIdeal Z).comap
        (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z))) ∧
      ((Scheme.IdealSheafData.vanishingIdeal Z).comap
        (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z))).support =
        Z.preimage (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)).continuous := by
  refine ⟨blowup_pullback_isEffectiveCartier _, ?_⟩
  have hs : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
    SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  rw [blowup_pullback_support, hs]

end DeJongAlterations.Geometry.BlowupCartier
