import Hironaka.Geometry.QuotGrassmannPivotAffinePrincipalGenerators
import Hironaka.Algebra.FiniteProjectivePrincipalCover

/-!
# Native finite projectivity of SAME actual affine sections

Original native generating isomorphisms produce all local finite free frames.
Actual affine quasicoherence supplies the literal original localization maps.
Finite presentation and projectivity are conclusions, without Noetherian input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual native original affine local generating data internally produces finite presented projective global sections. -/
theorem originalAffineLocalGeneratorsSections_finitePresentation_projective
    {A : CommRingCat.{u}} {M : (Spec A).Modules} [M.IsQuasicoherent]
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType] :
    Module.FinitePresentation A Γ(M, ⊤) ∧ Module.Projective A Γ(M, ⊤) := by
  let t := originalAffinePrincipalGeneratorElements q
  let φ : (g : t) → Γ(M, ⊤) →ₗ[A] Γ(M, PrimeSpectrum.basicOpen g.val) :=
    originalAffinePrincipalGeneratorRestriction q
  let (g : t) : Algebra A Γ(Spec A, PrimeSpectrum.basicOpen g.val) := inferInstance
  let (g : t) : IsLocalization.Away g.val
      Γ(Spec A, PrimeSpectrum.basicOpen g.val) := inferInstance
  let (g : t) : IsScalarTower A Γ(Spec A, PrimeSpectrum.basicOpen g.val)
      Γ(M, PrimeSpectrum.basicOpen g.val) := inferInstance
  let : ∀ g : t, IsLocalizedModule.Away g.val (φ g) :=
    fun g => originalAffinePrincipalGeneratorRestriction_isLocalizedModule q g
  exact Algebra.FiniteProjectivePrincipalCover.finitePresentation_projective_of_localizationSpan
    (Rₚ := fun g : t => Γ(Spec A, PrimeSpectrum.basicOpen g.val))
    (Mₚ := fun g : t => Γ(M, PrimeSpectrum.basicOpen g.val))
    t (originalAffinePrincipalGeneratorElements_span q) φ
    (fun g => ⟨originalAffinePrincipalGeneratorSections_finite q g,
      originalAffinePrincipalGeneratorSections_projective q g⟩)

end Hironaka.Geometry.QuotGrassmann
