import Hironaka.Geometry.QuotGrassmannPivotLocalGeneratorFrames
import Hironaka.Geometry.ProperSteinProjectiveCechAffineFiniteType

/-!
# Actual principal subopens refine ORIGINAL native locally free generators

The cover is produced from the native original generating data. Its literal
principal restriction maps are native module localizations, by actual affine
quasicoherence. Original section rings and their scalar actions are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : CommRingCat.{u}} {M : (Spec A).Modules}

/-- The original actual principal opens lying in actual original generator-cover members. -/
def originalAffinePrincipalGeneratorElements
    (q : SheafOfModules.LocalGeneratorsData.{v} M) : Set A :=
  {g | ∃ i, (PrimeSpectrum.basicOpen g : (Spec A).Opens) ≤ q.X i}

/-- The actual original native principal refinement internally spans the whole original ring. -/
theorem originalAffinePrincipalGeneratorElements_span
    (q : SheafOfModules.LocalGeneratorsData.{v} M) :
    Ideal.span (originalAffinePrincipalGeneratorElements q) = ⊤ := by
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := Spec A) q.X).mp q.coversTop
  have hopen : ⨆ g ∈ originalAffinePrincipalGeneratorElements q,
      (PrimeSpectrum.basicOpen g : (Spec A).Opens) = ⊤ := by
    apply top_unique
    rw [← hqcover]
    refine iSup_le fun i => ?_
    rintro x hx
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hg⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx (q.X i).2
    have hle : (PrimeSpectrum.basicOpen g : (Spec A).Opens) ≤
        ⨆ g ∈ originalAffinePrincipalGeneratorElements q,
          (PrimeSpectrum.basicOpen g : (Spec A).Opens) :=
      le_iSup_of_le g (le_iSup_of_le (show g ∈ originalAffinePrincipalGeneratorElements q
        from ⟨i, hg⟩) le_rfl)
    exact hle hxg
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hopen

/-- Every produced original principal section module is finite over its SAME actual original section ring. -/
theorem originalAffinePrincipalGeneratorSections_finite
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (g : originalAffinePrincipalGeneratorElements q) :
    Module.Finite Γ(Spec A, PrimeSpectrum.basicOpen g.val)
      Γ(M, PrimeSpectrum.basicOpen g.val) := by
  obtain ⟨i, hi⟩ := g.property
  exact originalLocalGeneratorSubopenSections_finite q i _ hi

/-- Every produced original principal section module is free over its SAME actual original section ring. -/
theorem originalAffinePrincipalGeneratorSections_free
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (g : originalAffinePrincipalGeneratorElements q) :
    Module.Free Γ(Spec A, PrimeSpectrum.basicOpen g.val)
      Γ(M, PrimeSpectrum.basicOpen g.val) := by
  obtain ⟨i, hi⟩ := g.property
  exact originalLocalGeneratorSubopenSections_free q i _ hi

/-- Native actual principal-section projectivity follows from original generating maps, without a frame input. -/
theorem originalAffinePrincipalGeneratorSections_projective
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (g : originalAffinePrincipalGeneratorElements q) :
    Module.Projective Γ(Spec A, PrimeSpectrum.basicOpen g.val)
      Γ(M, PrimeSpectrum.basicOpen g.val) := by
  let := originalAffinePrincipalGeneratorSections_free q g
  exact Module.Projective.of_free

/-- The literal ORIGINAL top-to-principal section restriction map, with the native original scalar action. -/
def originalAffinePrincipalGeneratorRestriction
    (q : SheafOfModules.LocalGeneratorsData.{v} M)
    (g : originalAffinePrincipalGeneratorElements q) :
    Γ(M, ⊤) →ₗ[A] Γ(M, PrimeSpectrum.basicOpen g.val) := by
  let V : (Spec A).Opens := PrimeSpectrum.basicOpen g.val
  let a : V ⟶ (⊤ : (Spec A).Opens) := homOfLE le_top
  exact ((modulesSpecToSheaf.obj M).obj.map a.op).hom

/-- Actual affine quasicoherence proves localization for the SAME actual original principal restriction map. -/
instance originalAffinePrincipalGeneratorRestriction_isLocalizedModule
    [M.IsQuasicoherent] (q : SheafOfModules.LocalGeneratorsData.{v} M)
    (g : originalAffinePrincipalGeneratorElements q) :
    IsLocalizedModule.Away g.val (originalAffinePrincipalGeneratorRestriction q g) := by
  exact ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance) g.val

end Hironaka.Geometry.QuotGrassmann
