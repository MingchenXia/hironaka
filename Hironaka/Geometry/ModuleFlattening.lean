import Hironaka.Geometry.ModuleFlatteningCover
import Hironaka.Geometry.AffineBlowupBirational
import Hironaka.Geometry.AffineBlowupProjective
import Hironaka.Geometry.Modification

/-!
# An actual projective modification with free original finite-module pure transform

The nonzero finitely generated ideal and actual finite minor-chart cover are
constructed from the original finite module. The projective modification is
the literal native blowup, and every chart uses the actual canonical tensor
image, with native freeness, finiteness and computed rank.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct

namespace Hironaka.Geometry.ModuleFlattening

open Algebra.ModuleFlatteningMinors Algebra.ModuleFlatteningMinorsPureTransform
  Algebra.ModuleFlatteningMinorsExistence

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native blowup of a nonzero original minor ideal is a modification. -/
theorem minorBlowup_isModification
    {R : Type u} [CommRing R] [IsDomain R] {n r : ℕ}
    (A : Matrix (Fin r) (Fin n) R) (hI : minorIdeal A ≠ ⊥) (hfg : (minorIdeal A).FG) :
    IsModification (affineBlowupStructure (minorIdeal A)) := by
  let : IsIntegral (affineBlowup (minorIdeal A)) := ProjIntegral.isIntegral_affineBlowup _ hI
  let : IsProper (affineBlowupStructure (minorIdeal A)) := affineBlowupStructure_isProper _ hfg
  exact { sourceIntegral := inferInstance
          targetIntegral := inferInstance
          birational := affineBlowupStructure_birationalOver _ hI }

/-- The original finite module internally constructs an actual projective modification,
with actual native finite minor-chart cover on which its canonical tensor-image pure
transform is free and finite of the internally computed generic rank. -/
theorem exists_projective_modification_free_pureTransform
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    ∃ (n r : ℕ) (m : Fin n → M) (A : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal A).FG ∧ minorIdeal A ≠ ⊥ ∧
      IsProjectiveOver (affineBlowupStructure (minorIdeal A)) ∧
      IsModification (affineBlowupStructure (minorIdeal A)) ∧
      IsAlteration (affineBlowupStructure (minorIdeal A)) ∧
      ∀ s : (minorFractionOpenCover A).I₀,
        let S := affineBlowupFractionChart (minorIdeal A) (columnMinor A s.val)
        Module.Free S (pureTransform R M S) ∧ Module.Finite S (pureTransform R M S) ∧
          Module.finrank S (pureTransform R M S) = r := by
  obtain ⟨n, r, m, A, hm, hfg, hI, hfree⟩ :=
    exists_nonzero_minorIdeal_free_finite_rank_pureTransform R M
  exact ⟨n, r, m, A, hm, hfg, hI, affineBlowupStructure_isProjective _ hfg,
    minorBlowup_isModification A hI hfg, affineBlowupStructure_isAlteration _ hI hfg,
    fun s ↦ hfree s.val s.property⟩


/-- Native module flatness of the actual original pure transform on the internally
constructed finite cover of the actual projective modification. -/
theorem exists_projective_modification_flat_pureTransform
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    ∃ (n r : ℕ) (m : Fin n → M) (A : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal A).FG ∧ minorIdeal A ≠ ⊥ ∧
      IsProjectiveOver (affineBlowupStructure (minorIdeal A)) ∧
      IsModification (affineBlowupStructure (minorIdeal A)) ∧
      ∀ s : (minorFractionOpenCover A).I₀,
        let S := affineBlowupFractionChart (minorIdeal A) (columnMinor A s.val)
        Module.Flat S (pureTransform R M S) ∧ Module.Finite S (pureTransform R M S) ∧
          Module.finrank S (pureTransform R M S) = r := by
  obtain ⟨n, r, m, A, hm, hfg, hI, hp, hmod, halt, hfree⟩ :=
    exists_projective_modification_free_pureTransform R M
  refine ⟨n, r, m, A, hm, hfg, hI, hp, hmod, fun s ↦ ?_⟩
  obtain ⟨hf, hfin, hrank⟩ := hfree s
  let : Module.Free (affineBlowupFractionChart (minorIdeal A) (columnMinor A s.val))
      (pureTransform R M (affineBlowupFractionChart (minorIdeal A) (columnMinor A s.val))) := hf
  exact ⟨inferInstance, hfin, hrank⟩

end Hironaka.Geometry.ModuleFlattening
