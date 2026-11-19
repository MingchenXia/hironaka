import Hironaka.Geometry.FiniteMorphismFlatteningComparison
import Hironaka.Algebra.FiniteMorphismFlatteningTorsion

/-!
# Finite-morphism flattening by an internally constructed projective modification

The native global transform is the actual scheme-theoretic closure of
the actual generic fibre in the original base-changed finite scheme.
Its affine charts are the actual algebra tensor images. The original
finite algebra internally constructs the nonzero minor ideal, and the
actual finite blowup chart cover proves global native finite flatness.
This is the finite-morphism case, not the general proper-family theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.FiniteMorphismFlattening

open Algebra.FiniteMorphismFlattening Algebra.ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- The actual closed transform retains its literal projection to the original finite scheme. -/
abbrev globalTransformToOriginal (I : Ideal R) : globalTransform R A I ⟶ Spec (.of A) :=
  globalTransformInclusion R A I ≫ pullback.snd _ _

/-- The actual transform square commutes with the original finite morphism and original blowup. -/
@[reassoc (attr := simp)]
theorem globalTransformToOriginal_structure (I : Ideal R) :
    globalTransformToOriginal R A I ≫ originalMap R A =
      globalTransformMap R A I ≫ affineBlowupStructure I := by
  simp only [globalTransformToOriginal, globalTransformMap, Category.assoc]
  rw [← pullback.condition]

/-- The literal transform map to the original scheme is proper by the actual blowup base change. -/
theorem globalTransformToOriginal_isProper (I : Ideal R) (hfg : I.FG) :
    IsProper (globalTransformToOriginal R A I) := by
  let : IsProper (affineBlowupStructure I) := affineBlowupStructure_isProper I hfg
  dsimp only [globalTransformToOriginal]
  infer_instance

/-- Actual flatness of the internally constructed chart algebra images glues to
native flatness of the one global native generic-fibre closure. -/
theorem globalTransformMap_flat_of_minorCharts {n r : ℕ}
    (V : Matrix (Fin r) (Fin n) R)
    (hflat : ∀ s : (ModuleFlattening.minorFractionOpenCover V).I₀,
      Flat (chartTransformMap R A
        (affineBlowupFractionChart (minorIdeal V) (columnMinor V s.val)))) :
    Flat (globalTransformMap R A (minorIdeal V)) := by
  apply IsZariskiLocalAtTarget.of_openCover (ModuleFlattening.minorFractionOpenCover V)
  intro s
  let H := chartToGlobalTransform_isPullback R A (minorIdeal V)
    (columnMinor V s.val) (columnMinor_mem_minorIdeal V s.val) s.property
  change Flat (pullback.snd (globalTransformMap R A (minorIdeal V))
    (affineBlowupChartInclusion (minorIdeal V) (columnMinor V s.val)
      (columnMinor_mem_minorIdeal V s.val) s.property))
  apply (MorphismProperty.cancel_left_of_respectsIso @Flat H.isoPullback.hom _).mp
  rw [H.isoPullback_hom_snd]
  exact hflat s

/-- A finite algebra over an arbitrary domain internally constructs an actual
projective modification of the base whose native generic-fibre strict transform
is globally finite and flat. The transform retains its original algebra structure,
including possible nilpotents; no geometric flattening certificate is assumed. -/
theorem exists_projective_modification_finite_flat_transform [Module.Finite R A] :
    ∃ (n r : ℕ) (m : Fin n → A) (V : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal V).FG ∧ minorIdeal V ≠ ⊥ ∧
      IsProjectiveOver (affineBlowupStructure (minorIdeal V)) ∧
      IsModification (affineBlowupStructure (minorIdeal V)) ∧
      IsFinite (globalTransformMap R A (minorIdeal V)) ∧
      Flat (globalTransformMap R A (minorIdeal V)) := by
  obtain ⟨n, r, m, V, hm, hfg, hI, hp, hmod, hcharts⟩ :=
    exists_projective_modification_finite_flat_chartTransforms R A
  exact ⟨n, r, m, V, hm, hfg, hI, hp, hmod, inferInstance,
    globalTransformMap_flat_of_minorCharts R A V fun s ↦ (hcharts s).2⟩

end Hironaka.Geometry.FiniteMorphismFlattening
