import DeJongAlterations.StableModification.Limits.Descent
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Actual finite intermediate-field scheme models, with the ORIGINAL scalar coefficient maps. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteModel

open StableModification.Limits

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

/-- The actual finite-generation levels inside the ORIGINAL algebraic scalar field. -/
abbrev Index : Type u := (FGSubalgebra k (⊤ : Subalgebra k L))ᵒᵖ

/-- The SAME actual level subalgebra is canonically an intermediate FIELD. -/
def levelField (i : Index k L) : IntermediateField k L :=
  Subalgebra.IsAlgebraic.toIntermediateField (S := i.unop.1)
    (by intro x _; exact Algebra.IsAlgebraic.isAlgebraic x)

/-- Finite generation and original algebraicity INTERNALLY prove finite field dimension. -/
theorem levelField_finiteDimensional (i : Index k L) :
    FiniteDimensional k (levelField k L i) := by
  let : Algebra.FiniteType k (levelField k L i) :=
    (Subalgebra.fg_iff_finiteType i.unop.1).mp i.unop.2.1
  exact Algebra.IsIntegral.finite

/-- The actual directed coefficient rings, contravariantly on their native spectra. -/
abbrev diagram : Index k L ⥤ Scheme.{u} :=
  (fgDiagram (⊤ : Subalgebra k L)).op ⋙ Scheme.Spec

/-- The canonical original scalar field identifies with its actual top subalgebra. -/
def topScalarIso : Spec (.of L) ≅ (fgSpecCone (⊤ : Subalgebra k L)).pt :=
  Scheme.Spec.mapIso (Subalgebra.topEquiv : (⊤ : Subalgebra k L) ≃ₐ[k] L).toRingEquiv.toCommRingCatIso.op

/-- The limit cone has apex the ORIGINAL Spec L, with no supplied comparison. -/
def scalarCone : Cone (diagram k L) :=
  (fgSpecCone (⊤ : Subalgebra k L)).extend (topScalarIso k L).hom

/-- Each whole native cone map is the SAME prescribed original finite-field coefficient map. -/
theorem scalarCone_π (i : Index k L) :
    (scalarCone k L).π.app i =
      Spec.map (CommRingCat.ofHom (levelField k L i).val.toRingHom) := by
  change Spec.map (CommRingCat.ofHom (Subalgebra.topEquiv :
      (⊤ : Subalgebra k L) ≃ₐ[k] L).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.unop.2.2).toRingHom) = _
  rw [← Spec.map_comp]
  rfl

/-- The ORIGINAL Spec L is the actual limit of the constructed finite field levels. -/
def isLimitScalarCone : IsLimit (scalarCone k L) :=
  IsLimit.extendIso (topScalarIso k L).hom (isLimitFGSpecCone (⊤ : Subalgebra k L))

/-- The ENTIRE original k-coefficient triangle is retained for each actual finite field level. -/
theorem levelField_coefficient_triangle (i : Index k L) :
    Spec.map (CommRingCat.ofHom (levelField k L i).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i))) =
        Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  rw [← Spec.map_comp]
  rfl

/-- ANY actual FP scalar scheme INTERNALLY produces an actual finite intermediate-field model,
the WHOLE canonical scalar Cartesian square, and the ENTIRE original k-structure triangle.
No model, reducedness or geometric-integrality certificate is assumed. -/
theorem exists_finite_field_model {Y : Scheme.{u}} (p : Y ⟶ Spec (.of L))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p] :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ (Y₀ : Scheme.{u}) (p₀ : Y₀ ⟶ Spec (.of E)) (g : Y ⟶ Y₀),
        LocallyOfFinitePresentation p₀ ∧ QuasiCompact p₀ ∧ QuasiSeparated p₀ ∧
        IsPullback g p p₀ (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        g ≫ p₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
          p ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  obtain ⟨i, m, hm⟩ := exists_model (isLimitScalarCone k L) p
  have H := m.isPullback
  rw [scalarCone_π] at H
  refine ⟨levelField k L i, levelField_finiteDimensional k L i, m.Y, m.fY, m.g,
    hm.1, hm.2.1, hm.2.2, H, ?_⟩
  rw [H.w_assoc, levelField_coefficient_triangle]

end DeJongAlterations.Geometry.AlgebraicFieldFiniteModel
