import DeJongAlterations.Geometry.AlgebraicFieldFiniteModel
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! Actual scalar integrality descends; an integral finite field model is INTERNALLY constructed. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteIntegralModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual integral scalar geometry proves original integrality on the SAME native field square. -/
theorem isIntegral_of_scalar_pullback {E L : Type u} [Field E] [Field L] (φ : E →+* L)
    {Y YL : Scheme.{u}} (p : Y ⟶ Spec (.of E)) {g : YL ⟶ Y} {pL : YL ⟶ Spec (.of L)}
    (H : IsPullback g pL p (Spec.map (CommRingCat.ofHom φ))) [IsIntegral YL] :
    IsIntegral Y := by
  let c := Spec.map (CommRingCat.ofHom φ)
  let : Surjective c := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  let : IsSchemeTheoreticallyDominant c := IsSchemeTheoreticallyDominant.of_isDominant c
  let : Flat p := inferInstance
  let : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isPullback H.flip
  let : QuasiCompact g := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced g
  let : Surjective g := MorphismProperty.of_isPullback H.flip inferInstance
  let : IrreducibleSpace Y := (irreducibleSpace_def Y).mpr (by
    change IsIrreducible (Set.univ : Set Y)
    simpa only [Set.image_univ, g.surjective.range_eq] using
      (IrreducibleSpace.isIrreducible_univ YL).image g g.continuous.continuousOn)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- ONLY actual integral FP scalar geometry INTERNALLY produces the actual integral finite
field model with its WHOLE original scalar and k-coefficient triangles. -/
theorem exists_integral_finite_field_model (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] {Y : Scheme.{u}} [IsIntegral Y] (p : Y ⟶ Spec (.of L))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p] :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ (Y₀ : Scheme.{u}) (p₀ : Y₀ ⟶ Spec (.of E)) (g : Y ⟶ Y₀),
        LocallyOfFinitePresentation p₀ ∧ QuasiCompact p₀ ∧ QuasiSeparated p₀ ∧
        IsIntegral Y₀ ∧
        IsPullback g p p₀ (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        g ≫ p₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
          p ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  obtain ⟨E, hfinite, Y₀, p₀, g, hfp, hqc, hqs, H, ht⟩ :=
    AlgebraicFieldFiniteModel.exists_finite_field_model k L p
  exact ⟨E, hfinite, Y₀, p₀, g, hfp, hqc, hqs,
    isIntegral_of_scalar_pullback E.val.toRingHom p₀ H, H, ht⟩

end DeJongAlterations.Geometry.AlgebraicFieldFiniteIntegralModel
