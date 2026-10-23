import DeJongAlterations.Geometry.CurveCompactification
import DeJongAlterations.Geometry.CurveBoundary
import DeJongAlterations.Geometry.CurveBoundarySupport
import DeJongAlterations.Geometry.RegularSmoothConverse
import DeJongAlterations.Theorem

/-!
# Full alterations with prescribed strict-normal-crossings boundary for curves

The alteration is the actual global normalization. Its actual regular
projective compactification and the entire reduced boundary are constructed
internally. Generic etaleness is proved over every ground field; smoothness
of the compactification is asserted only over perfect fields.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CurveBoundary

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual full Theorem4.1 output for every dimension-at-most-one variety,
with generically etale normalization and finite reduced entire boundary. -/
theorem exists_alterationWithBoundary_curve
    (p : X ⟶ Spec (.of k)) [IsVariety p] (hdim : topologicalKrullDim X ≤ 1)
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    ∃ d : AlterationWithBoundary p (Z : Set X),
      IsGenericallyEtale d.alteration ∧ (d.boundary.support : Set d.compactification).Finite := by
  let N := NormalizationGluing.normalization X
  let a := NormalizationGluing.normalizationStructure X
  let pN := a ≫ p
  let : IsIntegral N := NormalizationFinite.isIntegral_normalization
  let : IsVariety pN := NormalizationFiniteArbitraryField.normalization_isVariety p
  let : IsAlteration a := NormalizationFiniteArbitraryField.normalizationStructure_isAlteration p
  have hnN : IsNormalScheme N := NormalizationGluing.normalization_isNormalScheme X
  have hdimN : topologicalKrullDim N ≤ 1 :=
    FunctionFieldDimension.topologicalKrullDim_normalization_le_one X hdim
  obtain ⟨C, pC, i, hvC, hpC, hi, _, hbase, hnC, hrC, hdimC⟩ :=
    CurveCompactification.exists_regular_projective_compactification pN hnN hdimN
  let := hvC
  let := hi
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace pC
  let : AlgebraicGeometry.IsNoetherian C := ⟨⟩
  let D := extendedBoundary a i Z
  have hW : extendedClosed a i Z ≠ ⊤ := extendedClosed_ne_top a i Z hZ
  have hsnc : IsStrictNormalCrossings D :=
    isStrictNormalCrossings_vanishingIdeal hnC hdimC (extendedClosed a i Z) hW
  let d : AlterationWithBoundary p (Z : Set X) := {
    source := N
    compactification := C
    sourceStructure := pN
    compactificationStructure := pC
    alteration := a
    inclusion := i
    boundary := D
    sourceVariety := inferInstance
    compactificationVariety := inferInstance
    alterationOver := rfl
    inclusionOver := hbase
    isAlteration := inferInstance
    isOpenImmersion := inferInstance
    projective := hpC
    regular := hrC
    normalCrossings := hsnc
    boundarySupport := extendedBoundary_support a i Z }
  exact ⟨d, NormalizationFiniteArbitraryField.normalizationStructure_isGenericallyEtale p,
    finite_support hdimC D hW⟩

/-- Full curve alterations over perfect fields, including smooth projective
compactification and the same actual generically etale alteration. -/
theorem exists_alterationWithBoundary_curve_perfect [PerfectField k]
    (p : X ⟶ Spec (.of k)) [IsVariety p] (hdim : topologicalKrullDim X ≤ 1)
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    ∃ d : AlterationWithBoundary p (Z : Set X),
      IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure := by
  obtain ⟨d, hge, _⟩ := exists_alterationWithBoundary_curve p hdim Z hZ
  let := d.compactificationVariety
  exact ⟨d, hge, RegularSmoothConverse.smooth_of_isRegularScheme
    d.compactificationStructure d.regular⟩

end DeJongAlterations.Geometry.CurveBoundary
