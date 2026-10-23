import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension
import DeJongAlterations.Geometry.NormalizationGluing

/-! # Native normalization does not increase actual scheme dimension -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FunctionFieldDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual normalization cover and integral-extension incomparability bound dimension. -/
theorem topologicalKrullDim_normalization_le (X : Scheme.{u}) [IsIntegral X] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) :
    topologicalKrullDim (NormalizationGluing.normalization X) ≤ d := by
  apply topologicalKrullDim_le_of_openCover _ d (NormalizationGluing.normalizationCover X)
  intro U
  change topologicalKrullDim (PrimeSpectrum (NormalizationGluing.closureRing U)) ≤ d
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have hint := Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral
    (algebraMap Γ(X, U.1.1) (NormalizationGluing.closureRing U))
    (algebraMap_isIntegral_iff.mpr inferInstance)
  have hle := U.1.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(X, U.1.1)) ≤ topologicalKrullDim X at hle
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hle
  exact hint.trans (hle.trans hdim)

/-- The exact dimension-one consumer for actual global curve normalization. -/
theorem topologicalKrullDim_normalization_le_one (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim (NormalizationGluing.normalization X) ≤ 1 :=
  topologicalKrullDim_normalization_le X 1 hdim

end DeJongAlterations.Geometry.FunctionFieldDimension
