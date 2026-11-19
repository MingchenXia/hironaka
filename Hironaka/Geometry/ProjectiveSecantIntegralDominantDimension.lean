import Hironaka.Geometry.ProjectiveSecantIntegralDimension
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Actual dominant integral maps preserve the original finite-type target dimension
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original coordinate ring of any specified original nonempty affine open has the whole original integral field-scheme dimension. -/
theorem ringKrullDim_affineSections_eq_original
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] (V : Y.affineOpens) [Nonempty V.1] :
    ringKrullDim Γ(Y, V.1) = topologicalKrullDim Y := by
  obtain ⟨d, hY, htr⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
  exact (FunctionFieldDimension.affineSections_dimension_eq p V d htr).trans hY.symm

/-- Integral dominance internally preserves original dimension, without any source reducedness, integrality, Noetherianity or finite-type hypothesis. -/
theorem topologicalKrullDim_eq_of_integral_dominant
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsIntegralHom f] [IsDominant f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  apply le_antisymm (topologicalKrullDim_le_of_isIntegralHom f)
  let V := RationalCoordinateMap.coordinateOpen (X := Y) (fun j : Fin 0 => j.elim0)
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have hint := f.isIntegral_app V.1 V.2
  have hinj : Function.Injective (f.app V.1).hom := by
    simpa only [Scheme.Hom.app_eq_appLE] using f.app_injective V.1
  have hlower := Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral_of_injective
    (f.app V.1).hom hint hinj
  have hsource := (V.2.preimage f).fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(X, f ⁻¹ᵁ V.1)) ≤ topologicalKrullDim X at hsource
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hsource
  calc
    topologicalKrullDim Y = ringKrullDim Γ(Y, V.1) := (ringKrullDim_affineSections_eq_original p V).symm
    _ ≤ ringKrullDim Γ(X, f ⁻¹ᵁ V.1) := hlower
    _ ≤ topologicalKrullDim X := hsource

end Hironaka.Geometry.ProjectiveSecant
