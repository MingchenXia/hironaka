import Hironaka.Geometry.ProjectiveSecantIntegralSchemeOpenDescent
import Hironaka.Geometry.ProjectiveSpaceBaseChange
import Hironaka.Geometry.ProjectiveCurveFibrationCharts

/-!
# Genuine original projective parameter opens below actual algebraic scalar opens
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveSpaceBaseChange

universe u

/-- The exact whole original projective coefficient square internally makes the actual algebraic scalar morphism integral. -/
theorem projectiveCoefficientMap_isIntegralHom
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] (m : ℕ) :
    IsIntegralHom (projectiveCoefficientMap (algebraMap k L) m) := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  exact MorphismProperty.of_isPullback (isPullback_projectiveCoefficientMap (algebraMap k L) m).flip
    inferInstance

/-- Every specified actual nonempty algebraic scalar projective open internally contains the literal inverse image of an actual nonempty ORIGINAL projective parameter open. -/
theorem exists_original_projective_open_under_algebraicScalar
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] (m : ℕ)
    (O : (projectiveSpace L m).Opens) (hO : (O : Set (projectiveSpace L m)).Nonempty) :
    ∃ U : (projectiveSpace k m).Opens, (U : Set (projectiveSpace k m)).Nonempty ∧
      (projectiveCoefficientMap (algebraMap k L) m ⁻¹ᵁ U) ≤ O := by
  let : IsIntegralHom (projectiveCoefficientMap (algebraMap k L) m) :=
    projectiveCoefficientMap_isIntegralHom k L m
  exact exists_nonempty_base_open_of_integral (projectiveCoefficientMap (algebraMap k L) m) O hO

end Hironaka.Geometry.ProjectiveSecant
