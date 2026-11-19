import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackSections
import Hironaka.Geometry.QuotGrassmannPivotOverSchemeCoefficients
import Hironaka.Geometry.QuotGrassmannPivotScalarNaturality

/-!
# Actual ORIGINAL global contraction coefficients under the ORIGINAL polynomial-pivot pullback

These are whole original native unit endomorphisms transported through the
actual open-scheme equivalence and genuine Scheme.Modules pullback functor.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The ACTUAL original contraction's native pulled-back coefficient is its SAME original polynomial entry. -/
theorem originalOverContractionEntry_truePullback_one_top
    (a : ι ⊕ ν) (row : (ι → ι ⊕ ν) × ι) :
    (originalPullbackUnitEnd (pivotMatrixSchemeIso R e).inv
      (originalOverEquivUnitEnd (projectiveModel R ι ν)
        (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
        (originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e) a row))).val.app
          (.op ⊤) (1 : Γ(affineChart R ι κ, ⊤)) =
      originalAffineCoefficientMap (ChartRing R ι κ) ⊤
        (originalContractionMatrix (Equiv.refl (ι → ι ⊕ ν)) (pivotUniversalMatrix R e) row a) := by
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let b := originalOverContractionEntry R ι ν (pivotIndex (coordinateSelector ι ν) e) a row
  let v := originalContractionMatrix (Equiv.refl (ι → ι ⊕ ν)) (pivotUniversalMatrix R e) row a
  have h := originalOverSchemePullbackUnitEnd_one_top U (pivotMatrixSchemeIso R e).inv b
  have hp := congrArg (fun z => (pivotMatrixSchemeIso R e).inv.appTop (U.topIso.inv z))
    (originalOverContractionEntry_polynomial R e a row)
  have ht := ConcreteCategory.congr_hom (originalPivotMatrixSchemeIso_sectionTriangle R e) v
  exact h.trans (hp.trans ht)

end Hironaka.Geometry.QuotGrassmann
