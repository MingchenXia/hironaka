import Hironaka.Geometry.NodeNormal
import Hironaka.Geometry.MonomialBlowupTowerRegular

/-! Actual normality of every processed prefix stage of the literal finite node tower. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.NodeNormalTower

open MonomialBlowupTower MonomialBlowupTowerCharts

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

/-- Every actual prefix blowup stage over a normal domain is normal, without a Noetherian hypothesis. -/
theorem prefix_isNormalScheme (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) : IsNormalScheme (tower l a.length).left := by
  obtain ⟨S⟩ := MonomialBlowupTowerRegular.nonempty_charts l hl a b hab
  apply NodeNormal.isNormalScheme_of_openCover _ S.openCover
  intro i
  cases i with
  | none => exact NodeNormal.node_isNormalScheme _ S.remaining_ne_zero
  | some i => exact NodeNormal.node_isNormalScheme _ (S.factor_ne_zero i)

/-- The actual final global finite node blowup tower is normal over every integrally closed domain. -/
theorem resolved_isNormalScheme (l : List A) (hl : (0 : A) ∉ l) :
    IsNormalScheme (resolved l) := by
  exact prefix_isNormalScheme l hl l [] (by simp)

end Hironaka.Geometry.NodeNormalTower
