import Hironaka.Algebra.NodeGeometricCompletionOriginalFiberSection
import Mathlib.RingTheory.Localization.Submodule

/-! Internal essential finite type and Noetherianity of the ORIGINAL local closed fibre over its native base residue field. -/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletionFiberFiniteType

open NodeGeometricCompletionOriginalFiberSection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A]
  [Algebra A B]

local notation "Q" => FiberRing A B
local notation "k" => ResidueField A

attribute [local instance] baseResidueAlgebra

/-- The SAME actual original quotient algebra agrees with its entire native base-residue coefficient map. -/
theorem baseResidue_scalarTower : IsScalarTower A k Q := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (CompletionLocalMap.closedFiberIdeal (algebraMap A B))
    (algebraMap A B a) = baseResidueMap A B (residue A a)
  exact (baseResidueMap_residue A B a).symm

variable [Algebra.EssFiniteType A B]

/-- Original essential finite type descends to the literal closed fibre over its SAME native base residue field. -/
theorem fiber_essFiniteType : Algebra.EssFiniteType k Q := by
  let := baseResidue_scalarTower A B
  let : Algebra.EssFiniteType A Q := Algebra.EssFiniteType.comp A B Q
  exact Algebra.EssFiniteType.of_comp A k Q

/-- Noetherianity of the actual original local closed fibre follows over the residue FIELD, with no Noetherian base hypothesis. -/
theorem fiber_isNoetherianRing : IsNoetherianRing Q := by
  let := fiber_essFiniteType A B
  exact Algebra.EssFiniteType.isNoetherianRing k Q

end Hironaka.Algebra.NodeGeometricCompletionFiberFiniteType
