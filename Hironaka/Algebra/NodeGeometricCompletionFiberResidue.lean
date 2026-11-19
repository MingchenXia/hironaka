import Hironaka.Algebra.NodeGeometricCompletionOriginalFiberSection

/-! The ORIGINAL point and closed-fibre native residue fields with ALL original coefficient maps. -/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletionFiberResidue

open NodeGeometricCompletionOriginalFiberSection CompletionLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

local notation "k" => ResidueField A
local notation "Q" => FiberRing A B

local instance actualFiberLocalRing : IsLocalRing Q :=
  CompletionIdealQuotient.quotientLocalRing _ (closedFiberIdeal_le_maximalIdeal (algebraMap A B))

local instance actualQuotientLocal : IsLocalHom (Ideal.Quotient.mk (closedFiberIdeal (algebraMap A B))) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

attribute [local instance] baseResidueAlgebra

/-- The canonical ORIGINAL quotient residue equivalence preserves the WHOLE actual original base residue field. -/
def quotientResidueAlgEquiv : ResidueField B ≃ₐ[k] ResidueField Q := by
  refine AlgEquiv.ofRingEquiv (f := quotientResidueEquiv A B) ?_
  intro a
  obtain ⟨r, rfl⟩ := residue_surjective a
  change ResidueField.map (Ideal.Quotient.mk (closedFiberIdeal (algebraMap A B)))
    (algebraMap k (ResidueField B) (residue A r)) = residue Q (baseResidueMap A B (residue A r))
  rw [ResidueField.algebraMap_residue, ResidueField.map_residue, baseResidueMap_residue]

/-- Every ORIGINAL local representative retains its SAME native quotient residue image. -/
theorem quotientResidueAlgEquiv_residue (b : B) :
    quotientResidueAlgEquiv A B (residue B b) =
      residue Q (Ideal.Quotient.mk (closedFiberIdeal (algebraMap A B)) b) :=
  ResidueField.map_residue _ b

/-- Original residue finiteness transfers through the SAME canonical original quotient residue equivalence. -/
theorem quotientResidue_finite [FiniteDimensional k (ResidueField B)] :
    FiniteDimensional k (ResidueField Q) :=
  Module.Finite.of_equiv_equiv (RingEquiv.refl k) (quotientResidueAlgEquiv A B).toRingEquiv
    (by ext a; exact ((quotientResidueAlgEquiv A B).commutes a).symm)

/-- Original residue separability transfers through the ENTIRE original coefficient triangle. -/
theorem quotientResidue_separable [Algebra.IsSeparable k (ResidueField B)] :
    Algebra.IsSeparable k (ResidueField Q) :=
  Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl k) (quotientResidueAlgEquiv A B).toRingEquiv
    (by ext a; exact ((quotientResidueAlgEquiv A B).commutes a).symm)

variable (L : Type u) [Field L] [Algebra (ResidueField B) L]

/-- The WHOLE actual original base field embedding, through the prescribed ORIGINAL point field. -/
@[instance_reducible]
def originalBaseFieldAlgebra : Algebra k L :=
  ((algebraMap (ResidueField B) L).comp (algebraMap k (ResidueField B))).toAlgebra

/-- The prescribed ORIGINAL selected embedding is transferred through the SAME actual quotient residue map. -/
@[instance_reducible]
def quotientPointAlgebra : Algebra (ResidueField Q) L :=
  ((algebraMap (ResidueField B) L).comp (quotientResidueAlgEquiv A B).symm.toRingHom).toAlgebra

/-- The ENTIRE actual selected-field scalar triangle retains the original base coefficient embedding. -/
theorem quotientPoint_base_triangle :
    letI := originalBaseFieldAlgebra A B L
    letI := quotientPointAlgebra A B L
    algebraMap k L = (algebraMap (ResidueField Q) L).comp (algebraMap k (ResidueField Q)) := by
  let := originalBaseFieldAlgebra A B L
  let := quotientPointAlgebra A B L
  apply RingHom.ext
  intro a
  change algebraMap (ResidueField B) L (algebraMap k (ResidueField B) a) =
    algebraMap (ResidueField B) L ((quotientResidueAlgEquiv A B).symm
      (algebraMap k (ResidueField Q) a))
  rw [AlgEquiv.commutes]

/-- The SAME original base and actual closed-fibre point coefficients form a native scalar tower. -/
theorem quotientPoint_scalarTower :
    letI := originalBaseFieldAlgebra A B L
    letI := quotientPointAlgebra A B L
    IsScalarTower k (ResidueField Q) L := by
  let := originalBaseFieldAlgebra A B L
  let := quotientPointAlgebra A B L
  exact IsScalarTower.of_algebraMap_eq' (quotientPoint_base_triangle A B L)

/-- EVERY original local germ retains EXACTLY the prescribed ORIGINAL residue image through the actual closed fibre. -/
theorem quotientPoint_original (b : B) :
    letI := quotientPointAlgebra A B L
    algebraMap (ResidueField Q) L
      (residue Q (Ideal.Quotient.mk (closedFiberIdeal (algebraMap A B)) b)) =
        algebraMap (ResidueField B) L (residue B b) := by
  let := quotientPointAlgebra A B L
  change algebraMap (ResidueField B) L
    ((quotientResidueAlgEquiv A B).symm (quotientResidueAlgEquiv A B (residue B b))) = _
  rw [AlgEquiv.symm_apply_apply]

end Hironaka.Algebra.NodeGeometricCompletionFiberResidue
