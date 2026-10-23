import DeJongAlterations.Algebra.NodeGeometricCompletionFieldSection
import DeJongAlterations.Algebra.CompletionLocalMapClosedFiber

/-! The ORIGINAL point residue field as actual coefficients in the literal completed original fibre. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionOriginalFiberSection

open CompletionRegularityBasics CompletionLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R T : Type u) [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
  [Algebra R T] [IsLocalHom (algebraMap R T)]

/-- The actual uncompleted original local fibre quotient. -/
abbrev FiberRing := T ⧸ closedFiberIdeal (algebraMap R T)

local instance fiberRing_local : IsLocalRing (FiberRing R T) :=
  CompletionIdealQuotient.quotientLocalRing _ (closedFiberIdeal_le_maximalIdeal (algebraMap R T))

local instance quotientMap_local : IsLocalHom (Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T))) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- The actual original base residue map into the original fibre quotient. -/
def baseResidueMap : ResidueField R →+* FiberRing R T :=
  Ideal.Quotient.lift (maximalIdeal R)
    ((Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T))).comp (algebraMap R T)) (by
      intro r hr
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_map_of_mem (algebraMap R T) hr)

omit [IsLocalRing T] [IsLocalHom (algebraMap R T)] in
/-- The original coefficient formula on every original residue representative. -/
theorem baseResidueMap_residue (r : R) :
    baseResidueMap R T (residue R r) =
      Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T)) (algebraMap R T r) := rfl

/-- The exact original base-residue algebra on the actual fibre quotient. -/
@[instance_reducible]
def baseResidueAlgebra : Algebra (ResidueField R) (FiberRing R T) := (baseResidueMap R T).toAlgebra

attribute [local instance] baseResidueAlgebra

/-- The actual original quotient residue map is surjective. -/
theorem quotientResidue_surjective :
    Function.Surjective (ResidueField.map (Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T)))) := by
  intro a
  obtain ⟨q, rfl⟩ := residue_surjective a
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨residue T t, ResidueField.map_residue _ _⟩

/-- The canonical residue identification of the ORIGINAL quotient map. -/
def quotientResidueEquiv : ResidueField T ≃+* ResidueField (FiberRing R T) :=
  RingEquiv.ofBijective (ResidueField.map (Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T))))
    ⟨RingHom.injective _, quotientResidue_surjective R T⟩

variable [IsNoetherianRing T]

/-- The actual canonical original point residue field of the completed original fibre. -/
def originalResidueEquiv : ResidueField T ≃+* ResidueField (Completion (FiberRing R T)) :=
  (quotientResidueEquiv R T).trans (residueFieldEquiv (FiberRing R T))

/-- Every actual original target residue representative retains its literal completed quotient image. -/
theorem originalResidueEquiv_residue (t : T) :
    originalResidueEquiv R T (residue T t) =
      residue (Completion (FiberRing R T)) (algebraMap (FiberRing R T) (Completion (FiberRing R T))
        (Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T)) t)) := by
  change residueFieldEquiv (FiberRing R T)
    (ResidueField.map (Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T))) (residue T t)) = _
  rw [ResidueField.map_residue, residueFieldEquiv_apply, ResidueField.map_residue]

/-- The actual completed fibre coefficient action is exactly the original point residue extension. -/
theorem originalResidue_triangle :
    algebraMap (ResidueField R) (ResidueField (Completion (FiberRing R T))) =
      (originalResidueEquiv R T).toRingHom.comp (algebraMap (ResidueField R) (ResidueField T)) := by
  ext a
  obtain ⟨r, rfl⟩ := residue_surjective a
  change residue (Completion (FiberRing R T))
      (algebraMap (ResidueField R) (Completion (FiberRing R T)) (residue R r)) =
        originalResidueEquiv R T (algebraMap (ResidueField R) (ResidueField T) (residue R r))
  rw [ResidueField.algebraMap_residue, originalResidueEquiv_residue]
  rfl

variable [FiniteDimensional (ResidueField R) (ResidueField T)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField T)]

local instance completedFiberResidue_finite :
    FiniteDimensional (ResidueField R) (ResidueField (Completion (FiberRing R T))) :=
  Module.Finite.of_equiv_equiv (RingEquiv.refl (ResidueField R)) (originalResidueEquiv R T)
    (by ext a; exact RingHom.congr_fun (originalResidue_triangle R T) a)

local instance completedFiberResidue_separable :
    Algebra.IsSeparable (ResidueField R) (ResidueField (Completion (FiberRing R T))) :=
  Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField R)) (originalResidueEquiv R T)
    (by ext a; exact RingHom.congr_fun (originalResidue_triangle R T) a)

local instance completedFiberBase_local :
    IsLocalHom (algebraMap (ResidueField R) (Completion (FiberRing R T))) := by
  infer_instance

/-- The ORIGINAL actual point residue field as internally constructed coefficients
in the literal completed original fibre quotient. -/
def pointFieldSection : ResidueField T →+* Completion (FiberRing R T) :=
  (NodeGeometricCompletionFieldSection.fieldSection (ResidueField R) (Completion (FiberRing R T))).comp
    (originalResidueEquiv R T).toRingHom

/-- The literal residue formula is the canonical ORIGINAL point residue identification. -/
theorem residue_pointFieldSection (a : ResidueField T) :
    residue (Completion (FiberRing R T)) (pointFieldSection R T a) = originalResidueEquiv R T a :=
  NodeGeometricCompletionFieldSection.residue_fieldSection _ _ _

/-- Through the actual original residue identification the entire residue composite is the identity. -/
theorem originalResidueProjection_comp_pointFieldSection :
    (originalResidueEquiv R T).symm.toRingHom.comp
      ((residue (Completion (FiberRing R T))).comp (pointFieldSection R T)) = RingHom.id _ := by
  ext a
  change (originalResidueEquiv R T).symm
    (residue (Completion (FiberRing R T)) (pointFieldSection R T a)) = a
  rw [residue_pointFieldSection, RingEquiv.symm_apply_apply]

/-- The whole ORIGINAL base point residue field action is retained, not just a primitive generator. -/
theorem pointFieldSection_base (a : ResidueField R) :
    pointFieldSection R T (algebraMap (ResidueField R) (ResidueField T) a) =
      algebraMap (ResidueField R) (Completion (FiberRing R T)) a := by
  change NodeGeometricCompletionFieldSection.fieldSection _ _
    (originalResidueEquiv R T (algebraMap (ResidueField R) (ResidueField T) a)) = _
  have he := RingHom.congr_fun (originalResidue_triangle R T) a
  change algebraMap (ResidueField R) (ResidueField (Completion (FiberRing R T))) a =
    originalResidueEquiv R T (algebraMap (ResidueField R) (ResidueField T) a) at he
  rw [← he]
  exact (NodeGeometricCompletionFieldSection.fieldSectionAlgHom _ _).commutes a

/-- The actual coefficient triangle on the whole original base residue field. -/
theorem pointFieldSection_triangle :
    (pointFieldSection R T).comp (algebraMap (ResidueField R) (ResidueField T)) =
      algebraMap (ResidueField R) (Completion (FiberRing R T)) :=
  RingHom.ext (pointFieldSection_base R T)

/-- The actual new coefficient action is the constructed ORIGINAL point field section. -/
@[instance_reducible]
def pointFieldAlgebra : Algebra (ResidueField T) (Completion (FiberRing R T)) :=
  (pointFieldSection R T).toAlgebra

/-- The original point residue extension and new coefficients form the actual original scalar tower. -/
theorem pointFieldAlgebra_scalarTower :
    letI := pointFieldAlgebra R T
    IsScalarTower (ResidueField R) (ResidueField T) (Completion (FiberRing R T)) := by
  let := pointFieldAlgebra R T
  exact IsScalarTower.of_algebraMap_eq' (pointFieldSection_triangle R T).symm

/-- In particular every ORIGINAL base stalk coefficient has its literal completed quotient image. -/
theorem pointFieldSection_original (r : R) :
    pointFieldSection R T (residue T (algebraMap R T r)) =
      algebraMap (FiberRing R T) (Completion (FiberRing R T))
        (Ideal.Quotient.mk (closedFiberIdeal (algebraMap R T)) (algebraMap R T r)) := by
  rw [← ResidueField.algebraMap_residue, pointFieldSection_base]
  rfl

end DeJongAlterations.Algebra.NodeGeometricCompletionOriginalFiberSection
