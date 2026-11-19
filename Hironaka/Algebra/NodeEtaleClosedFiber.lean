import Hironaka.Algebra.NodeEtaleFlat
import Hironaka.Algebra.NodeNonsplitPresentation

/-! # Actual upper closed fibre and the original quotient, with forward coefficient actions -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleClosedFiber

open IsLocalRing NodeEtaleCoefficients NodeFlatPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

attribute [local instance] residueAlgebra idealResidueAlgebra

variable [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  [IsAdicComplete (maximalIdeal B) B]

local notation "T" => CoefficientRing A B
local notation "F" => ClosedFiber A B
local instance : Algebra T B := coefficientTargetAlgebra A B
local instance : IsLocalHom (algebraMap T B) := coefficientMap_isLocalHom A B

/-- The WHOLE actual upper closed-fibre ideal is precisely the original lower one. -/
theorem upperClosedFiberIdeal_eq : closedFiberIdeal T B = closedFiberIdeal A B :=
  NodeEtaleFlat.coefficientTarget_maximalIdeal_image A B

/-- The same native B quotients are identified by the actual full ideal equality. -/
def upperClosedFiberRingEquiv : ClosedFiber T B ≃+* F :=
  Ideal.quotEquivOfEq (upperClosedFiberIdeal_eq A B)

/-- EVERY original completed-target representative remains precisely that representative. -/
theorem upperClosedFiberRingEquiv_mk (b : B) :
    upperClosedFiberRingEquiv A B (Ideal.Quotient.mk (closedFiberIdeal T B) b) =
      Ideal.Quotient.mk (closedFiberIdeal A B) b :=
  Ideal.quotEquivOfEq_mk _ b

/-- The entire forward composite is the SAME original lower quotient map. -/
theorem upperClosedFiberRingEquiv_wholeMap :
    (upperClosedFiberRingEquiv A B).toRingHom.comp (Ideal.Quotient.mk (closedFiberIdeal T B)) =
      Ideal.Quotient.mk (closedFiberIdeal A B) :=
  RingHom.ext (upperClosedFiberRingEquiv_mk A B)

/-- The actual upper residue action is the quotient lift of the forward original coefficient map only. -/
def upperResidueMap : ResidueField T →+* F :=
  Ideal.Quotient.lift (maximalIdeal T)
    ((Ideal.Quotient.mk (closedFiberIdeal A B)).comp (coefficientMap A B).toRingHom) (by
      intro t ht
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← upperClosedFiberIdeal_eq A B]
      exact Ideal.mem_map_of_mem (algebraMap T B) ht)

/-- EVERY actual upper residue representative retains its SAME actual forward coefficient image. -/
theorem upperResidueMap_residue (t : T) :
    upperResidueMap A B (residue T t) =
      Ideal.Quotient.mk (closedFiberIdeal A B) (coefficientMap A B t) := rfl

/-- The native original lower quotient receives only the actual forward upper residue action. -/
@[instance_reducible]
def upperResidueAlgebra : Algebra (ResidueField T) F := (upperResidueMap A B).toAlgebra

local instance : Algebra (ResidueField T) F := upperResidueAlgebra A B
local instance : Algebra (ResidueField T) (ClosedFiber T B) := closedFiberAlgebra T B

/-- The actual same-ring upper/lower quotient equivalence preserves the ENTIRE native upper residue action. -/
def upperClosedFiberEquiv : ClosedFiber T B ≃ₐ[ResidueField T] F := by
  refine AlgEquiv.ofRingEquiv (f := upperClosedFiberRingEquiv A B) ?_
  intro a
  obtain ⟨t, rfl⟩ := residue_surjective a
  change upperClosedFiberRingEquiv A B
    (Ideal.Quotient.mk (closedFiberIdeal T B) (algebraMap T B t)) = _
  exact upperClosedFiberRingEquiv_mk A B (algebraMap T B t)

/-- EVERY original B representative follows the SAME actual upper/lower equivalence. -/
theorem upperClosedFiberEquiv_mk (b : B) :
    upperClosedFiberEquiv A B (Ideal.Quotient.mk (closedFiberIdeal T B) b) =
      Ideal.Quotient.mk (closedFiberIdeal A B) b :=
  upperClosedFiberRingEquiv_mk A B b

/-- EVERY actual upper T coefficient retains the original forward coefficient image. -/
theorem upperClosedFiberEquiv_coefficient (t : T) :
    upperClosedFiberEquiv A B (algebraMap T (ClosedFiber T B) t) =
      Ideal.Quotient.mk (closedFiberIdeal A B) (coefficientMap A B t) :=
  upperClosedFiberEquiv_mk A B _

/-- EVERY original base coefficient retains precisely its original target quotient image. -/
theorem upperResidueMap_originalBase (a : A) :
    upperResidueMap A B (residue T (algebraMap A T a)) =
      Ideal.Quotient.mk (closedFiberIdeal A B) (algebraMap A B a) := by
  rw [upperResidueMap_residue]
  congr 1
  exact (coefficientMap A B).commutes a

omit [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  [IsAdicComplete (maximalIdeal B) B] in
/-- The original native target residue map factors through precisely the original lower closed fibre. -/
def originalResidueProjection : F →+* ResidueField B :=
  Ideal.Quotient.lift (closedFiberIdeal A B) (residue B) (by
    intro b hb
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((map_maximalIdeal_le (algebraMap A B)) hb))

omit [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  [IsAdicComplete (maximalIdeal B) B] in
/-- EVERY original target representative has its SAME native residue. -/
theorem originalResidueProjection_mk (b : B) :
    originalResidueProjection A B (Ideal.Quotient.mk (closedFiberIdeal A B) b) = residue B b := rfl

/-- The WHOLE actual upper residue action induces the native residue map of the SAME original Hensel lift. -/
theorem originalResidueProjection_upperResidue :
    (originalResidueProjection A B).comp (upperResidueMap A B) =
      (coefficientResidueEquiv A B).toRingHom := by
  ext a
  obtain ⟨t, rfl⟩ := residue_surjective a
  change residue B (coefficientMap A B t) =
    ResidueField.map (coefficientMap A B).toRingHom (residue T t)
  exact (ResidueField.map_residue _ _).symm

end Hironaka.Algebra.NodeEtaleClosedFiber
